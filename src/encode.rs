use crate::common::abencode;
use crate::common::Symbol;

use arrayvec::ArrayVec;
use std::collections::BTreeMap;
use std::collections::VecDeque;
use std::convert::TryFrom;
use std::convert::TryInto;

#[derive(Default)]
pub struct Encoder {
    stream_header_emitted: bool,
    emission_buffer: VecDeque<bool>,
    block_buffer: Vec<u8>,
    alignment_ticker: u8,
    block_crc: Option<crc::crc32::Digest>,
    stream_crc: u32,
}

impl Encoder {
    pub fn push_byte(&mut self, byte: u8) -> Result<Vec<u8>, &'static str> {
        if !self.stream_header_emitted {
            self.emit_stream_header();
        }
        if self.block_crc.is_none() {
            self.block_crc = Some(crc::crc32::Digest::new(crc::crc32::IEEE));
        }
        crc::Hasher32::write(self.block_crc.as_mut().unwrap(), &[byte.reverse_bits()][..]);
        self.block_buffer.push(byte);
        if self.block_buffer.len() == 900_000_000 {
            self.emit_block();
        }
        Ok(self.drain_available_bytes())
    }

    pub fn finish(&mut self) -> Result<Vec<u8>, &'static str> {
        if !self.stream_header_emitted {
            self.emit_stream_header();
        }
        if !self.block_buffer.is_empty() {
            self.emit_block();
        }
        self.emit_stream_footer();
        Ok(self.drain_available_bytes())
    }

    fn emit_block(&mut self) {
        log::trace!("Emitting block");
        let crc = crc::Hasher32::sum32(self.block_crc.as_ref().unwrap()).reverse_bits();
        self.stream_crc = crc ^ ((self.stream_crc << 1) | (self.stream_crc >> 31));
        let crc = crc.to_be_bytes();
        self.block_crc.take();
        self.emit_bytes(crate::common::BLOCK_MAGIC);
        log::trace!("block crc: {:?}", crc);
        self.emit_bytes(&crc[..]);
        self.emit_bit(false); // "Randomized" flag
        let rle1 = rle_encode(&self.block_buffer);
        self.block_buffer.clear();
        let (mut bwt_data, origin_ptr) = bwt_encode(&rle1);
        log::trace!("Encode origin_ptr: {:?}", origin_ptr);
        log::trace!("Encode bwt_data: {:?}", bwt_data);
        let origin_ptr: u32 = u32::try_from(origin_ptr).unwrap();
        self.emit_bytes(&origin_ptr.to_be_bytes()[1..]); // OrigPtr
        let mtf_stack: std::collections::BTreeSet<u8> =
            mtf_encode(&mut bwt_data).into_iter().collect();
        let mtf_stack2: Vec<u8> = mtf_stack.iter().cloned().collect();
        let mut rle2 = rle2_encode(&bwt_data);
        rle2.push(Symbol::Eob);

        // The decoder assumes that a tree will be NumSyms + 2 entries long. We have to make sure it IS that long, even though it often doesn't have any reason to be that long.
        rle2.push(Symbol::RunA);
        rle2.push(Symbol::RunB);
        for i in 1..=mtf_stack.len() {
            rle2.push(Symbol::Idx(i.try_into().unwrap()));
        }
        log::trace!("rl2: {:?}", rle2);
        let tree = huff_encode(&rle2);

        // Remove the stray RunA, RunB, and Idx()es we added to pad out the tree size.
        rle2.pop();
        rle2.pop();
        for _ in 0..mtf_stack.len() {
            rle2.pop();
        }
        log::trace!("Tree: {:?}", tree);
        let depth_map = huff_node_to_depth_map(&tree, 0, &mtf_stack2).unwrap();
        assert!(depth_map.len() == mtf_stack.len() + 2);
        log::trace!("Depth map: {:?}", depth_map);
        let code_map = crate::common::depth_map_to_code_map(&depth_map);

        let mut pages_bitset = 0u16;
        let mut page_vec = Vec::new();
        for page_number in 0..16 {
            pages_bitset <<= 1;
            let mut page_bitset = 0u16;
            for offset in 0..16 {
                page_bitset <<= 1;
                let val = page_number * 16 + offset;
                if mtf_stack.contains(&(val)) {
                    pages_bitset |= 1;
                    page_bitset |= 1;
                }
            }
            if page_bitset != 0 {
                page_vec.extend(&page_bitset.to_be_bytes());
            }
        }
        self.emit_bytes(&pages_bitset.to_be_bytes()[..]);
        self.emit_bytes(&page_vec[..]);

        // Emit NumTrees as 0b010.
        self.emit_bit(false);
        self.emit_bit(true);
        self.emit_bit(false);

        let num_symbols: u16 = u16::try_from(bwt_data.len())
            .unwrap()
            .checked_add(1)
            .unwrap();
        let mut num_sels: u16 = (num_symbols / 50)
            .checked_add(if num_symbols % 50 != 0 { 1 } else { 0 })
            .unwrap();
        let num_sels2 = num_sels;
        log::trace!("Specifying num_sels as {}", num_sels);
        for _ in 0..15 {
            num_sels <<= 1;
            let bit = num_sels & 0b1000_0000_0000_0000 != 0;
            log::trace!("Emitting num_sels bit: {}", bit);
            self.emit_bit(bit);
        }
        for _ in 0..num_sels2 {
            self.emit_bit(false);
        }

        for _ in 0..2 {
            let mut clen: u8 = *depth_map.iter().next().unwrap().1;
            log::trace!("Emitting initial clen: {}", clen);
            let mut clen2 = clen;
            for _ in 0..5 {
                self.emit_bit(clen2 & 0b1_0000 != 0);
                clen2 <<= 1;
            }
            for (_k, v) in &depth_map {
                log::trace!("Emitting depth {}", v);
                while clen < *v {
                    self.emit_bit(true);
                    self.emit_bit(false);
                    clen = clen.checked_add(1).unwrap();
                }
                while clen > *v {
                    self.emit_bit(true);
                    self.emit_bit(true);
                    clen = clen.checked_sub(1).unwrap();
                }
                self.emit_bit(false);
            }
        }

        for symbol in rle2 {
            let code = code_map.get(&symbol.to_u16(&mtf_stack2).unwrap()).unwrap();
            for bit in code {
                self.emit_bit(*bit);
            }
        }
    }

    fn emit_stream_header(&mut self) {
        self.stream_header_emitted = true;
        self.emit_bytes(b"BZh9");
    }

    fn emit_stream_footer(&mut self) {
        self.emit_bytes(crate::common::STREAM_FOOTER_MAGIC);
        let crc = self.stream_crc;
        self.emit_bytes(&crc.to_be_bytes()[..]);
        while self.alignment_ticker != 0 {
            self.emit_bit(false);
        }
    }

    fn emit_bytes(&mut self, bytes: &[u8]) {
        for i in bytes {
            self.emit_byte(*i);
        }
    }

    fn emit_byte(&mut self, byte: u8) {
        for i in 0..8 {
            self.emit_bit((byte << i) & 0b1000_0000 != 0);
        }
    }

    fn emit_bit(&mut self, bit: bool) {
        self.emission_buffer.push_back(bit);
        self.alignment_ticker = (self.alignment_ticker + 1) % 8;
    }

    fn drain_byte(&mut self) -> u8 {
        let mut result = 0u8;
        for _ in 0..8 {
            result <<= 1;
            if self.emission_buffer.pop_front().unwrap() {
                result |= 1;
            }
        }
        result
    }

    fn drain_available_bytes(&mut self) -> Vec<u8> {
        let mut result = Vec::new();
        while self.emission_buffer.len() >= 8 {
            result.push(self.drain_byte());
        }
        result
    }
}

#[derive(Default)]
pub struct RleEncoderState {
    prev_symbol: Option<u8>,
    run_length: u8,
    finished: bool,
}

impl RleEncoderState {
    pub fn push_symbol(&mut self, symbol: u8) -> ArrayVec<[u8; 2]> {
        assert!(!self.finished);
        let mut result = ArrayVec::default();
        match self.prev_symbol {
            None => {
                self.prev_symbol = Some(symbol);
                self.run_length = 1;
                result.push(symbol);
            }
            Some(x) if symbol == x => {
                if self.run_length < 254 {
                    self.run_length = self.run_length.checked_add(1).unwrap();
                    if self.run_length <= 4 {
                        result.push(symbol);
                    }
                } else {
                    result.push(self.run_length.checked_sub(3).unwrap());
                    self.run_length = 0;
                }
            }
            Some(_) => {
                if self.run_length >= 4 {
                    result.push(self.run_length.checked_sub(4).unwrap());
                }
                self.run_length = 1;
                self.prev_symbol = Some(symbol);
                result.push(symbol);
            }
        }
        result
    }

    pub fn finish(&mut self) -> ArrayVec<[u8; 1]> {
        assert!(!self.finished);
        self.finished = true;
        let mut result = ArrayVec::default();
        if self.run_length >= 4 {
            result.push(self.run_length.checked_sub(4).unwrap());
        }
        result
    }
}

pub fn rle_encode(input: &[u8]) -> Vec<u8> {
    let mut result = Vec::new();
    let mut state = RleEncoderState::default();
    for i in input {
        result.extend(state.push_symbol(*i));
    }
    result.extend(state.finish());
    result
}

pub fn bwt_encode(block: &[u8]) -> (Vec<u8>, usize) {
    let mut rotations: Vec<(&[u8], &[u8])> = (0..(block.len()))
        .map(|x| (&block[x..], &block[..x]))
        .collect();
    rotations.sort_by(|a, b| {
        let total_len = a.0.len() + a.1.len();
        for i in 0..total_len {
            let left = if i < a.0.len() {
                a.0[i]
            } else {
                a.1[i - a.0.len()]
            };
            let right = if i < b.0.len() {
                b.0[i]
            } else {
                b.1[i - b.0.len()]
            };
            match left.partial_cmp(&right).unwrap() {
                std::cmp::Ordering::Equal => (),
                x => {
                    return x;
                }
            }
        }
        std::cmp::Ordering::Equal
    });
    log::trace!("bwt matrix: {:?}", rotations);
    let final_column = rotations
        .iter()
        .map(|(a, b)| {
            if b.len() != 0 {
                b[b.len() - 1]
            } else {
                a[a.len() - 1]
            }
        })
        .collect();
    let idx = rotations
        .iter()
        .enumerate()
        .find_map(|(k, v)| {
            if v.0 == &block[..v.0.len()] && v.1 == &block[v.0.len()..] {
                Some(k)
            } else {
                None
            }
        })
        .unwrap();
    (final_column, idx)
}

pub fn mtf_encode(data: &mut [u8]) -> Vec<u8> {
    let mut stack: Vec<u8> = data
        .iter()
        .copied()
        .collect::<std::collections::BTreeSet<u8>>()
        .into_iter()
        .collect();
    for v in data {
        log::trace!("v: {}, stack: {:?}", v, stack);
        let idx: u8 = stack
            .iter()
            .position(|x| x == v)
            .expect("failed to find symbol in stack")
            .try_into()
            .expect("idx too large");
        let symbol = *v;
        *v = idx;
        stack.remove(idx.into());
        stack.insert(0, symbol);
    }
    stack
}

pub fn rle2_encode(data: &[u8]) -> Vec<Symbol> {
    let mut output = Vec::new();
    let mut zero_count = 0;
    for &i in data {
        if zero_count == 0 && i != 0 {
            output.push(Symbol::Idx(i.into()));
        } else if zero_count > 0 && i != 0 {
            output.extend(abencode(zero_count));
            output.push(Symbol::Idx(i.into()));
            zero_count = 0;
        } else {
            debug_assert!(i == 0);
            zero_count += 1;
        }
    }
    if zero_count > 0 {
        output.extend(abencode(zero_count));
    }
    output
}

#[derive(Debug, Clone, PartialOrd, PartialEq, Eq, Ord)]
pub enum HuffmanNode {
    Leaf {
        symbol: Symbol,
        weight: usize,
    },
    Node {
        weight: usize,
        left: Box<HuffmanNode>,
        right: Box<HuffmanNode>,
    },
}

impl HuffmanNode {
    fn weight(&self) -> usize {
        match self {
            HuffmanNode::Leaf { weight, .. } => *weight,
            HuffmanNode::Node { weight, .. } => *weight,
        }
    }

    fn symbol(&self) -> Result<Symbol, &'static str> {
        match self {
            HuffmanNode::Leaf { symbol, .. } => Ok(*symbol),
            HuffmanNode::Node { .. } => Err("HuffmanNode::symbol used on an internal node"),
        }
    }

    fn left(&self) -> Result<&HuffmanNode, &'static str> {
        match self {
            HuffmanNode::Node { left, .. } => Ok(&*left),
            HuffmanNode::Leaf { .. } => Err("HuffmanNode::left used on a leaf node"),
        }
    }

    fn right(&self) -> Result<&HuffmanNode, &'static str> {
        match self {
            HuffmanNode::Node { right, .. } => Ok(&*right),
            HuffmanNode::Leaf { .. } => Err("HuffmanNode::right used on a leaf node"),
        }
    }

    fn is_leaf(&self) -> bool {
        match self {
            HuffmanNode::Leaf { .. } => true,
            _ => false,
        }
    }
}

fn find_low_node(nodes: &[HuffmanNode]) -> usize {
    let low_weight = nodes.iter().map(|x| x.weight()).min().unwrap();
    let lowest_at_weight = nodes
        .iter()
        .enumerate()
        .filter(|(_k, v)| v.weight() == low_weight)
        .map(|(k, v)| (v, k))
        .max()
        .unwrap()
        .1;
    lowest_at_weight
}

pub fn huff_encode(symbols: &[Symbol]) -> HuffmanNode {
    let mut weights = std::collections::BTreeMap::<Symbol, usize>::new();
    for symbol in symbols {
        *weights.entry(*symbol).or_default() += 1;
    }
    let mut nodes: Vec<_> = weights
        .into_iter()
        .map(|x| HuffmanNode::Leaf {
            symbol: x.0,
            weight: x.1,
        })
        .collect();
    nodes.sort_by_key(|x| x.weight());
    while nodes.len() > 1 {
        let low_node = nodes.remove(find_low_node(&nodes));
        let low2_node = nodes.remove(find_low_node(&nodes));
        let new_weight = low_node.weight() + low2_node.weight();
        let new_node = HuffmanNode::Node {
            weight: new_weight,
            left: Box::new(low2_node),
            right: Box::new(low_node),
        };
        nodes.push(new_node);
        nodes.sort_by_key(|x| x.weight());
    }
    nodes.remove(0)
}

fn huff_node_to_depth_map(
    node: &HuffmanNode,
    current_depth: u8,
    syms: &[u8],
) -> Result<BTreeMap<u16, u8>, &'static str> {
    let mut result = BTreeMap::new();
    if node.is_leaf() {
        let repr = node.symbol()?.to_u16(syms)?;
        log::trace!("Representing {:?} as {}", node.symbol(), repr);
        result.insert(repr, current_depth);
        Ok(result)
    } else {
        let next_depth = current_depth
            .checked_add(1)
            .ok_or("BUG: Huffman tree is >255 deep")?;
        result.extend(huff_node_to_depth_map(node.left()?, next_depth, syms)?);
        result.extend(huff_node_to_depth_map(node.right()?, next_depth, syms)?);
        Ok(result)
    }
}

pub fn encode(data: &[u8]) -> Result<Vec<u8>, &'static str> {
    let mut result = Vec::new();
    let mut encoder = crate::encode::Encoder::default();
    for i in data {
        result.extend(encoder.push_byte(*i)?);
    }
    result.extend(encoder.finish()?);
    Ok(result)
}
