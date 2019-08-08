// Based on reverse engineering performed by Joe Tsai from https://github.com/dsnet/compress/blob/master/doc/bzip2-format.pdf (https://digital-static.net)

use arrayvec::ArrayVec;
use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::convert::TryInto;

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

#[cfg(test)]
#[test]
fn rle_test() {
    assert_eq!(&rle_encode(b"AAAAAAABBBBCCCD")[..], b"AAAA\x03BBBB\x00CCCD");
    assert_eq!(&rle_encode(b"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA")[..], b"AAAA\xfbA");
    assert_eq!(&rle_encode(b"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA")[..], b"AAAA\xfbAAAA\x00");
    assert_eq!(&rle_encode(b"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA")[..], b"AAAA\xfbAAAA\x29");
}

pub fn bwt_encode(block: &[u8]) -> (Vec<u8>, usize) {
    let mut rotations: Vec<(&[u8], &[u8])> = (0..(block.len()))
        .map(|x| (&block[x..], &block[..x]))
        .collect();
    rotations.sort();
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

#[cfg(test)]
#[test]
fn bwt_test() {
    assert_eq!(bwt_encode(&b"banana"[..]), (b"nnbaaa".to_vec(), 3));
}

pub fn mtf_encode(data: &mut [u8]) -> Vec<u8> {
    let mut stack: Vec<u8> = data
        .iter()
        .copied()
        .collect::<std::collections::BTreeSet<u8>>()
        .into_iter()
        .collect();
    for v in data {
        println!("v: {}, stack: {:?}", v, stack);
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

#[cfg(test)]
#[test]
fn mtf_test() {
    let mut data = b"bbyaeeeeeeafeeeybzzzzzzzzzyz".to_vec();
    let _stack = mtf_encode(&mut data);
    assert_eq!(
        &data[..],
        [1, 0, 4, 2, 3, 0, 0, 0, 0, 0, 1, 4, 2, 0, 0, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1]
    );
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq)]
pub enum Symbol {
    RunA,
    RunB,
    Idx(u8),
}

pub fn abencode(mut zerocnt: u32) -> Vec<Symbol> {
    zerocnt += 1;
    let len = 32 - zerocnt.leading_zeros() - 1;
    let mut result = Vec::new();
    for i in 0..len {
        if zerocnt & (1 << i) > 0 {
            result.push(Symbol::RunB)
        } else {
            result.push(Symbol::RunA)
        }
    }
    result
}

pub fn abdecode(symbols: &[Symbol]) -> u32 {
    let mut result = 0u32;
    for &i in symbols.iter().rev() {
        assert!(i == Symbol::RunA || i == Symbol::RunB);
        result <<= 1;
        if i == Symbol::RunB {
            result |= 1;
        }
    }
    result |= 1 << symbols.len();
    result -= 1;
    result
}

#[cfg(test)]
#[test]
fn abencode_test() {
    assert_eq!(abencode(1), vec![Symbol::RunA]);
    assert_eq!(abencode(2), vec![Symbol::RunB]);
    assert_eq!(abencode(3), vec![Symbol::RunA, Symbol::RunA]);
    assert_eq!(abencode(4), vec![Symbol::RunB, Symbol::RunA]);
    assert_eq!(abencode(5), vec![Symbol::RunA, Symbol::RunB]);
    assert_eq!(abencode(6), vec![Symbol::RunB, Symbol::RunB]);
    assert_eq!(abencode(7), vec![Symbol::RunA, Symbol::RunA, Symbol::RunA]);
    assert_eq!(abencode(8), vec![Symbol::RunB, Symbol::RunA, Symbol::RunA]);
    assert_eq!(abencode(9), vec![Symbol::RunA, Symbol::RunB, Symbol::RunA]);
    assert_eq!(abencode(10), vec![Symbol::RunB, Symbol::RunB, Symbol::RunA]);
    assert_eq!(abencode(11), vec![Symbol::RunA, Symbol::RunA, Symbol::RunB]);
    assert_eq!(abencode(12), vec![Symbol::RunB, Symbol::RunA, Symbol::RunB]);
    assert_eq!(abencode(13), vec![Symbol::RunA, Symbol::RunB, Symbol::RunB]);
    assert_eq!(abencode(14), vec![Symbol::RunB, Symbol::RunB, Symbol::RunB]);
    assert_eq!(
        abencode(15),
        vec![Symbol::RunA, Symbol::RunA, Symbol::RunA, Symbol::RunA]
    );
    assert_eq!(
        abencode(16),
        vec![Symbol::RunB, Symbol::RunA, Symbol::RunA, Symbol::RunA]
    );
    assert_eq!(
        abencode(17),
        vec![Symbol::RunA, Symbol::RunB, Symbol::RunA, Symbol::RunA]
    );
    assert_eq!(
        abencode(18),
        vec![Symbol::RunB, Symbol::RunB, Symbol::RunA, Symbol::RunA]
    );
    assert_eq!(abencode(30).len(), 4);
    assert_eq!(abencode(31).len(), 5);
    assert_eq!(abencode(62).len(), 5);
    assert_eq!(abencode(63).len(), 6);
    for i in 0..=64 {
        let encoded = abencode(i);
        let decoded = abdecode(&encoded[..]);
        assert_eq!(decoded, i);
    }
}

pub fn rle2_encode(data: &[u8]) -> Vec<Symbol> {
    let mut output = Vec::new();
    let mut zero_count = 0;
    for &i in data {
        if zero_count == 0 && i != 0 {
            output.push(Symbol::Idx(i));
        } else if zero_count > 0 && i != 0 {
            output.extend(abencode(zero_count));
            output.push(Symbol::Idx(i));
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

    fn symbol(&self) -> Symbol {
        match self {
            HuffmanNode::Leaf { symbol, .. } => *symbol,
            HuffmanNode::Node { .. } => panic!(),
        }
    }

    fn left(&self) -> &HuffmanNode {
        match self {
            HuffmanNode::Node { left, .. } => &*left,
            _ => panic!(),
        }
    }

    fn right(&self) -> &HuffmanNode {
        match self {
            HuffmanNode::Node { right, .. } => &*right,
            _ => panic!(),
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

pub fn huff_to_bits(
    tree: &HuffmanNode,
    prev: Vec<bool>,
) -> std::collections::BTreeMap<Symbol, Vec<bool>> {
    let mut result = std::collections::BTreeMap::default();
    if tree.is_leaf() {
        result.insert(tree.symbol(), prev);
    } else {
        let mut lprev = prev.clone();
        lprev.push(false);
        result.extend(huff_to_bits(tree.left(), lprev));
        let mut rprev = prev.clone();
        rprev.push(true);
        result.extend(huff_to_bits(tree.right(), rprev));
    }
    result
}

#[allow(dead_code)]
fn decode_bwt_slow(bwt: &[u8], ptr: usize) -> Vec<u8> {
    log::trace!("PTR: {}", ptr);
    let mut matrix = Vec::new();
    for _ in bwt {
        let mut row = Vec::new();
        row.resize(bwt.len(), 0);
        matrix.push(row);
    }
    for ci in (0..bwt.len()).rev() {
        log::trace!("decode_bwt_slow ci: {}", ci);
        for (ri, &b) in bwt.iter().enumerate() {
            matrix[ri][ci] = b;
        }
        matrix.sort();
    }
    log::trace!("Input: {:x?}", String::from_utf8(bwt.to_vec()));
    for (idx, row) in matrix.iter().enumerate() {
        log::trace!("Row {}: {:x?}", idx, String::from_utf8(row.clone()));
    }
    return matrix[usize::try_from(ptr).unwrap()].clone();
}

fn decode_bwt(bwt: &[u8], ptr: usize) -> Vec<u8> {
    let mut cumm = Vec::new();
    let mut n = 0;
    cumm.resize(256, 0);
    for &i in bwt {
        cumm[usize::from(i)] += 1;
    }
    for idx in 0..cumm.len() {
        let v = cumm[idx];
        cumm[idx] = n;
        n += v;
    }

    let mut perm = Vec::new();
    perm.resize(bwt.len(), 0);
    for (k, &v) in bwt.iter().enumerate() {
        perm[cumm[usize::from(v)]] = k;
        cumm[usize::from(v)] += 1;
    }

    let mut i = perm[ptr];
    let mut data = Vec::new();
    data.resize(bwt.len(), 0);
    for j in 0..bwt.len() {
        data[j] = bwt[i];
        i = perm[i];
    }
    data
}

enum DecoderState {
    StreamStart { idx: usize },
    BlockStart { idx: usize },
    BlockTrees { state: BlockTreesState },
    BlockData,
    StreamFooter { idx: usize },
    Error,
}

enum BlockTreesState {
    SymMapL1,
    SymMapL2 { page_count: u16 },
    NumTrees,
    NumSels,
    Selectors,
    Trees,
}

impl Default for DecoderState {
    fn default() -> Self {
        DecoderState::StreamStart { idx: 0 }
    }
}

#[derive(Default)]
pub struct Decoder {
    state: DecoderState,
    level: Option<u8>,
    crc32: ArrayVec<[u8; 4]>,
    orig_ptr: u32,
    stack: Vec<u8>,
    accumulator: Vec<bool>,
    misalignment: u8,
    num_trees: u8,
    num_sels: u16,
    selectors: Vec<u8>,
    trees: Vec<BTreeMap<u16, Vec<bool>>>,
    block_symbols: Vec<u16>,
    block_symbols2: Vec<u8>,
}

fn code_to_bits(mut code: usize, bits: u8) -> Vec<bool> {
    let mut result = Vec::new();
    for _ in 0..bits {
        result.push(code & 1 != 0);
        code >>= 1;
    }
    result.into_iter().rev().collect()
}

fn tree_to_map(tree: &BTreeMap<u16, u8>) -> BTreeMap<u16, Vec<bool>> {
    let mut result = BTreeMap::new();
    let mut data: Vec<(u8, u16)> = tree.iter().map(|(k, v)| (*v, *k)).collect();
    data.sort();
    let mut code = 0;
    for i in 0..data.len() {
        result.insert(data[i].1, code_to_bits(code, data[i].0));
        let next_bit_len = data
            .iter()
            .skip(i + 1)
            .next()
            .map(|x| x.0)
            .unwrap_or(data[i].0);
        code = (code + 1) << (next_bit_len - data[i].0)
    }
    result
}

const NEED_BITS: &'static str = "not enough bytes";

impl Decoder {
    pub fn push_byte(&mut self, byte: u8) -> Result<Vec<u8>, &'static str> {
        self.stash_bits(byte, 8);
        let mut final_result = Vec::new();
        loop {
            let pre_len = self.accumulator.len();
            let result = self.consume();
            let post_len = self.accumulator.len();
            self.misalignment += u8::try_from((pre_len - post_len) % 8).unwrap();
            self.misalignment = self.misalignment % 8;
            match result {
                Ok(Some(data)) => {
                    final_result.extend(data);
                }
                Ok(None) => (),
                Err(NEED_BITS) => {
                    break;
                }
                Err(err) => {
                    self.state = DecoderState::Error;
                    return Err(err);
                }
            }
        }
        Ok(final_result)
    }

    fn consume(&mut self) -> Result<Option<Vec<u8>>, &'static str> {
        match self.state {
            DecoderState::StreamStart { ref mut idx } => match idx {
                0 => {
                    if consume_bytes(&mut self.accumulator, 2)? != b"BZ" {
                        Err("bad magic")
                    } else {
                        *idx += 2;
                        Ok(None)
                    }
                }
                2 => {
                    if consume_byte(&mut self.accumulator)? != b'h' {
                        Err("bad version")
                    } else {
                        *idx += 1;
                        Ok(None)
                    }
                }
                3 => {
                    let byte = consume_byte(&mut self.accumulator)?;
                    if !b"123456789".iter().any(|x| *x == byte) {
                        Err("bad level")
                    } else {
                        let level = byte.checked_sub(b'0').unwrap();
                        debug_assert!(level >= 1);
                        debug_assert!(level <= 9);
                        self.level = Some(level);
                        self.state = DecoderState::BlockStart { idx: 0 };
                        Ok(None)
                    }
                }
                _ => Err("internal error"),
            },
            DecoderState::BlockStart { ref mut idx } => match idx {
                0 => {
                    let magic = consume_bytes(&mut self.accumulator, 6)?;
                    log::trace!("Magic: {:x?}", magic);
                    if magic == b"\x17\x72\x45\x38\x50\x90" {
                        log::trace!("Saw streamfooter");
                        self.state = DecoderState::StreamFooter { idx: 6 };
                        Ok(None)
                    } else if magic == b"\x31\x41\x59\x26\x53\x59" {
                        *idx = 6;
                        Ok(None)
                    } else {
                        Err("bad block magic")
                    }
                }
                6 => {
                    let crc = consume_bytes(&mut self.accumulator, 4)?;
                    log::trace!("block crc: {:x?}", crc);
                    self.crc32.extend(crc);
                    *idx = 10;
                    Ok(None)
                }
                10 => {
                    let randomized = consume_bit(&mut self.accumulator)?;
                    if randomized {
                        Err("randomized byte set")
                    } else {
                        *idx = 11;
                        Ok(None)
                    }
                }
                11 => {
                    let orig_ptr = consume_bytes(&mut self.accumulator, 3)?;
                    let mut orig_ptr2 = [0u8; 4];
                    orig_ptr2[1..=3].copy_from_slice(&orig_ptr);
                    self.orig_ptr = u32::from_be_bytes(orig_ptr2);
                    log::trace!("orig_ptr: {}", self.orig_ptr);
                    self.state = DecoderState::BlockTrees {
                        state: BlockTreesState::SymMapL1,
                    };
                    Ok(None)
                }
                _ => Err("internal error"),
            },
            DecoderState::BlockTrees { ref mut state } => match state {
                BlockTreesState::SymMapL1 => {
                    let page_count = consume_u16(&mut self.accumulator)?;
                    log::trace!("SymMapL1: {:b}", page_count);
                    *state = BlockTreesState::SymMapL2 { page_count };
                    Ok(None)
                }
                BlockTreesState::SymMapL2 { page_count } => {
                    let bytes = consume_bytes(
                        &mut self.accumulator,
                        (u16::try_from(page_count.count_ones()).unwrap() * 2).into(),
                    )?;
                    let mut skip_count = 0;
                    for page in 0u8..16 {
                        if *page_count & (0b1000_0000_0000_0000 >> page) != 0 {
                            log::trace!("Doing page {}", page);
                            for bit in 0..16 {
                                let pt2 = if bit >= 8 { 1 } else { 0 };
                                let byte_number = usize::from((page - skip_count) * 2 + pt2);
                                log::trace!("byte number: {:?}", byte_number);
                                let byte: u8 = bytes[byte_number];
                                let included = (0b1000_0000 >> (bit % 8)) & byte != 0;
                                if included {
                                    let idx = (page * 16 + bit).try_into().unwrap();
                                    self.stack.push(idx);
                                }
                            }
                        } else {
                            skip_count += 1;
                            log::trace!("Skipping page {}", page);
                        }
                    }
                    *state = BlockTreesState::NumTrees;
                    Ok(None)
                }
                BlockTreesState::NumTrees => {
                    let num_trees_bits = consume_bits(&mut self.accumulator, 3)?;
                    let mut num_trees = 0;
                    for i in num_trees_bits {
                        num_trees <<= 1;
                        if i {
                            num_trees |= 1;
                        }
                    }
                    log::trace!("num_trees: {}", num_trees);
                    self.num_trees = num_trees;
                    *state = BlockTreesState::NumSels;
                    Ok(None)
                }
                BlockTreesState::NumSels => {
                    let num_sels_bits = consume_bits(&mut self.accumulator, 15)?;
                    let mut num_sels = 0u16;
                    for i in num_sels_bits {
                        num_sels <<= 1;
                        if i {
                            num_sels |= 1;
                        }
                    }
                    self.num_sels = num_sels;
                    log::trace!("num_sels: {}", num_sels);
                    *state = BlockTreesState::Selectors;
                    Ok(None)
                }
                BlockTreesState::Selectors => {
                    if self.selectors.len() == self.num_sels.into() {
                        log::trace!("Selectors: {:?}", self.selectors);
                        *state = BlockTreesState::Trees;
                        Ok(None)
                    } else {
                        if !self.accumulator.iter().any(|x| *x == false) {
                            Err(NEED_BITS)
                        } else {
                            let mut selector_number = 0;
                            while consume_bit(&mut self.accumulator)? {
                                selector_number += 1
                            }
                            if selector_number > 5 {
                                Err("invalid selector")
                            } else {
                                self.selectors.push(selector_number);
                                Ok(None)
                            }
                        }
                    }
                }
                BlockTreesState::Trees => {
                    if self.trees.len() == self.num_trees.into() {
                        self.state = DecoderState::BlockData;
                        Ok(None)
                    } else if self.accumulator.len() < 5 {
                        Err(NEED_BITS)
                    } else {
                        let mut cursor = 5;
                        let clen_bits: Vec<bool> =
                            self.accumulator.iter().copied().take(5).collect();
                        let mut clen = 0u8;
                        for i in clen_bits {
                            clen <<= 1;
                            if i {
                                clen |= 1;
                            }
                        }
                        log::trace!("Initial clen: {}", clen);
                        let mut tree = BTreeMap::new();
                        for value in 0u16..u16::try_from(self.stack.len() + 2).unwrap() {
                            log::trace!("Considering value {:?}", value);
                            loop {
                                let bit = self.accumulator.iter().skip(cursor).next();
                                cursor += 1;
                                match bit {
                                    None => {
                                        return Err(NEED_BITS);
                                    }
                                    Some(true) => {
                                        let other_bit =
                                            self.accumulator.iter().skip(cursor).copied().next();
                                        cursor += 1;
                                        if other_bit.is_none() {
                                            return Err(NEED_BITS);
                                        }
                                        if other_bit == Some(true) && clen == 0 {
                                            return Err("tried to decrement clen while at 0");
                                        } else if other_bit == Some(true) {
                                            clen -= 1;
                                            log::trace!("Decrementing clen to {}", clen);
                                        } else if other_bit == Some(false) && clen == 20 {
                                            return Err("tried to increment clen above 20");
                                        } else {
                                            clen += 1;
                                            log::trace!("Incrementing clen to {}", clen);
                                        }
                                    }
                                    Some(false) => {
                                        tree.insert(value, clen);
                                        break;
                                    }
                                }
                            }
                        }
                        log::trace!("tree: {:?}", tree);
                        let tree = tree_to_map(&tree);
                        log::trace!("tree map: {:?}", tree);
                        self.trees.push(tree);
                        self.accumulator.drain(..cursor);
                        Ok(None)
                    }
                }
            },
            DecoderState::BlockData => {
                let mut bits = Vec::new();
                let mut cursor = 0;
                loop {
                    let next_bit = self.accumulator.iter().skip(cursor).next();
                    cursor += 1;
                    if next_bit.is_none() {
                        return Err(NEED_BITS);
                    }
                    bits.push(*next_bit.unwrap());
                    assert!(bits.len() <= 20);
                    let tree_number: usize = self.selectors[self.block_symbols.len() / 50].into();
                    if let Some((symbol, _)) = self.trees[tree_number]
                        .iter()
                        .filter(|(_k, v)| v == &&bits)
                        .next()
                    {
                        log::trace!(
                            "Saw symbol: {} (idx: {}, tree: {})",
                            symbol,
                            self.block_symbols.len(),
                            tree_number
                        );
                        if *symbol == u16::try_from(self.stack.len() + 1).unwrap() {
                            self.state = DecoderState::BlockStart { idx: 0 };
                            self.accumulator.drain(..cursor);
                            return Ok(Some(self.decode_block()));
                        }
                        self.block_symbols.push(*symbol);
                        self.accumulator.drain(..cursor);
                        return Ok(None);
                    }
                }
            }
            DecoderState::StreamFooter { ref mut idx } => match idx {
                6 => {
                    let _crc = consume_bytes(&mut self.accumulator, 4)?;
                    *idx = 10;
                    Ok(None)
                }
                10 => {
                    let mut padding_size = 8 - self.misalignment;
                    if padding_size == 8 {
                        padding_size = 0;
                    }
                    assert!(padding_size < 8);
                    consume_bits(&mut self.accumulator, padding_size.into())?;
                    self.state = DecoderState::StreamStart { idx: 0 };
                    Ok(None)
                }
                _ => Err("internal error"),
            },
            DecoderState::Error => {
                log::warn!("Pushing byte into errored decoder");
                Err("already errored")
            }
        }
    }

    fn stash_bits(&mut self, mut byte: u8, how_many: u8) {
        assert!(how_many <= 8);
        byte = byte << (8 - how_many);
        for _ in 0..how_many {
            self.accumulator.push(byte & 0b1000_0000 != 0);
            byte = byte << 1;
        }
    }

    fn decode_block(&mut self) -> Vec<u8> {
        self.un_rle2();
        self.un_mtf();
        self.un_bwt();
        self.un_rle1();
        let mut tmp = Vec::new();
        std::mem::swap(&mut self.block_symbols2, &mut tmp);
        self.trees.clear();
        self.selectors.clear();
        tmp
    }

    fn un_rle1(&mut self) {
        let mut result = Vec::new();
        let mut last = None;
        let mut count = 0;
        for &i in &self.block_symbols2 {
            if count == 4 {
                for _ in 0..i {
                    result.push(last.unwrap());
                }
                count = 0;
                last = None;
            } else {
                if Some(i) == last {
                    count += 1;
                    result.push(i);
                } else {
                    count = 1;
                    result.push(i);
                    last = Some(i);
                }
            }
        }
        std::mem::replace(&mut self.block_symbols2, result);
    }

    fn un_bwt(&mut self) {
        let ptr: usize = self.orig_ptr.try_into().unwrap();
        let result = decode_bwt(&self.block_symbols2, ptr);
        std::mem::replace(&mut self.block_symbols2, result);
    }

    fn un_mtf(&mut self) {
        let mut new_block = Vec::new();
        for &i in &self.block_symbols {
            let symbol = self.stack.remove(i.into());
            log::trace!("Emitting a {:x?}", symbol);
            new_block.push(symbol);
            self.stack.insert(0, symbol);
        }
        std::mem::replace(&mut self.block_symbols2, new_block);
    }

    fn un_rle2(&mut self) {
        if self.block_symbols.is_empty() {
            return;
        }
        log::trace!("Starting with {} symbols", self.block_symbols.len());
        let mut new_block = Vec::new();
        let mut ab_accumulator = Vec::new();
        for &i in &self.block_symbols {
            if i != 0 && i != 1 {
                if ab_accumulator.is_empty() {
                    log::trace!("Pushing a single {}", i - 1);
                    new_block.push(i - 1);
                } else {
                    let count = abdecode(&ab_accumulator);
                    log::trace!("Pushing {} zeros, then a {}", count, i - 1);
                    for _ in 0..count {
                        new_block.push(0);
                    }
                    ab_accumulator.clear();
                    new_block.push(i - 1);
                }
            } else {
                ab_accumulator.push(if i == 0 { Symbol::RunA } else { Symbol::RunB });
            }
        }
        for _ in 0..abdecode(&ab_accumulator) {
            log::trace!("Pushing a trailing zero");
            new_block.push(0);
        }
        log::trace!("new_block_len: {}", new_block.len());
        std::mem::replace(&mut self.block_symbols, new_block);
    }
}

fn consume_bit(bits: &mut Vec<bool>) -> Result<bool, &'static str> {
    if bits.is_empty() {
        return Err(NEED_BITS);
    }
    Ok(bits.remove(0))
}

fn consume_bits(bits: &mut Vec<bool>, count: usize) -> Result<Vec<bool>, &'static str> {
    if bits.len() < count {
        return Err(NEED_BITS);
    }
    Ok(bits.drain(..count).collect())
}

fn consume_byte(bits: &mut Vec<bool>) -> Result<u8, &'static str> {
    if bits.len() < 8 {
        return Err(NEED_BITS);
    }
    let mut result = 0u8;
    for i in bits.drain(..8) {
        result <<= 1;
        if i {
            result |= 1;
        }
    }
    Ok(result)
}

fn consume_bytes(bits: &mut Vec<bool>, count: usize) -> Result<Vec<u8>, &'static str> {
    if bits.len() < count * 8 {
        return Err(NEED_BITS);
    }
    let mut result = Vec::new();
    for _ in 0..count {
        result.push(consume_byte(bits).unwrap());
    }
    Ok(result)
}

fn consume_u16(bits: &mut Vec<bool>) -> Result<u16, &'static str> {
    if bits.len() < 16 {
        return Err(NEED_BITS);
    }
    let mut stack = [0u8; 2];
    let bytes = consume_bytes(bits, 2).unwrap();
    stack.copy_from_slice(&bytes);
    Ok(u16::from_be_bytes(stack))
}

#[cfg(test)]
static LOGGER_INIT: std::sync::Once = std::sync::Once::new();

#[cfg(test)]
#[test]
fn format_decode_test() {
    LOGGER_INIT.call_once(env_logger::init);
    let data = b"\x42\x5a\x68\x31\x31\x41\x59\x26\x53\x59\x5a\x55\xc4\x1e\x00\x00\x0c\x5f\x80\x20\x00\x40\x84\x00\x00\x80\x20\x40\x00\x2f\x6c\xdc\x80\x20\x00\x48\x4a\x9a\x4c\xd5\x53\xfc\x69\xa5\x53\xff\x55\x3f\x69\x50\x15\x48\x95\x4f\xff\x55\x51\xff\xaa\xa0\xff\xf5\x55\x31\xff\xaa\xa7\xfb\x4b\x34\xc9\xb8\x38\xff\x16\x14\x56\x5a\xe2\x8b\x9d\x50\xb9\x00\x81\x1a\x91\xfa\x25\x4f\x08\x5f\x4b\x5f\x53\x92\x4b\x11\xc5\x22\x92\xd9\x50\x56\x6b\x6f\x9e\x17\x72\x45\x38\x50\x90\x5a\x55\xc4\x1e";
    let mut decoder = Decoder::default();
    let mut result = Vec::new();
    for byte in &data[..] {
        match decoder.push_byte(*byte) {
            Ok(data) => {
                result.extend(data);
            }
            _ => (),
        }
    }
    assert_eq!(&result[..], &b"If Peter Piper picked a peck of pickled peppers, where\'s the peck of pickled peppers Peter Piper picked?????"[..]);
}

#[cfg(test)]
#[test]
fn decode_bwt_test() {
    LOGGER_INIT.call_once(env_logger::init);
    let data = b"?fsrrdkkeaddrrffs,es???d\x01     eeiiiieeeehrppkllkppttpphppPPIootwppppPPcccccckk      iipp    eeeeeeeeer'ree  ";
    assert_eq!(&decode_bwt(data, 24)[..], &b"If Peter Piper picked a peck of pickled peppers, where\'s the peck of pickled peppers Peter Piper picked????\x01"[..]);
}
