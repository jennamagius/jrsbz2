use crate::common::*;

use arrayvec::ArrayVec;
use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::convert::TryInto;

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
    selectors_mtf: Vec<u8>,
    stream_crc: u32,
    ignore_crc: bool,
}

const NEED_BITS: &'static str = "not enough bytes";

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
    log::trace!("Input: {:?}", String::from_utf8(bwt.to_vec()));
    for (idx, row) in matrix.iter().enumerate() {
        log::trace!("Row {}: {:?}", idx, String::from_utf8(row.clone()));
    }
    return matrix[usize::try_from(ptr).unwrap()].clone();
}

pub(crate) fn decode_bwt(bwt: &[u8], ptr: usize) -> Vec<u8> {
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

impl Decoder {
    pub fn ignore_crc(&mut self) {
        self.ignore_crc = true;
    }

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
                        self.stream_crc = 0;
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
                    if magic == crate::common::STREAM_FOOTER_MAGIC {
                        log::trace!("Saw streamfooter");
                        self.state = DecoderState::StreamFooter { idx: 6 };
                        Ok(None)
                    } else if magic == crate::common::BLOCK_MAGIC {
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
                    self.selectors_mtf = (0..num_trees).collect();
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
                            while consume_bit(&mut self.accumulator).unwrap() {
                                selector_number += 1
                            }
                            if selector_number > self.num_trees {
                                Err("invalid selector")
                            } else {
                                let result =
                                    self.selectors_mtf.remove(usize::from(selector_number));
                                self.selectors.push(result);
                                self.selectors_mtf.insert(0, result);
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
                        log::trace!("Trying to eat {} depths.", self.stack.len() + 2);
                        let mut tree = BTreeMap::new();
                        for value in 0u16..u16::try_from(self.stack.len() + 2).unwrap() {
                            //log::trace!("Considering value {:?}", value);
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
                        let tree = depth_map_to_code_map(&tree);
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
                    if bits.len() > 20 {
                        return Err("bit sequence doesn't match a known huffman code");
                    }
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
                            return Ok(Some(self.decode_block()?));
                        }
                        self.block_symbols.push(*symbol);
                        self.accumulator.drain(..cursor);
                        return Ok(None);
                    }
                }
            }
            DecoderState::StreamFooter { ref mut idx } => match idx {
                6 => {
                    let crc = consume_bytes(&mut self.accumulator, 4)?;
                    if !self.ignore_crc && crc != self.stream_crc.to_be_bytes() {
                        return Err("stream CRC mismatch");
                    }
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

    fn decode_block(&mut self) -> Result<Vec<u8>, &'static str> {
        self.un_rle2();
        self.un_mtf();
        self.un_bwt();
        self.un_rle1();
        let mut tmp = Vec::new();
        std::mem::swap(&mut self.block_symbols2, &mut tmp);
        self.trees.clear();
        self.selectors.clear();
        self.block_symbols.clear();
        self.stack.clear();
        self.crc32.clear();
        self.num_sels = 0;
        self.num_trees = 0;
        let mut crc_hasher = crc::crc32::Digest::new(crc::crc32::IEEE);
        for &i in &tmp {
            crc::crc32::Hasher32::write(&mut crc_hasher, &[i.reverse_bits()][..]);
        }
        let computed_crc = crc::crc32::Hasher32::sum32(&crc_hasher).reverse_bits();
        if !self.ignore_crc && &self.crc32[..] != &computed_crc.to_be_bytes()[..] {
            return Err("block crc mismatch");
        }
        self.stream_crc = computed_crc ^ ((self.stream_crc << 1) | (self.stream_crc >> 31));
        Ok(tmp)
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
            log::trace!("Emitting a {:?}", symbol);
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

pub fn decode(data: &[u8]) -> Vec<u8> {
    let mut result = Vec::new();
    let mut decoder = Decoder::default();
    for i in data {
        result.extend(decoder.push_byte(*i).unwrap());
    }
    result
}
