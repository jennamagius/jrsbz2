use arrayvec::ArrayVec;
use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::convert::TryInto;

pub(crate) const STREAM_FOOTER_MAGIC: &[u8] = b"\x17\x72\x45\x38\x50\x90";

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq)]
pub enum Symbol {
    RunA,
    RunB,
    Idx(u8),
}

impl Symbol {
    pub(crate) fn to_u16(&self) -> u16 {
        match self {
            Symbol::RunA => 0,
            Symbol::RunB => 1,
            Symbol::Idx(a) => u16::from(*a) + 2,
        }
    }
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

fn code_to_bits(mut code: usize, bits: u8) -> Vec<bool> {
    let mut result = Vec::new();
    for _ in 0..bits {
        result.push(code & 1 != 0);
        code >>= 1;
    }
    result.into_iter().rev().collect()
}

/// Converts a mapping of { symbol : bit_depth } into a mapping of { symbol : bit_representation } as a canonical huffman code.
pub(crate) fn depth_map_to_code_map(tree: &BTreeMap<u16, u8>) -> BTreeMap<u16, Vec<bool>> {
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
