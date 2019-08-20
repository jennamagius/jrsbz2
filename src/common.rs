use arrayvec::ArrayVec;
use std::collections::BTreeMap;
use std::convert::TryFrom;

pub(crate) const STREAM_FOOTER_MAGIC: &[u8] = b"\x17\x72\x45\x38\x50\x90";
pub(crate) const BLOCK_MAGIC: &[u8] = b"\x31\x41\x59\x26\x53\x59";

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq)]
pub enum Symbol {
    RunA,
    RunB,
    Idx(u16),
    Eob,
}

impl Symbol {
    pub(crate) fn to_u16(&self, syms: &[u8]) -> Result<u16, &'static str> {
        log::trace!("to_u16: {:?}, {:?}", self, syms);
        Ok(match self {
            Symbol::RunA => 0,
            Symbol::RunB => 1,
            Symbol::Idx(a) => a.checked_add(1).ok_or("BUG: Symbol::to_u16 Idx overflow")?,
            Symbol::Eob => u16::try_from(syms.len())
                .map_err(|_| "BUG: Symbol::to_u16 too many symbols")?
                .checked_add(1)
                .ok_or("BUG: Symbol::to_u16 overflow finding index for Eob")?,
        })
    }
}

pub fn abencode(mut zerocnt: u32) -> Result<ArrayVec<[Symbol; 32]>, &'static str> {
    zerocnt += 1;
    let len = 32u32
        .checked_sub(
            zerocnt
                .leading_zeros()
                .checked_add(1)
                .ok_or("BUG: integer overflow")?,
        )
        .ok_or("cannot abencode 0")?;
    let mut result = ArrayVec::new();
    for i in 0..len {
        if zerocnt & (1 << i) > 0 {
            result
                .try_push(Symbol::RunB)
                .map_err(|_| "zerocnt too large")?;
        } else {
            result
                .try_push(Symbol::RunA)
                .map_err(|_| "zerocnt too large")?;
        }
    }
    Ok(result)
}

pub fn abdecode(symbols: &[Symbol]) -> Result<u32, &'static str> {
    let mut result = 0u32;
    for &i in symbols.iter().rev() {
        if !(i == Symbol::RunA || i == Symbol::RunB) {
            return Err("invalid abdecode input");
        }
        result <<= 1;
        if i == Symbol::RunB {
            result |= 1;
        }
    }
    result |= 1 << symbols.len();
    result = result.checked_sub(1).ok_or("integer underflow")?;
    Ok(result)
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

const BACKING_BUFFER_CAPACITY: usize = 900_000;

pub(crate) struct BackingBuffer([u8; BACKING_BUFFER_CAPACITY]);

unsafe impl arrayvec::Array for BackingBuffer {
    type Item = u8;
    type Index = u32;

    fn as_ptr(&self) -> *const u8 {
        self.0.as_ptr()
    }

    fn as_mut_ptr(&mut self) -> *mut u8 {
        self.0.as_mut_ptr()
    }

    fn capacity() -> usize {
        BACKING_BUFFER_CAPACITY
    }
}

impl Default for BackingBuffer {
    fn default() -> Self {
        BackingBuffer([0u8; BACKING_BUFFER_CAPACITY])
    }
}
