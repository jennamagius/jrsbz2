use arrayvec::ArrayVec;
use std::collections::BTreeMap;
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
    let stack = mtf_encode(&mut data);
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

pub fn canonicalize_huff(huff: BTreeMap<Symbol, Vec<bool>>) -> BTreeMap<Symbol, Vec<bool>> {
    let max_len = huff.values().map(|x| x.len()).max().unwrap();
    let min_len = huff.values().map(|x| x.len()).min().unwrap();
    let mut result = BTreeMap::new();
    for i in min_len..=max_len {
        let mut symbols_at_len: Vec<Symbol> = huff
            .iter()
            .filter(|(_k, v)| v.len() == i)
            .map(|(k, _v)| k.clone())
            .collect();
        let mut reprs_at_len: Vec<Vec<bool>> = huff
            .iter()
            .filter(|(_k, v)| v.len() == i)
            .map(|(_k, v)| v.clone())
            .collect();
        symbols_at_len.sort();
        reprs_at_len.sort();
        for (repr, symbol) in reprs_at_len.into_iter().zip(symbols_at_len.into_iter()) {
            result.insert(symbol, repr);
        }
    }
    result
}

#[cfg(test)]
#[test]
fn huff_test() {
    let data = b"aaaaaaaaaaaaaaabbbbbbbccccccddddddeeeee".to_vec();
    let mut data: Vec<Symbol> = data.iter().map(|x| Symbol::Idx(*x)).collect();
    let tree = huff_encode(&data);
    println!("Tree: {:?}", tree);
    println!("Map: {:?}", huff_to_bits(&tree, vec![]));
    println!(
        "Canonical map: {:?}",
        canonicalize_huff(huff_to_bits(&tree, vec![]))
    );
    match tree {
        HuffmanNode::Node {
            weight,
            left,
            right,
        } => match *left {
            HuffmanNode::Leaf { symbol, weight } => {
                assert_eq!(symbol, Symbol::Idx(b'a'));
                assert_eq!(weight, 15);
            }
            _ => panic!(),
        },
        _ => panic!(),
    }
}
