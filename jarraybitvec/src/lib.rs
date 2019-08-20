use arrayvec::ArrayVec;

pub struct ArrayBitVec<T>
where
    T: arrayvec::Array<Item = u8>,
{
    start: usize,
    len: usize,
    buffer: ArrayVec<T>,
}

impl<T> Default for ArrayBitVec<T>
where
    T: arrayvec::Array<Item = u8>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T> ArrayBitVec<T>
where
    T: arrayvec::Array<Item = u8>,
{
    pub fn new() -> ArrayBitVec<T> {
        let mut buffer = ArrayVec::default();
        // buffer.resize(buffer.capacity(), 0);
        for _ in 0..buffer.capacity() {
            buffer.push(0);
        }
        ArrayBitVec {
            start: 0,
            len: 0,
            buffer,
        }
    }

    pub fn push_bit(&mut self, bit: bool) {
        self.try_push_bit(bit).expect("capacity exceeded");
    }

    pub fn pop_bit_front(&mut self) -> bool {
        self.try_pop_bit_front().expect("out of bounds")
    }

    pub fn try_pop_bit_front(&mut self) -> Option<bool> {
        let result = self.try_get(0)?;
        self.start += 1;
        self.len -= 1;
        Some(result)
    }

    pub fn try_push_bit(&mut self, bit: bool) -> Result<(), ()> {
        let byte_idx = (self.start + self.len) / 8;
        if byte_idx >= self.buffer.len() {
            return Err(());
        }
        let misalignment = (self.start + self.len) % 8;
        let mut mask = 0b1000_0000;
        mask >>= misalignment;
        if bit {
            self.buffer[byte_idx] |= mask;
        } else {
            self.buffer[byte_idx] &= mask ^ 0xFF;
        }
        self.len += 1;
        Ok(())
    }

    pub fn clear(&mut self) {
        self.start = 0;
        self.len = 0;
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get(&self, idx: usize) -> bool {
        self.try_get(idx).expect("out of bounds")
    }

    pub fn try_get(&self, idx: usize) -> Option<bool> {
        if idx > self.len() {
            return None;
        }
        let byte_idx = (self.start + idx) / 8;
        let misalignment = (self.start + idx) % 8;
        let mut mask = 0b1000_0000;
        mask >>= misalignment;
        Some(self.buffer.get(byte_idx)? & mask != 0)
    }

    pub fn iter(&self) -> Iterator<T> {
        Iterator {
            idx: 0,
            parent: self,
        }
    }

    pub fn advance(&mut self, amt: usize) {
        self.start += amt;
        self.len -= amt;
    }
}

pub struct Iterator<'a, T>
where
    T: arrayvec::Array<Item = u8>,
{
    idx: usize,
    parent: &'a ArrayBitVec<T>,
}

impl<'a, T> std::iter::Iterator for Iterator<'a, T>
where
    T: arrayvec::Array<Item = u8>,
{
    type Item = bool;

    fn next(&mut self) -> Option<bool> {
        if self.parent.len() <= self.idx {
            None
        } else {
            let result = self.parent.get(self.idx);
            self.idx += 1;
            Some(result)
        }
    }
}

#[cfg(test)]
#[test]
fn basic_tests() {
    let mut my_buffer = ArrayBitVec::<[u8; 1]>::new();
    my_buffer.push_bit(false);
    my_buffer.push_bit(true);
    my_buffer.push_bit(false);
    my_buffer.push_bit(false);
    my_buffer.push_bit(true);
    assert_eq!(my_buffer.get(0), false);
    assert_eq!(my_buffer.get(1), true);
    assert_eq!(my_buffer.get(2), false);
    assert_eq!(my_buffer.get(3), false);
    assert_eq!(my_buffer.get(4), true);
    let stuff: Vec<bool> = my_buffer.iter().collect();
    assert_eq!(&stuff[..], &[false, true, false, false, true][..]);
    my_buffer.advance(1);
    let stuff: Vec<bool> = my_buffer.iter().collect();
    assert_eq!(&stuff[..], &[true, false, false, true][..]);
    assert_eq!(my_buffer.pop_bit_front(), true);
    let stuff: Vec<bool> = my_buffer.iter().collect();
    assert_eq!(&stuff[..], &[false, false, true][..]);
}
