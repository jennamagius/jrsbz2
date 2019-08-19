use arrayvec::ArrayVec;

pub struct ArrayBitVec<T>
where
    T: arrayvec::Array<Item = u8>,
{
    start: usize,
    len: usize,
    buffer: ArrayVec<T>,
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

    pub fn get(&self, idx: usize) -> bool {
        let byte_idx = (self.start + idx) / 8;
        let misalignment = (self.start + idx) % 8;
        let mut mask = 0b1000_0000;
        mask >>= misalignment;
        self.buffer[byte_idx] & mask != 0
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
}
