use bitvec::prelude::*;

#[derive(Debug, PartialEq, Clone, Eq)]
pub struct FastBitvec {
    pub bitvec: BitVec,
    first_zero: Option<usize>,
    first_one: Option<usize>,
}

impl FastBitvec {
    pub fn new(size: usize) -> Self {
        Self {
            bitvec: bitvec![0; size],
            first_zero: Some(0),
            first_one: None,
        }
    }

    pub fn size(&self) -> usize {
        self.bitvec.len()
    }

    pub fn set(&mut self, index: usize, value: bool) {
        self.bitvec.set(index, value);

        if value && self.first_zero == Some(index) {
            let mut next_zero = None;

            for i in index..self.size() {
                if !self.get(i) {
                    next_zero = Some(i);
                    break;
                }
            }
            self.first_zero = next_zero;
        }

        if value && self.first_one.is_none() {
            self.first_one = Some(index);
        }

        if !value && self.first_one == Some(index) {
            let mut next_one = None;

            for i in index..self.size() {
                if self.get(i) {
                    next_one = Some(i);
                    break;
                }
            }
            self.first_one = next_one;
        }
    }

    pub fn get(&self, index: usize) -> bool {
        *self.bitvec.get(index).as_deref().unwrap()
    }

    pub fn iter_1(&self) -> impl Iterator<Item = usize> + '_ {
        self.bitvec.iter_ones()
    }

    pub fn iter_0(&self) -> impl Iterator<Item = usize> + '_ {
        self.bitvec.iter_zeros()
    }

    pub fn choice_0(&self) -> Option<usize> {
        self.first_zero
    }

    pub fn choice_1(&self) -> Option<usize> {
        self.first_one
    }
}
