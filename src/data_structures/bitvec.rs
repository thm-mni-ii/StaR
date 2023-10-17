use bitvec::prelude::*;

#[derive(Debug, PartialEq, Clone, Eq)]
pub struct FastBitvec {
    pub bitvec: BitVec,
    //ones: HashSet<usize>,
    //zeros: HashSet<usize>,
}

impl FastBitvec {
    pub fn new(size: usize) -> Self {
        Self {
            bitvec: bitvec![0; size],
            //ones: HashSet::new(),
            //zeros: HashSet::from_iter(0..size),
        }
    }

    pub fn size(&self) -> usize {
        self.bitvec.len()
    }

    pub fn set(&mut self, index: usize, value: bool) {
        /*if value {
            self.ones.insert(index);
            self.zeros.remove(&index);
        } else {
            self.ones.remove(&index);
            self.zeros.insert(index);
        }*/
        self.bitvec.set(index, value);
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
        self.iter_0().next()
    }

    pub fn choice_1(&self) -> Option<usize> {
        self.iter_1().next()
    }
}
