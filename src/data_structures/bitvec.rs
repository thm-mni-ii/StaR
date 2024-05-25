use bitvec::prelude::*;

#[derive(Debug, PartialEq, Clone, Eq)]
/// A bit vector that allows to get the first 0 and the first 1 in O(1) time.
pub struct FastBitvec {
    pub bitvec: BitVec,
    first_zero: Option<usize>,
    first_one: Option<usize>,
}

impl FastBitvec {
    /// Create a new FastBitvec with a given size.
    /// # Example
    /// ```
    /// use star::data_structures::bitvec::FastBitvec;
    /// let bitvec = FastBitvec::new(10);
    /// assert_eq!(bitvec.size(), 10);
    /// ```

    pub fn new(size: usize) -> Self {
        Self {
            bitvec: bitvec![0; size],
            first_zero: Some(0),
            first_one: None,
        }
    }

    /// Get the size of a bit vector.
    /// # Example
    /// ```
    /// use star::data_structures::bitvec::FastBitvec;
    /// let bitvec = FastBitvec::new(10);
    /// assert_eq!(bitvec.size(), 10);
    /// ```
    pub fn size(&self) -> usize {
        self.bitvec.len()
    }

    /// Set a value in a bit vector at a given index.
    /// # Example
    /// ```
    /// use star::data_structures::bitvec::FastBitvec;
    /// let mut bitvec = FastBitvec::new(10);
    /// bitvec.set(0, true);
    /// assert_eq!(bitvec.get(0), true);
    /// ```
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

        if value && self.first_one.is_some() && index < self.first_one.unwrap() {
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

        if !value && self.first_zero.is_some() && index < self.first_zero.unwrap() {
            self.first_zero = Some(index);
        
        }
    }

    pub fn set_0(&mut self, index: usize, value: bool, degrees: &Vec<(usize, usize)>) {
        self.bitvec.set(index, value);
        
        if self.first_zero == None {
            return;
        }
        if value && degrees[self.first_zero.unwrap()].0 == index {
            let mut next_zero = None;

            for i in self.first_zero.unwrap()..self.size() {
                if !self.get(degrees[i].0) {
                    next_zero = Some(i);
                    break;
                }
            }
            self.first_zero = next_zero;
        }

        if !value && self.first_zero.is_some() && index < self.first_zero.unwrap() {
            self.first_zero = Some(index);
        
        }
    }

    /// Get a value from a bit vector at a given index.
    /// # Example
    /// ```
    /// use star::data_structures::bitvec::FastBitvec;
    /// let mut bitvec = FastBitvec::new(10);
    /// bitvec.set(0, true);
    /// assert_eq!(bitvec.get(0), true);
    /// ```
    pub fn get(&self, index: usize) -> bool {
        *self.bitvec.get(index).as_deref().unwrap()
    }

    /// Iterate over all ones in a bit vector.
    /// # Example
    /// ```
    /// use star::data_structures::bitvec::FastBitvec;
    /// let mut bitvec = FastBitvec::new(10);
    /// bitvec.set(0, true);
    /// let mut iter = bitvec.iter_1();
    /// assert_eq!(iter.next(), Some(0));
    /// ```
    pub fn iter_1(&self) -> impl Iterator<Item = usize> + '_ {
        self.bitvec.iter_ones()
    }

    /// Iterate over all zeros in a bit vector.
    /// # Example
    /// ```
    /// use star::data_structures::bitvec::FastBitvec;
    /// let mut bitvec = FastBitvec::new(10);
    /// let mut iter = bitvec.iter_0();
    /// assert_eq!(iter.next(), Some(0));
    /// ```
    pub fn iter_0(&self) -> impl Iterator<Item = usize> + '_ {
        self.bitvec.iter_zeros()
    }

    /// Get the first zero in a bit vector.
    /// # Example
    /// ```
    /// use star::data_structures::bitvec::FastBitvec;
    /// let mut bitvec = FastBitvec::new(10);
    /// bitvec.set(0, true);
    /// assert_eq!(bitvec.choice_0(), Some(1));
    /// ```
    pub fn choice_0(&self) -> Option<usize> {
        self.first_zero
    }

    pub fn choice_0_1(&self, degrees: &Vec<(usize, usize)>) -> Option<usize> {
        if self.first_zero == None { return None }
        Some(degrees[self.first_zero.unwrap()].0)
    }

    /// Get the first one in a bit vector.
    /// # Example
    /// ```
    /// use star::data_structures::bitvec::FastBitvec;
    /// let mut bitvec = FastBitvec::new(10);
    /// bitvec.set(0, true);
    /// assert_eq!(bitvec.choice_1(), Some(0));
    /// ```
    pub fn choice_1(&self) -> Option<usize> {
        self.first_one
    }
}

/*#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fast_bitvec() {
        let mut bitvec = FastBitvec::new(10);
        assert_eq!(bitvec.size(), 10);

        bitvec.set(0, true);
        assert_eq!(bitvec.get(0), true);
        assert_eq!(bitvec.choice_1(), Some(0));
        assert_eq!(bitvec.choice_0(), Some(1));

        bitvec.set(1, true);
        assert_eq!(bitvec.get(1), true);
        assert_eq!(bitvec.choice_1(), Some(0));
        assert_eq!(bitvec.choice_0(), Some(2));

        bitvec.set(0, false);
        assert_eq!(bitvec.get(0), false);
        assert_eq!(bitvec.choice_1(), Some(1));
        assert_eq!(bitvec.choice_0(), Some(0));

        bitvec.set(1, false);
        assert_eq!(bitvec.get(1), false);
        assert_eq!(bitvec.choice_1(), None);
        assert_eq!(bitvec.choice_0(), Some(0));
    }
}*/
