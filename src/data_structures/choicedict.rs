type Word = u32;
type BlockIndex = usize;
type WordIndex = usize;
type Color = usize;

#[derive(PartialEq)]
/// A 2-color choice dictionary based on the ideas presented in <https://drops.dagstuhl.de/opus/volltexte/2018/10014/pdf/LIPIcs-ISAAC-2018-66.pdf>
/// (DOI: 10.4230/LIPIcs.ISAAC.2018.66).
///
/// Each element of a 2-color choice dictionary either has color 0 or color 1.
/// Intuitively, a 2-color choice dictionary can be thought of as a bit vector that supports the usual read and write operations in time O(1).
/// What makes the data structure special is that it also supports the choice<sub>c</sub> operation, i.e, retrieving an element with color c,
/// in time O(1) while still occupying only n + O(1) bits.
pub struct ChoiceDict {
    a: Vec<Word>,
    bar0: BlockIndex,
    bar1: BlockIndex,
    size: usize,
}

impl ChoiceDict {
    /// Returns a choice dictionary with `size` elements.
    ///
    /// Initially, all elements have color 0.
    ///
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choicedict::ChoiceDict;
    ///
    /// let dict = ChoiceDict::new(1000);
    /// ```
    pub fn new(size: usize) -> Self {
        let num_words = size.div_ceil(Word::BITS as usize);
        let num_words_padded = if num_words % block_size() == 0 {
            num_words
        } else {
            (num_words / block_size() + 1) * block_size()
        };
        let num_blocks = num_words_padded / block_size();
        if num_blocks >= Word::MAX as usize {
            panic!("size too large");
        }

        Self {
            a: vec![0; num_words_padded],
            bar0: num_blocks,
            bar1: 0,
            size,
        }
    }

    /// Returns an iterator for iterating over all elements of color 0.
    ///
    /// Time complexity per `next()` call: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choicedict::ChoiceDict;
    ///
    /// let mut dict = ChoiceDict::new(1000);
    /// for i in 0..1000 {
    ///   dict.set1(i);
    /// }
    /// dict.set0(372);
    /// let mut it = dict.iter0();
    /// let elem = it.next();
    /// assert_eq!(elem, Some(372));
    /// ```
    pub fn iter0(&self) -> ChoiceDictIterator {
        ChoiceDictIterator::new(self, 0)
    }

    /// Returns an iterator for iterating over all elements of color 1.
    ///
    /// Time complexity per `next()` call: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choicedict::ChoiceDict;
    ///
    /// let mut dict = ChoiceDict::new(1000);
    /// dict.set1(17);
    /// let mut it = dict.iter1();
    /// assert_eq!(it.next(), Some(17));
    /// assert_eq!(it.next(), None);
    /// ```
    pub fn iter1(&self) -> ChoiceDictIterator {
        ChoiceDictIterator::new(self, 1)
    }

    /// Returns the index of an arbitrary element of color 0 (if present).
    ///
    /// Time complexity: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choicedict::ChoiceDict;
    ///
    /// let mut dict = ChoiceDict::new(1000);
    /// for i in 0..1000 {
    ///   dict.set1(i);
    /// }
    /// assert_eq!(dict.choice0(), None);
    /// dict.set0(703);
    /// assert_eq!(dict.choice0(), Some(703));
    /// ```
    pub fn choice0(&self) -> Option<usize> {
        self.iter0().next()
    }

    /// Returns the index of an arbitrary element of color 1 (if present).
    ///
    /// Time complexity: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choicedict::ChoiceDict;
    ///
    /// let mut dict = ChoiceDict::new(1000);
    /// assert_eq!(dict.choice1(), None);
    /// dict.set1(180);
    /// assert_eq!(dict.choice1(), Some(180));
    /// ```
    pub fn choice1(&self) -> Option<usize> {
        self.iter1().next()
    }

    /// Sets the color of all elements to 0.
    ///
    /// Time complexity: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choicedict::ChoiceDict;
    ///
    /// let mut dict = ChoiceDict::new(1000);
    /// dict.set1(100);
    /// dict.set1(263);
    /// dict.set1(827);
    /// dict.init0();
    /// assert_eq!(dict.choice1(), None);
    /// ```
    pub fn init0(&mut self) {
        self.bar0 = self.max_block();
        self.bar1 = 0;
    }

    /// Sets the color of all elements to 1.
    ///
    /// Time complexity: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choicedict::ChoiceDict;
    ///
    /// let mut dict = ChoiceDict::new(1000);
    /// dict.init1();
    /// assert_eq!(dict.choice0(), None);
    /// ```
    pub fn init1(&mut self) {
        self.bar1 = self.max_block();
        self.bar0 = 0;
    }

    /// Returns the color of the element at the given index.
    ///
    /// Time complexity: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choicedict::ChoiceDict;
    ///
    /// let mut dict = ChoiceDict::new(1000);
    /// dict.set1(532);
    /// let elem = dict.get(532);
    /// assert_eq!(elem, 1);
    /// ```
    pub fn get(&self, index: usize) -> Word {
        self.check_bounds(index);

        let wi = e2w(index);
        let bi = w2b(wi);

        let block = self.block(bi);

        // disconnected from 0-area
        if !self.is_connected(&block, 0) {
            return 1;
        }

        // disconnected from 1-area
        if !self.is_connected(&block, 1) {
            return 0;
        }

        let wrd = self.read_word_chained(wi);
        let offset = index % Word::BITS as usize;

        get_bit(wrd, offset)
    }

    /// Sets the color of the element at the given index to 1.
    ///
    /// Time complexity: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choicedict::ChoiceDict;
    ///
    /// let mut dict = ChoiceDict::new(1000);
    /// dict.set1(692);
    /// assert_eq!(dict.get(692), 1);
    /// ```
    pub fn set1(&mut self, index: usize) {
        self.write(index, 1)
    }

    /// Sets the color of the element at the given index to 0.
    ///
    /// Time complexity: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choicedict::ChoiceDict;
    ///
    /// let mut dict = ChoiceDict::new(1000);
    /// dict.set1(302);
    /// assert_eq!(dict.get(302), 1);
    /// dict.set0(302);
    /// assert_eq!(dict.get(302), 0);
    /// ```
    pub fn set0(&mut self, index: usize) {
        self.write(index, 0)
    }

    fn read_word_chained(&self, w: WordIndex) -> Word {
        let bi = w2b(w);
        let block_i = self.block(bi);

        for i in 0..=1 {
            if !block_i.is_left[i] && w % block_size() == i {
                return match block_i.chained_to[i] {
                    None => self.a[w],
                    Some(bj) => {
                        let wj = b2w(bj);
                        self.a[wj + 2]
                    }
                };
            }
        }

        self.a[w]
    }

    fn write(&mut self, index: usize, c: Color) {
        assert!(c == 0 || c == 1);

        self.check_bounds(index);

        if self.get(index) == c as Word {
            return;
        }

        let w = e2w(index);
        let b = w2b(w);
        let block = self.block(b);

        if block.is_left[c] {
            match block.chained_to[c] {
                Some(_) => {
                    self.connect(&block, c);
                    self.write_chained(index, w, c);
                }
                None => {
                    self.write_chained(index, w, c);
                }
            }
        } else {
            match block.chained_to[c] {
                Some(_) => {
                    self.write_chained(index, w, c);
                }
                None => {
                    self.connect(&block, c);
                    self.write_chained(index, w, c);
                }
            }
        }
    }

    fn write_chained(&mut self, index: usize, w: WordIndex, c: Color) {
        let bi = w2b(w);
        let block_i = self.block(bi);

        for i in 0..=1 {
            if !block_i.is_left[i] && w % block_size() == i {
                let bj = block_i.chained_to[i].unwrap();
                let wj = b2w(bj);
                self.update_color(&block_i, wj + 2, index, c);
                return;
            }
        }

        self.update_color(&block_i, w, index, c);
    }

    fn update_color(&mut self, block: &Block, w: WordIndex, index: usize, c: Color) {
        if c == 0 {
            self.a[w] &= !(1 << (index % Word::BITS as usize))
        } else {
            self.a[w] |= 1 << (index % Word::BITS as usize)
        }

        match w % block_size() {
            0 => self.break_chain(block.b, 0),
            1 => self.break_chain(block.b, 1),
            _ => {}
        }

        if self.is_full_block(block.b, c) {
            self.disconnect(block, 1 - c);
        }
    }

    fn break_chain(&mut self, b: BlockIndex, c: Color) {
        if let Some(bj) = self.chained_to(b, c) {
            let wj = b2w(bj);
            self.a[wj + c] = 0;
        }
    }

    fn is_full_block(&self, b: usize, c: Color) -> bool {
        let w = b2w(b);
        let val = if c == 0 { 0 } else { Word::MAX };
        self.read_word_chained(w) == val
            && self.read_word_chained(w + 1) == val
            && self.read_word_chained(w + 2) == val
    }

    fn chain(&mut self, bl: BlockIndex, br: BlockIndex, c: Color) {
        let wl = b2w(bl);
        let wr = b2w(br);
        self.a[wl + 2] = self.a[wr + c];
        self.a[wl + c] = br as Word;
        self.a[wr + c] = bl as Word;
    }

    fn unchain(&mut self, block: &Block, c: Color) -> (BlockIndex, BlockIndex) {
        let bi = block.b;
        let bj = self.chained_to(bi, c).unwrap();
        let bar = self.get_barrier(c);

        if bi <= bar {
            let wi = b2w(bi);
            let wj = b2w(bj);
            self.a[wj + c] = self.a[wi + 2];
            self.init_block(block, c);
            (bi, bj)
        } else {
            self.unchain(&self.block(bj), c)
        }
    }

    fn get_barrier(&self, c: Color) -> usize {
        if c == 0 {
            self.bar0
        } else {
            self.bar1
        }
    }

    fn set_barrier(&mut self, c: Color, bar: BlockIndex) {
        if c == 0 {
            self.bar0 = bar
        } else {
            self.bar1 = bar
        }
    }

    fn disconnect(&mut self, block: &Block, c: Color) {
        assert!(self.is_connected(block, c));

        let b = block.b;
        let bar = self.get_barrier(c);
        let b_star = bar;

        if b > bar {
            let (b_dash, _) = self.unchain(block, c);
            if b_dash != b_star {
                match self.chained_to(b_star, c) {
                    None => {
                        self.chain(b_dash, b_star, c);
                    }
                    Some(b_double_dash) => {
                        self.unchain(&self.block(b_star), c);
                        self.chain(b_dash, b_double_dash, c);
                    }
                }
            }
        } else if b != b_star {
            match self.chained_to(b_star, c) {
                None => {
                    self.chain(b, b_star, c);
                }
                Some(b_double_dash) => {
                    self.unchain(&self.block(b_star), c);
                    self.chain(b, b_double_dash, c);
                }
            }
        }

        self.set_barrier(c, bar - 1);
    }

    fn connect(&mut self, block: &Block, c: Color) {
        assert!(!self.is_connected(block, c));

        let b = block.b;
        let bar = self.get_barrier(c);
        let b_star = bar + 1;
        let mut break_chain = false;

        if b > bar {
            self.init_block(block, c);
            if b != b_star {
                match self.chained_to(b_star, c) {
                    None => {
                        self.init_block(&self.block(b_star), c);
                        self.chain(b_star, b, c);
                    }
                    Some(b_double_dash) => {
                        self.unchain(&self.block(b_star), c);
                        self.chain(b_double_dash, b, c);
                        break_chain = true;
                    }
                }
            }
        } else {
            let (_, b_dash) = self.unchain(block, c);
            if b_dash != b_star {
                match self.chained_to(b_star, c) {
                    None => {
                        self.init_block(&self.block(b_star), c);
                        self.chain(b_star, b_dash, c);
                    }
                    Some(b_double_dash) => {
                        self.unchain(&self.block(b_star), c);
                        self.chain(b_double_dash, b_dash, c);
                        break_chain = true;
                    }
                }
            } else {
                break_chain = true;
            }
        }

        self.set_barrier(c, bar + 1);
        if break_chain {
            self.break_chain(b_star, c);
        }
    }

    fn block(&self, b: BlockIndex) -> Block {
        Block {
            b,
            w: b2w(b),
            is_left: [b <= self.bar0, b <= self.bar1],
            chained_to: [self.chained_to(b, 0), self.chained_to(b, 1)],
        }
    }

    fn is_connected(&self, block: &Block, c: Color) -> bool {
        (block.is_left[c] && block.chained_to[c].is_none()) // in left area without chain
            || (!block.is_left[c] && block.chained_to[c].is_some()) // in right area with chain
    }

    fn init_block(&mut self, block: &Block, c: Color) {
        let w = block.w;
        let val = if c == 1 { 0 } else { Word::MAX };

        for i in 0..=1 {
            if c == i {
                self.a[w + i] = val;
            } else if let Some(bj) = block.chained_to[i] {
                let wj = b2w(bj);
                self.a[wj + 2] = val;
            } else {
                self.a[w + i] = val;
            }
        }

        self.a[w + 2] = val;
    }

    fn chained_to(&self, b: BlockIndex, c: Color) -> Option<usize> {
        let w = b2w(b);
        let bj = self.a[w + c] as usize;

        if bj == 0 || bj > self.max_block() {
            return None;
        }

        let wk = b2w(bj);
        let bar = if c == 0 { self.bar0 } else { self.bar1 };
        if ((b <= bar && bar < bj) || (bj <= bar && bar < b)) && self.a[wk + c] == b as Word {
            return Some(bj);
        }

        None
    }

    fn max_block(&self) -> usize {
        self.a.len() / block_size()
    }

    fn check_bounds(&self, index: usize) {
        if index >= self.size {
            panic!("index out of bounds");
        }
    }
}

/// An iterator that iterates over the elements of a specific color in a choice dictionary.
pub struct ChoiceDictIterator<'a> {
    dict: &'a ChoiceDict,
    word: Word,
    c: Color,
    b: BlockIndex, // index of current block
    w: WordIndex,  // index of current word
    i: usize,      // index of current word in current block
    j: usize,      // index of current element in current word
    is_c_full: bool,
}

impl ChoiceDictIterator<'_> {
    fn new(dict: &'_ ChoiceDict, c: Color) -> ChoiceDictIterator<'_> {
        let mut it = ChoiceDictIterator {
            dict,
            word: 0,
            c,
            b: 0,
            w: 0,
            i: 0,
            j: 0,
            is_c_full: false,
        };
        it.next_block();

        it
    }

    fn next_block(&mut self) {
        self.b += 1;

        if self.b > self.dict.get_barrier(self.c) {
            return;
        }

        let (b, w) = match self.dict.chained_to(self.b, self.c) {
            Some(bj) => (bj, b2w(bj)),
            None => (self.b, b2w(self.b)),
        };

        self.is_c_full = (b <= self.dict.get_barrier(1 - self.c)
            && self.dict.chained_to(b, 1 - self.c).is_some())
            || (b > self.dict.get_barrier(1 - self.c)
                && self.dict.chained_to(b, 1 - self.c).is_none());

        self.i = 0;
        self.w = w;
        self.word = self.dict.read_word_chained(w);
    }

    fn next_word(&mut self) {
        self.j = 0;
        self.i += 1
    }
}

impl Iterator for ChoiceDictIterator<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        while self.b <= (self.dict.get_barrier(self.c)) {
            while self.i < block_size() {
                let w: usize = self.w + self.i;
                let word: Word = if self.is_c_full {
                    0
                } else {
                    self.dict.read_word_chained(w)
                };

                while self.j < Word::BITS as usize {
                    let j = self.j;
                    self.j += 1;
                    let idx = w * Word::BITS as usize + j;

                    if idx < self.dict.size
                        && (self.is_c_full || get_bit(word, j) as usize == self.c)
                    {
                        return Some(idx);
                    }
                }

                self.next_word()
            }

            self.next_block();
        }

        None
    }
}

#[derive(Debug)]
struct Block {
    b: BlockIndex,
    w: WordIndex,
    is_left: [bool; 2],
    chained_to: [Option<usize>; 2],
}

fn block_size() -> usize {
    3
}

fn get_bit(word: Word, index: usize) -> Word {
    Word::from(word & (1 << index) != 0)
}

// element index to word index
fn e2w(index: usize) -> WordIndex {
    index / Word::BITS as usize
}

// word index to block index
fn w2b(w: WordIndex) -> BlockIndex {
    w / block_size() + 1
}

// block index to word index
fn b2w(b: BlockIndex) -> WordIndex {
    b * block_size() - block_size()
}

#[cfg(test)]
mod tests {
    use super::{ChoiceDict, Color, Word};
    use crate::data_structures::choicedict::block_size;
    use rand::{rngs::StdRng, Rng, SeedableRng};
    use std::collections::HashSet;

    #[test]
    fn test_new() {
        let dict = ChoiceDict::new(100);
        for i in 0..dict.size {
            assert_eq!(dict.get(i), 0);
        }
    }

    #[test]
    fn test_set_and_get() {
        let mut dict = ChoiceDict::new(100);
        for i in [23, 62, 99, 0] {
            dict.set1(i);
            assert_eq!(dict.get(i), 1);
            dict.set0(i);
            assert_eq!(dict.get(i), 0);
        }
    }

    #[test]
    fn test_set_and_get_all_forward() {
        let mut dict = ChoiceDict::new(100);
        for i in 0..dict.size {
            dict.set1(i);
        }
        for i in 0..dict.size {
            assert_eq!(dict.get(i), 1);
        }
        for i in 0..dict.size {
            dict.set0(i);
        }
        for i in 0..dict.size {
            assert_eq!(dict.get(i), 0);
        }
    }

    #[test]
    fn test_set_and_get_all_backward() {
        let mut dict = ChoiceDict::new(100);
        for i in 0..dict.size {
            dict.set1(dict.size - i - 1);
        }
        for i in 0..dict.size {
            assert_eq!(dict.get(i), 1);
        }
        for i in 0..dict.size {
            dict.set0(dict.size - i - 1);
        }
        for i in 0..dict.size {
            assert_eq!(dict.get(i), 0);
        }
    }

    #[test]
    fn test_init() {
        let mut dict = ChoiceDict::new(100);
        dict.init1();
        for i in 0..dict.size {
            assert_eq!(dict.get(i), 1);
        }
        dict.init0();
        for i in 0..dict.size {
            assert_eq!(dict.get(i), 0);
        }
    }

    #[test]
    fn test_choice() {
        let mut dict = ChoiceDict::new(100);

        assert!(dict.choice0().is_some());
        assert!(dict.choice1().is_none());

        dict.set1(10);

        assert!(dict.choice0().is_some());
        assert_eq!(dict.choice1(), Some(10));
    }

    #[test]
    fn test_iterate() {
        let mut dict = ChoiceDict::new(100);
        let indices = [20, 1, 33, 99, 0];
        for i in indices {
            dict.set1(i);
        }
        let elems_1: HashSet<Color> = dict.iter1().collect();
        let elems_0: HashSet<Color> = dict.iter0().collect();

        assert_eq!(elems_1.len(), indices.len());
        assert_eq!(elems_0.len(), dict.size - indices.len());

        for i in indices {
            assert!(elems_1.contains(&i));
        }
    }

    #[test]
    fn test_init_and_iterate() {
        let size = 5 * block_size() * Word::BITS as usize;
        let mut dict = ChoiceDict::new(size);
        dict.init1();
        let elems_1: HashSet<Color> = dict.iter1().collect();
        assert_eq!(elems_1.len(), dict.size);
        for i in 0..dict.size {
            assert!(elems_1.contains(&i));
        }
        dict.init0();
        let elems_0: HashSet<Color> = dict.iter0().collect();
        assert_eq!(elems_0.len(), dict.size);
        for i in 0..dict.size {
            assert!(elems_0.contains(&i));
        }
    }

    #[test]
    fn test_connect_and_disconnect() {
        let num_blocks = 2;
        let size = num_blocks * 3 * Word::BITS as usize;
        let mut dict = ChoiceDict::new(size);

        assert_eq!(dict.bar0, num_blocks);
        assert_eq!(dict.bar1, 0);

        for i in 0..(3 * Word::BITS as usize) {
            dict.set1(i);
        }

        assert_eq!(dict.bar0, num_blocks - 1);
        assert_eq!(dict.bar1, 1);

        for i in 0..(3 * Word::BITS as usize) {
            dict.set0(i);
        }

        assert_eq!(dict.bar0, num_blocks);
        assert_eq!(dict.bar1, 0);
    }

    #[test]
    fn test_break_accidental_0_chain() {
        let mut dict = ChoiceDict::new(21 * Word::BITS as usize);
        dict.a[7] = 6;
        dict.a[15] = 3;
        dict.a[16] = 3;
        dict.a[18] = 6;
        dict.bar0 = 6;
        dict.bar1 = 5;
        dict.set1(15 * Word::BITS as usize + 2);
        assert_eq!(dict.a[15], 7);
        assert!(dict.a[18] != 6);
    }

    #[test]
    fn test_break_accidental_1_chain() {
        let mut dict = ChoiceDict::new(21 * Word::BITS as usize);
        dict.a[6] = 6;
        dict.a[15] = 3;
        dict.a[16] = 3;
        dict.a[19] = 6;
        dict.bar1 = 6;
        dict.bar0 = 5;
        dict.set1(16 * Word::BITS as usize + 2);
        assert_eq!(dict.a[16], 7);
        assert!(dict.a[19] != 6);
    }

    #[test]
    fn test_fuzzy_inputs_element_wise() {
        let seed = [1; 32];
        let mut rng = StdRng::from_seed(seed);
        let count = if cfg!(miri) { 3 } else { 10 };

        for _ in 0..count {
            let size = rng.gen_range(1..1000);
            let mut dict = ChoiceDict::new(size);
            let mut vec = vec![0; size];
            let inner_count = if cfg!(miri) { 3 } else { size * 3 };
            let p: f64 = rng.gen();

            for _ in 0..inner_count {
                let idx = rng.gen_range(0..size);
                let c = rng.gen_bool(p) as Color;
                write_and_compare(&mut dict, &mut vec, idx, c);
                if rng.gen_bool(0.1) {
                    iterate_and_compare(&dict, &vec, rng.gen_bool(0.5) as usize);
                }
                if rng.gen_bool(0.1) {
                    init_and_compare(&mut dict, &mut vec, rng.gen_bool(0.5) as usize);
                }
            }
        }
    }

    #[test]
    fn test_fuzzy_inputs_block_wise() {
        let seed = [1; 32];
        let mut rng = StdRng::from_seed(seed);
        let count = if cfg!(miri) { 3 } else { 10 };

        for _ in 0..count {
            let size = rng.gen_range(1..1000);
            let mut dict: ChoiceDict = ChoiceDict::new(size);
            let mut vec = vec![0; size];
            let inner_count = if cfg!(miri) { 3 } else { size * 3 };
            let p: f64 = rng.gen();
            for _ in 0..inner_count {
                let c = rng.gen_bool(p) as Color;
                let b = rng.gen_range(0..dict.max_block());
                let block_start = b * block_size() * Word::BITS as usize;
                let block_end = block_start + block_size() * Word::BITS as usize;

                for i in block_start..block_end {
                    if i >= dict.size {
                        break;
                    }
                    write(&mut dict, &mut vec, i, c);
                }

                write_and_compare(&mut dict, &mut vec, block_start, c);

                if rng.gen_bool(0.1) {
                    iterate_and_compare(&dict, &vec, rng.gen_bool(0.5) as usize);
                }

                if rng.gen_bool(0.1) {
                    init_and_compare(&mut dict, &mut vec, rng.gen_bool(0.5) as usize);
                }
            }
        }
    }

    fn write(dict: &mut ChoiceDict, vec: &mut [Word], index: usize, c: Color) {
        if c == 0 {
            dict.set0(index);
        } else {
            dict.set1(index);
        }

        vec[index] = c as Word;
    }

    fn write_and_compare(dict: &mut ChoiceDict, vec: &mut Vec<Word>, index: usize, c: Color) {
        write(dict, vec, index, c);
        assert_eq!(dict_to_vec(dict), *vec);
    }

    fn init_and_compare(dict: &mut ChoiceDict, vec: &mut Vec<Word>, c: Color) {
        if c == 0 {
            dict.init0();
        } else {
            dict.init1();
        }

        for v in vec.iter_mut() {
            *v = u32::from(c != 0);
        }

        assert_eq!(dict_to_vec(dict), *vec);
    }

    fn iterate_and_compare(dict: &ChoiceDict, vec: &[Word], c: Color) {
        let mut it = if c == 0 { dict.iter0() } else { dict.iter1() };

        let mut dict_indices: HashSet<usize> = HashSet::new();
        let mut b_prev = it.b;
        while let Some(idx) = it.next() {
            dict_indices.insert(idx);
            assert!(
                it.b - b_prev <= 2,
                "call to next() skipped more than one block, this should never happen"
            );
            b_prev = it.b;
        }

        let mut vec_indices = HashSet::new();
        for (i, v) in vec.iter().enumerate() {
            if *v == c as Word {
                vec_indices.insert(i);
            }
        }

        let mut vec_indices_list = vec_indices.iter().collect::<Vec<_>>();
        let mut dict_indices_list = dict_indices.iter().collect::<Vec<_>>();
        vec_indices_list.sort();
        dict_indices_list.sort();
        assert_eq!(dict_indices_list, vec_indices_list);
    }

    pub fn dict_to_vec(dict: &ChoiceDict) -> Vec<Word> {
        let mut vec = vec![0; dict.size];

        for (i, v) in vec.iter_mut().enumerate() {
            *v = dict.get(i);
        }

        vec
    }
}
