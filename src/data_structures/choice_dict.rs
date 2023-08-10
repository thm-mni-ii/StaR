use std::fmt;

type Word = u32;
type BlockIdx = usize;
type WordIdx = usize;
type Color = usize;

#[derive(PartialEq, Clone)]
/// A 2-color choice dictionary based on the ideas presented in <https://drops.dagstuhl.de/opus/volltexte/2018/10014/pdf/LIPIcs-ISAAC-2018-66.pdf>
/// (DOI: 10.4230/LIPIcs.ISAAC.2018.66).
///
/// Each element of the choice dictionary either has color 0 or color 1. Storing a choice dictionary with n elements requires n + O(1) bits.
pub struct ChoiceDict {
    a: Vec<Word>,
    bar0: BlockIdx,
    bar1: BlockIdx,
    size: usize,
}

impl ChoiceDict {
    /// Return a choice dictionary with `size` elements.
    ///
    /// Initially, all elements have the color 0.
    ///
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choice_dict::ChoiceDict;
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

        Self {
            a: vec![0; num_words_padded],
            bar0: num_blocks,
            bar1: 0,
            size,
        }
    }

    /// Return an iterator for iterating over all elements of color 0.
    ///
    /// Time complexity per `next()` call: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choice_dict::ChoiceDict;
    ///
    /// let dict = ChoiceDict::new(1000);
    /// let mut it = dict.iter_0();
    /// let elem = it.next();
    /// assert_eq!(elem, Some(0));
    /// ```
    pub fn iter_0(&self) -> ChoiceDictIterator {
        return ChoiceDictIterator::new(self, 0);
    }

    /// Return an iterator for iterating over all elements of color 1.
    ///
    /// Time complexity per `next()` call: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choice_dict::ChoiceDict;
    ///
    /// let mut dict = ChoiceDict::new(1000);
    /// dict.set(17);
    /// let mut it = dict.iter_1();
    /// let elem = it.next();
    /// assert_eq!(elem, Some(17));
    /// ```
    pub fn iter_1(&self) -> ChoiceDictIterator {
        return ChoiceDictIterator::new(self, 1);
    }

    /// Return an arbitrary element of color 0 (if present).
    ///
    /// Time complexity: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choice_dict::ChoiceDict;
    ///
    /// let dict = ChoiceDict::new(1000);
    /// let elem = dict.choice_0();
    /// assert!(elem.is_some());
    /// ```
    pub fn choice_0(&self) -> Option<usize> {
        self.iter_0().next()
    }

    /// Return an arbitrary element of color 1 (if present).
    ///
    /// Time complexity: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choice_dict::ChoiceDict;
    ///
    /// let mut dict = ChoiceDict::new(1000);
    /// dict.set(100);
    /// let elem = dict.choice_1();
    /// assert!(elem.is_some());
    /// ```
    pub fn choice_1(&self) -> Option<usize> {
        self.iter_1().next()
    }

    /// Set the color of all elements to 0.
    ///
    /// Time complexity: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choice_dict::ChoiceDict;
    ///
    /// let mut dict = ChoiceDict::new(1000);
    /// dict.set(100);
    /// dict.set(263);
    /// dict.set(827);
    /// dict.reset();
    /// assert!(dict.choice_1().is_none());
    /// ```
    pub fn reset(&mut self) {
        self.bar0 = self.max_block();
        self.bar1 = 0;
    }

    /// Retrieve the color of the element at the given index.
    ///
    /// Time complexity: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choice_dict::ChoiceDict;
    ///
    /// let mut dict = ChoiceDict::new(1000);
    /// dict.set(532);
    /// let elem = dict.get(532);
    /// assert_eq!(elem, 1);
    /// ```
    pub fn get(&self, idx: usize) -> Word {
        self.check_bounds(idx);

        let wi = elem_idx_to_word_idx(idx);
        let wrd = self.read_word(wi);
        let offset = idx % Word::BITS as usize;

        get_bit(wrd, offset)
    }

    /// Set the color of the element at the given index to 1.
    ///
    /// Time complexity: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choice_dict::ChoiceDict;
    ///
    /// let mut dict = ChoiceDict::new(1000);
    /// dict.set(692);
    /// assert_eq!(dict.get(692), 1);
    /// ```
    pub fn set(&mut self, idx: usize) {
        self.write(idx, 1)
    }

    /// Set the color of the element at the given index to 0.
    ///
    /// Time complexity: O(1)
    ///
    /// # Example
    ///
    /// ```
    /// use star::data_structures::choice_dict::ChoiceDict;
    ///
    /// let mut dict = ChoiceDict::new(1000);
    /// dict.set(302);
    /// dict.remove(302);
    /// assert_eq!(dict.get(302), 0);
    /// ```
    pub fn remove(&mut self, idx: usize) {
        self.write(idx, 0)
    }

    fn read_word(&self, w: WordIdx) -> Word {
        let bi = word_idx_to_block_idx(w);
        let block_type_i = self.block_type(bi);

        if block_type_i.is_left[0] {
            match block_type_i.chained_to[0] {
                None => {
                    if block_type_i.is_left[1] {
                        match block_type_i.chained_to[1] {
                            None => self.a[w],
                            Some(_) => 0,
                        }
                    } else {
                        match block_type_i.chained_to[1] {
                            None => 0,
                            Some(bj) => {
                                if w % block_size() == 1 {
                                    let wj = block_idx_to_word_idx(bj);
                                    return self.a[wj + 2];
                                }

                                self.a[w]
                            }
                        }
                    }
                }
                Some(_) => Word::MAX,
            }
        } else {
            match block_type_i.chained_to[0] {
                None => Word::MAX,
                Some(bj) => {
                    if w % block_size() == 0 {
                        let wj = block_idx_to_word_idx(bj);
                        return self.a[wj + 2];
                    }

                    self.a[w]
                }
            }
        }
    }

    fn write(&mut self, idx: usize, c: Color) {
        self.check_bounds(idx);

        if self.get(idx) == c as Word {
            return;
        }

        let w = elem_idx_to_word_idx(idx);
        let b = word_idx_to_block_idx(w);
        let block_type = self.block_type(b);
        self.connect_and_write(idx, w, &block_type, c);
    }

    fn connect_and_write(&mut self, idx: usize, w: WordIdx, block_type: &BlockType, c: Color) {
        let b = block_type.b;

        if block_type.is_left[c] {
            match block_type.chained_to[c] {
                Some(_) => {
                    self.connect(block_type, c);
                    self.write_and_break(idx, w, block_type, c);
                }
                None => {
                    self.write_and_break(idx, w, block_type, c);
                }
            }
        } else {
            match block_type.chained_to[c] {
                Some(bj) => {
                    self.write_chained(idx, w, block_type, bj, 1, c);
                }
                None => {
                    self.connect(block_type, c);

                    // connect caused bi to move to the left area
                    if b == self.get_barrier(c) {
                        self.write_and_break(idx, w, block_type, c);
                        return;
                    }

                    // bi is connected and in the right area, so it must have a chain
                    let bj = self.chained_to(b, c).unwrap();
                    self.write_chained(idx, w, block_type, bj, 1, c);
                }
            }
        }
    }

    fn is_full_block(&self, b: usize, c: Color) -> bool {
        let w = block_idx_to_word_idx(b);
        let val = if c == 0 { 0 } else { Word::MAX };
        self.read_word(w) == val && self.read_word(w + 1) == val && self.read_word(w + 2) == val
    }

    fn write_and_break(&mut self, idx: usize, w: WordIdx, block_type: &BlockType, c: Color) {
        let bi = block_type.b;

        if !block_type.is_left[1 - c] {
            if let Some(bj) = block_type.chained_to[1 - c] {
                self.write_chained(idx, w, block_type, bj, 1 - c, c);
                return;
            }
        }

        self.write_bit(w, idx, c);
        self.break_chain(bi, c);
        self.disconnect_if_full(block_type, c);
    }

    fn write_chained(
        &mut self,
        idx: usize,
        wi: WordIdx,
        block_type: &BlockType,
        bj: BlockIdx,
        chain: Color,
        c: Color,
    ) {
        if wi % block_size() == chain {
            let wj = block_idx_to_word_idx(bj);
            self.write_bit(wj + 2, idx, c);
        } else {
            self.write_bit(wi, idx, c);
        }

        self.disconnect_if_full(block_type, c);
    }

    fn disconnect_if_full(&mut self, block_type: &BlockType, c: usize) {
        let b = block_type.b;

        if c == 1 && self.is_full_block(b, 1) {
            self.disconnect(block_type, 0);
        }

        if c == 0 && self.is_full_block(b, 0) {
            self.disconnect(block_type, 1);
        }
    }

    fn write_bit(&mut self, w: WordIdx, idx: usize, c: Color) {
        assert!(c == 0 || c == 1);

        if c == 1 {
            self.a[w] |= 1 << (idx % Word::BITS as usize)
        } else {
            self.a[w] &= !(1 << (idx % Word::BITS as usize))
        }
    }

    fn break_chain(&mut self, b: BlockIdx, c: Color) {
        if let Some(bj) = self.chained_to(b, c) {
            let wk = block_idx_to_word_idx(bj);
            self.a[wk + c] = 0;
        }
    }

    fn chain(&mut self, bl: BlockIdx, br: BlockIdx, c: Color) {
        let wl = block_idx_to_word_idx(bl);
        let wr = block_idx_to_word_idx(br);
        self.a[wl + 2] = self.a[wr + c];
        self.a[wl + c] = br as Word;
        self.a[wr + c] = bl as Word;
    }

    fn unchain(&mut self, block_type: &BlockType, c: Color) -> (BlockIdx, BlockIdx) {
        let bi = block_type.b;
        let bj = self.chained_to(bi, c);
        let bar = self.get_barrier(c);

        match bj {
            None => {
                self.init_block(block_type, c);
                if bi <= bar {
                    (bi, 0)
                } else {
                    (0, bi)
                }
            }
            Some(bj) => {
                if bi <= bar {
                    let wi = block_idx_to_word_idx(bi);
                    let wj = block_idx_to_word_idx(bj);
                    self.a[wj + c] = self.a[wi + 2];
                    self.init_block(block_type, c);

                    (bi, bj)
                } else {
                    self.unchain(&self.block_type(bj), c)
                }
            }
        }
    }

    fn get_barrier(&self, c: Color) -> usize {
        if c == 0 {
            self.bar0
        } else {
            self.bar1
        }
    }

    fn set_barrier(&mut self, c: Color, bar: BlockIdx) {
        if c == 0 {
            self.bar0 = bar
        } else {
            self.bar1 = bar
        }
    }

    fn disconnect(&mut self, block_type: &BlockType, c: Color) {
        assert!(self.is_connected(block_type, c));

        let b = block_type.b;
        let bar = self.get_barrier(c);
        let b_star = bar;
        let mut break_chain = false;

        if b > bar {
            let (b_dash, _) = self.unchain(block_type, c);

            if b_dash != b_star {
                match self.chained_to(b_star, c) {
                    None => {
                        self.chain(b_dash, b_star, c);
                    }
                    Some(b_double_dash) => {
                        self.unchain(&self.block_type(b_star), c);
                        self.chain(b_dash, b_double_dash, c);
                        break_chain = true;
                    }
                }
            } else {
                break_chain = true;
            }
        } else if b != b_star {
            match self.chained_to(b_star, c) {
                None => {
                    self.chain(b, b_star, c);
                }
                Some(b_double_dash) => {
                    self.unchain(&self.block_type(b_star), c);
                    self.chain(b, b_double_dash, c);
                    break_chain = true;
                }
            }
        }

        self.set_barrier(c, bar - 1);
        if break_chain {
            self.break_chain(b_star, c);
        }
    }

    fn connect(&mut self, block_type: &BlockType, c: Color) {
        assert!(!self.is_connected(block_type, c));

        let b = block_type.b;
        let bar = self.get_barrier(c);
        let b_star = bar + 1;
        let mut break_chain = false;

        if b > bar {
            self.init_block(block_type, c);

            if b != b_star {
                match self.chained_to(b_star, c) {
                    None => {
                        self.init_block(&self.block_type(b_star), c);
                        self.chain(b_star, b, c);
                    }
                    Some(b_double_dash) => {
                        self.unchain(&self.block_type(b_star), c);
                        self.chain(b_double_dash, b, c);
                        break_chain = true;
                    }
                }
            }
        } else {
            let (_, b_dash) = self.unchain(block_type, c);

            if b_dash != b_star {
                match self.chained_to(b_star, c) {
                    None => {
                        self.init_block(&self.block_type(b_star), c);
                        self.chain(b_star, b_dash, c);
                    }
                    Some(b_double_dash) => {
                        self.unchain(&self.block_type(b_star), c);
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

    fn block_type(&self, b: BlockIdx) -> BlockType {
        BlockType {
            b,
            w: block_idx_to_word_idx(b),
            is_left: [b <= self.bar0, b <= self.bar1],
            chained_to: [self.chained_to(b, 0), self.chained_to(b, 1)],
        }
    }

    fn is_connected(&self, block_type: &BlockType, c: Color) -> bool {
        if c == 0 {
            if block_type.is_left[0] {
                return block_type.chained_to[0].is_none();
            } else {
                return block_type.chained_to[0].is_some();
            }
        }

        if c == 1 {
            if block_type.is_left[1] {
                return block_type.chained_to[1].is_none();
            } else {
                return block_type.chained_to[1].is_some();
            }
        }

        false
    }

    fn init_block(&mut self, block_type: &BlockType, c: Color) {
        let w = block_type.w;
        let val = if c == 1 { 0 } else { Word::MAX };

        if c == 0 || block_type.chained_to[0].is_none() {
            self.a[w] = val;
        }
        if c == 1 || block_type.chained_to[1].is_none() {
            self.a[w + 1] = val;
        }
        self.a[w + 2] = val;
    }

    fn chained_to(&self, b: BlockIdx, c: Color) -> Option<usize> {
        let w = block_idx_to_word_idx(b);
        let bj = self.a[w + c] as usize;

        if bj == 0 || bj > self.max_block() {
            return None;
        }

        let wk = block_idx_to_word_idx(bj);

        let bar = if c == 0 { self.bar0 } else { self.bar1 };

        if ((b <= bar && bar < bj) || (bj <= bar && bar < b)) && self.a[wk + c] == b as Word {
            return Some(bj);
        }

        None
    }

    fn max_block(&self) -> usize {
        self.a.len() / block_size()
    }

    fn check_bounds(&self, idx: usize) {
        if idx >= self.size {
            panic!("index out of bounds");
        }
    }
}

impl fmt::Debug for ChoiceDict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in 1..(self.max_block() + 1) {
            if self.bar0 == b - 1 {
                write!(f, "|0|")?;
            }
            if self.bar1 == b - 1 {
                write!(f, "|1|")?;
            }
            let w = block_idx_to_word_idx(b);
            write!(f, "{:?}", [self.a[w], self.a[w + 1], self.a[w + 2]])?;
        }
        if self.bar0 == self.max_block() {
            write!(f, "b0")?;
        }
        if self.bar1 == self.max_block() {
            write!(f, "b1")?;
        }

        writeln!(f)
    }
}

/// An iterator for iterating over the elements of a specific color in a choice dictionary.
pub struct ChoiceDictIterator<'a> {
    dict: &'a ChoiceDict,
    word: Word,
    c: Color,
    b: BlockIdx,
    w: WordIdx,
    i: usize,
    j: usize,
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
        };
        it.next_block();

        it
    }

    fn next_block(&mut self) {
        self.b += 1;

        if self.b > self.dict.get_barrier(self.c) {
            return;
        }

        let w = match self.dict.chained_to(self.b, self.c) {
            Some(bj) => block_idx_to_word_idx(bj),
            None => block_idx_to_word_idx(self.b),
        };

        self.i = 0;
        self.w = w;
        self.word = self.dict.read_word(w);
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
                let w = self.w + self.i;
                let word = self.dict.read_word(w);

                while self.j < Word::BITS as usize {
                    let j = self.j;
                    self.j += 1;
                    let idx = w * Word::BITS as usize + j;

                    if idx < self.dict.size && get_bit(word, j) as usize == self.c {
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

struct BlockType {
    b: BlockIdx,
    w: WordIdx,
    is_left: [bool; 2],
    chained_to: [Option<usize>; 2],
}

fn block_size() -> usize {
    3
}

fn get_bit(word: Word, idx: usize) -> Word {
    Word::from(word & (1 << idx) != 0)
}

fn elem_idx_to_word_idx(idx: usize) -> WordIdx {
    idx / Word::BITS as usize
}

fn word_idx_to_block_idx(w: WordIdx) -> BlockIdx {
    w / block_size() + 1
}

fn block_idx_to_word_idx(b: BlockIdx) -> WordIdx {
    b * block_size() - block_size()
}

#[cfg(test)]
mod tests {
    use super::{ChoiceDict, Color, Word};
    use rand::{rngs::StdRng, seq::SliceRandom, Rng, SeedableRng};
    use std::collections::HashSet;

    #[test]
    fn various_sizes() {
        let count = if cfg!(miri) { 20 } else { 300 };

        for size in 1..count {
            let mut dict = ChoiceDict::new(size);
            let mut vec = vec![0; size];

            for i in 0..size {
                write_and_compare(&mut dict, &mut vec, i, 1);
            }
        }
    }

    #[test]
    fn set_and_remove() {
        let size = 10 * 3 * Word::BITS as usize;
        let mut dict = ChoiceDict::new(size);
        let mut vec = vec![0; size];
        let indices = [1, 12, 4, 33, 9, 10, 23, 2, 17, 8, 7, 6, 5, 4];

        for i in indices {
            write_and_compare(&mut dict, &mut vec, i, 1);
        }

        for i in indices {
            write_and_compare(&mut dict, &mut vec, i, 0);
        }
    }

    #[test]
    fn connect_and_disconnect() {
        let num_blocks = 2;
        let size = num_blocks * 3 * Word::BITS as usize;
        let mut dict = ChoiceDict::new(size);

        assert_eq!(dict.bar0, num_blocks);
        assert_eq!(dict.bar1, 0);

        for i in 0..(3 * Word::BITS as usize) {
            dict.set(i);
        }

        assert_eq!(dict.bar0, num_blocks - 1);
        assert_eq!(dict.bar1, 1);

        for i in 0..(3 * Word::BITS as usize) {
            dict.remove(i);
        }

        assert_eq!(dict.bar0, num_blocks);
        assert_eq!(dict.bar1, 0);
    }

    #[test]
    fn set_one_elem_per_block() {
        let blocks: Vec<usize> = (0..16).collect();
        let size = blocks.len() * 3 * Word::BITS as usize;
        let seed = [0; 32];
        let mut rng = StdRng::from_seed(seed);
        let count = if cfg!(miri) { 1 } else { 1000 };

        for _ in 0..count {
            let mut dict = ChoiceDict::new(size);
            let mut vec = vec![0; size];
            let mut blocks = blocks.clone();
            blocks.shuffle(&mut rng);

            for b in blocks {
                let idx = b * 3 * Word::BITS as usize;
                write_and_compare(&mut dict, &mut vec, idx, 1);
            }
        }
    }

    #[test]
    fn iterate() {
        let size = 5 * 3 * Word::BITS as usize;
        let mut dict = ChoiceDict::new(size);
        let mut vec = vec![0; size];
        let indices = if cfg!(miri) {
            vec![0, 20, 22]
        } else {
            vec![0, 20, 22, 7, 30, 81, 320, 133, size - 1]
        };

        for i in indices {
            write_and_compare(&mut dict, &mut vec, i, 1);
            iterate_and_compare(&dict, &vec, 1);
            iterate_and_compare(&dict, &vec, 0);
        }
    }

    #[test]
    fn choice() {
        let mut dict = ChoiceDict::new(100);

        assert!(dict.choice_1().is_none());
        dict.set(77);
        dict.set(20);
        assert!(dict.choice_1() == Some(20) || dict.choice_1() == Some(77));
        dict.remove(77);
        assert_eq!(dict.choice_1(), Some(20));

        for i in 0..100 {
            dict.set(i);
        }

        assert!(dict.choice_1().is_some());
        assert!(dict.choice_0().is_none());
    }

    #[test]
    fn random() {
        let seed = [0; 32];
        let mut rng = StdRng::from_seed(seed);
        let count = if cfg!(miri) { 3 } else { 50 };

        for _ in 0..count {
            let size = rng.gen_range(1..1000);
            let mut dict = ChoiceDict::new(size);
            let mut vec = vec![0; size];
            let inner_count = if cfg!(miri) { 3 } else { size * 3 };

            for _ in 0..inner_count {
                let idx = rng.gen_range(0..size);
                let c = rng.gen_bool(0.5) as Color;

                write_and_compare(&mut dict, &mut vec, idx, c);

                if rng.gen_bool(0.1) {
                    iterate_and_compare(&dict, &vec, rng.gen_bool(0.5) as usize)
                }

                if rng.gen_bool(0.1) {
                    reset_and_compare(&mut dict, &mut vec);
                }
            }
        }
    }

    fn write_and_compare(dict: &mut ChoiceDict, vec: &mut Vec<Word>, idx: usize, c: Color) {
        if c == 0 {
            dict.remove(idx);
        } else {
            dict.set(idx);
        }

        vec[idx] = c as Word;
        assert_eq!(dict_to_vec(dict), *vec);
    }

    fn reset_and_compare(dict: &mut ChoiceDict, vec: &mut Vec<Word>) {
        dict.reset();

        for v in vec.iter_mut() {
            *v = 0;
        }

        assert_eq!(dict_to_vec(dict), *vec);
    }

    fn iterate_and_compare(dict: &ChoiceDict, vec: &[Word], c: Color) {
        let it = if c == 0 { dict.iter_0() } else { dict.iter_1() };

        let dict_indices: HashSet<usize> = it.collect();
        let mut vec_indices = HashSet::new();

        for (i, v) in vec.iter().enumerate() {
            if *v == c as Word {
                vec_indices.insert(i);
            }
        }

        assert_eq!(dict_indices, vec_indices);
    }

    pub fn dict_to_vec(dict: &ChoiceDict) -> Vec<Word> {
        let mut vec = vec![0; dict.size];

        for (i, v) in vec.iter_mut().enumerate() {
            *v = dict.get(i);
        }

        vec
    }
}
