type Word = u8;
type BlockIdx = usize;
type WordIdx = usize;
type Color = usize;

pub struct ChoiceDict {
    a: Vec<Word>,
    bar0: BlockIdx,
    bar1: BlockIdx,
    size: usize,
}

impl ChoiceDict {
    pub fn new(size: usize) -> Self {
        let num_words = size.div_ceil(Word::BITS as usize);

        assert!(num_words % Self::block_size() == 0);

        let num_blocks = num_words / Self::block_size();

        Self {
            a: vec![0; num_words],
            bar0: num_blocks,
            bar1: 0,
            size,
        }
    }

    pub fn from_vec(vec: Vec<Word>) -> Self {
        let num_words = vec.len();

        assert!(num_words % Self::block_size() == 0);

        let num_blocks = num_words / Self::block_size();
        let size = vec.len() * Word::BITS as usize;

        Self {
            a: vec,
            bar0: num_blocks,
            bar1: 0,
            size,
        }
    }

    pub fn to_vec(&self) -> Vec<Word> {
        let mut vec = vec![0; self.size];

        for (i, v) in vec.iter_mut().enumerate() {
            *v = self.read(i);
        }

        vec
    }

    pub fn reset(&mut self) {
        self.bar0 = self.a.len() / Self::block_size();
        self.bar1 = 0;
    }

    pub fn read(&self, idx: usize) -> Word {
        let wi = Self::elem_idx_to_word_idx(idx);
        let wrd = self.read_word(wi);
        let offset = idx % Word::BITS as usize;

        Self::get_bit(wrd, offset)
    }

    pub fn set(&mut self, idx: usize) {
        self.write(idx, 1)
    }

    pub fn remove(&mut self, idx: usize) {
        self.write(idx, 0)
    }

    fn read_word(&self, w: WordIdx) -> Word {
        let bi = Self::word_idx_to_block_idx(w);
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
                                if w % Self::block_size() == 1 {
                                    let wj = Self::block_idx_to_word_idx(bj);
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
                    if w % Self::block_size() == 0 {
                        let wj = Self::block_idx_to_word_idx(bj);
                        return self.a[wj + 2];
                    }

                    self.a[w]
                }
            }
        }
    }

    fn write(&mut self, idx: usize, c: Color) {
        if idx >= self.size {
            panic!("index out of bounds");
        }

        if self.read(idx) == c as Word {
            return;
        }

        let w = Self::elem_idx_to_word_idx(idx);
        let b = Self::word_idx_to_block_idx(w);
        let block_type = Self::block_type(self, b);
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
        let w = Self::block_idx_to_word_idx(b);
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
        if wi % Self::block_size() == chain {
            let wj = Self::block_idx_to_word_idx(bj);
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
            let wk = Self::block_idx_to_word_idx(bj);
            self.a[wk + c] = 0;
        }
    }

    fn chain(&mut self, bl: BlockIdx, br: BlockIdx, c: Color) {
        let wl = Self::block_idx_to_word_idx(bl);
        let wr = Self::block_idx_to_word_idx(br);
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
                    let wi = Self::block_idx_to_word_idx(bi);
                    let wj = Self::block_idx_to_word_idx(bj);
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
                        self.print_blocks();
                        self.chain(b_dash, b_star, c);
                        self.print_blocks();
                    }
                    Some(b_double_dash) => {
                        self.unchain(&self.block_type(b_star), c);
                        self.print_blocks();
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
            w: Self::block_idx_to_word_idx(b),
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
        let w = Self::block_idx_to_word_idx(b);
        let bj = self.a[w + c] as usize;

        if bj == 0 || bj > self.max_block() {
            return None;
        }

        let wk = Self::block_idx_to_word_idx(bj);

        let bar = if c == 0 { self.bar0 } else { self.bar1 };

        if ((b <= bar && bar < bj) || (bj <= bar && bar < b)) && self.a[wk + c] == b as Word {
            return Some(bj);
        }

        None
    }

    fn print_blocks(&self) {
        for b in 1..(self.max_block() + 1) {
            if self.bar0 == b - 1 {
                print!("|0|")
            }
            if self.bar1 == b - 1 {
                print!("|1|")
            }
            let w = Self::block_idx_to_word_idx(b);
            print!("{:?}", [self.a[w], self.a[w + 1], self.a[w + 2]]);
        }
        if self.bar0 == self.max_block() {
            print!("b0")
        }
        if self.bar1 == self.max_block() {
            print!("b1")
        }
        println!()
    }

    fn block_size() -> usize {
        3
    }

    fn max_block(&self) -> usize {
        self.a.len() / Self::block_size()
    }

    fn get_bit(word: Word, idx: usize) -> Word {
        Word::from(word & (1 << idx) != 0)
    }

    fn elem_idx_to_word_idx(idx: usize) -> WordIdx {
        idx / Word::BITS as usize
    }

    fn word_idx_to_block_idx(w: WordIdx) -> BlockIdx {
        w / Self::block_size() + 1
    }

    fn block_idx_to_word_idx(b: BlockIdx) -> WordIdx {
        b * Self::block_size() - Self::block_size()
    }
}

struct BlockType {
    b: BlockIdx,
    w: WordIdx,
    is_left: [bool; 2],
    chained_to: [Option<usize>; 2],
}

#[cfg(test)]
mod tests {
    use rand::{rngs::StdRng, seq::SliceRandom, Rng, SeedableRng};

    use super::{ChoiceDict, Word};

    #[test]
    fn set_and_remove() {
        let size = 10 * 3 * Word::BITS as usize;
        let mut dict = ChoiceDict::new(size);
        let mut vec = vec![0; size];
        let indices = [1, 12, 4, 33, 9, 10, 23, 2, 17, 8, 7, 6, 5, 4];

        for i in indices {
            set_and_compare(&mut dict, &mut vec, i);
        }

        for i in indices {
            remove_and_compare(&mut dict, &mut vec, i);
        }
    }

    #[test]
    fn connect_and_disconnect() {
        let num_blocks = 2;
        let size = num_blocks * 3 * Word::BITS as usize;
        let mut dict = ChoiceDict::new(size);

        assert_eq!(dict.bar0, num_blocks);
        assert_eq!(dict.bar1, 0);

        for i in 0..24 {
            dict.set(i);
        }

        assert_eq!(dict.bar0, num_blocks - 1);
        assert_eq!(dict.bar1, 1);

        for i in 0..24 {
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

        for _ in 0..1000 {
            let mut dict = ChoiceDict::new(size);
            let mut vec = vec![0; size];
            let mut blocks = blocks.clone();
            blocks.shuffle(&mut rng);

            for b in blocks {
                let idx = b * 3 * Word::BITS as usize;

                if rng.gen_bool(1.) {
                    set_and_compare(&mut dict, &mut vec, idx);
                } else {
                    //remove_and_compare(&mut dict, &mut vec, idx);
                }
            }
        }
    }

    #[test]
    fn set_and_remove_randomly() {
        let seed = [0; 32];
        let mut rng = StdRng::from_seed(seed);

        for num_blocks in 2..17 {
            for _ in 0..200 {
                let blocks = 0..num_blocks;
                let size = blocks.len() * 3 * Word::BITS as usize;
                let mut dict = ChoiceDict::from_vec(
                    (0..(blocks.len() * 3))
                        .map(|_| rng.gen_range(0..Word::MAX))
                        .collect(),
                );
                let mut vec = vec![0; size];

                for _ in 0..(size * 5) {
                    let idx = rng.gen_range(0..size);

                    if rng.gen_bool(0.5) {
                        set_and_compare(&mut dict, &mut vec, idx);
                    } else {
                        remove_and_compare(&mut dict, &mut vec, idx);
                    }
                }
            }
        }
    }

    #[test]
    fn reset() {
        let mut dict = ChoiceDict::from_vec(vec![2, 4, 4, 1, 1, 6, 4, 120, 77, 3, 1, 123]);
        let mut vec = vec![0; 4 * 3 * Word::BITS as usize];

        reset_and_compare(&mut dict, &mut vec);
    }

    fn set_and_compare(dict: &mut ChoiceDict, vec: &mut Vec<Word>, idx: usize) {
        dict.set(idx);
        vec[idx] = 1;
        assert_eq!(dict.to_vec(), *vec);
    }

    fn remove_and_compare(dict: &mut ChoiceDict, vec: &mut Vec<Word>, idx: usize) {
        dict.remove(idx);
        vec[idx] = 0;

        assert_eq!(dict.to_vec(), *vec);
    }

    fn reset_and_compare(dict: &mut ChoiceDict, vec: &mut Vec<Word>) {
        dict.reset();
        for v in vec.iter_mut() {
            *v = 0;
        }

        assert_eq!(dict.to_vec(), *vec);
    }
}
