type Word = u8;

pub struct ChoiceDict {
    a: Vec<Word>,
    b1: usize,
    size: usize,
}

impl ChoiceDict {
    pub fn new(size: usize) -> Self {
        Self {
            a: vec![0; size.div_ceil(Word::BITS as usize)],
            b1: 0,
            size,
        }
    }

    pub fn from_vec(vec: Vec<Word>) -> Self {
        assert!(vec.len() % Self::block_size() == 0);

        let size = vec.len() * Word::BITS as usize;

        Self {
            a: vec,
            b1: 0,
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
        self.b1 = 0;
    }

    pub fn read(&self, i: usize) -> Word {
        let wi = Self::idx_to_wrd(i);
        let bi = Self::wrd_to_blk(wi);

        if bi <= self.b1 {
            match self.chained_to(bi) {
                None => Self::get_bit(self.a[wi], i % Word::BITS as usize),
                Some(_) => 0,
            }
        } else {
            match self.chained_to(bi) {
                None => 0,
                Some(bj) => {
                    if wi % 2 == 0 {
                        let wk = Self::blk_to_wrd(bj);
                        return Self::get_bit(self.a[wk + 1], i % Word::BITS as usize);
                    }
                    {
                        Self::get_bit(self.a[wi], i % Word::BITS as usize)
                    }
                }
            }
        }
    }

    pub fn set(&mut self, idx: usize) {
        self.write(idx, true)
    }

    pub fn remove(&mut self, idx: usize) {
        self.write(idx, false)
    }

    fn write(&mut self, idx: usize, val: bool) {
        if idx >= self.size {
            panic!("index out of bounds");
        }

        let wi = Self::idx_to_wrd(idx);
        let bi = Self::wrd_to_blk(wi);

        if bi <= self.b1 {
            match self.chained_to(bi) {
                None => {
                    self.write_and_break(idx, wi, bi, val);
                }
                Some(_) => {
                    self.connect(bi);
                    self.write_and_break(idx, wi, bi, val);
                }
            }
        } else {
            match self.chained_to(bi) {
                Some(bj) => self.write_chained(idx, wi, bj, val),
                None => {
                    self.connect(bi);

                    // connect caused bi to move to the left area
                    if bi == self.b1 {
                        self.write_and_break(idx, wi, bi, val);
                        return;
                    }

                    // bi is connected and in the right area, so it must have a chain
                    let bj = self.chained_to(bi).unwrap();
                    self.write_chained(idx, wi, bj, val)
                }
            }
        }
    }

    fn write_and_break(&mut self, i: usize, wi: usize, bi: usize, one: bool) {
        self.write_bit(wi, i, one);
        self.break_chain(bi);
    }

    fn write_chained(&mut self, i: usize, wi: usize, bj: usize, one: bool) {
        if wi % 2 == 0 {
            let wj = Self::blk_to_wrd(bj);
            self.write_bit(wj + 1, i, one);
        } else {
            self.write_bit(wi, i, one);
        }
    }

    fn write_bit(&mut self, wi: usize, i: usize, val: bool) {
        if val {
            self.a[wi] |= 1 << (i % Word::BITS as usize)
        } else {
            self.a[wi] &= !(1 << (i % Word::BITS as usize))
        }
    }

    fn break_chain(&mut self, bi: usize) {
        if let Some(bk) = self.chained_to(bi) {
            let wk = Self::blk_to_wrd(bk);
            self.a[wk] = 0;
        }
    }

    fn chain(&mut self, bl: usize, br: usize) {
        let wl = Self::blk_to_wrd(bl);
        let wr = Self::blk_to_wrd(br);
        self.a[wl + 1] = self.a[wr];
        self.a[wl] = br as Word;
        self.a[wr] = bl as Word;
    }

    fn unchain(&mut self, bi: usize) -> usize {
        let bj = self.chained_to(bi);

        match bj {
            None => {
                self.init_block(bi);
                bi
            }
            Some(bj) => {
                if bi <= self.b1 {
                    let wi = Self::blk_to_wrd(bi);
                    let wj = Self::blk_to_wrd(bj);
                    self.a[wj] = self.a[wi + 1];
                    self.init_block(bi);
                    bj
                } else {
                    self.unchain(bj)
                }
            }
        }
    }

    fn connect(&mut self, b: usize) {
        assert!(!self.is_connected(b));

        let b_star = self.b1 + 1;
        let mut break_chain = false;

        if b > self.b1 {
            self.init_block(b);

            if b != b_star {
                match self.chained_to(b_star) {
                    None => {
                        self.init_block(b_star);
                        self.chain(b_star, b);
                    }
                    Some(b_double_dash) => {
                        self.unchain(b_star);
                        self.chain(b_double_dash, b);
                        break_chain = true;
                    }
                }
            }
        } else {
            let b_dash = self.unchain(b);

            if b_dash != b_star {
                match self.chained_to(b_star) {
                    None => {
                        self.init_block(b_star);
                        self.chain(b_star, b_dash);
                    }
                    Some(b_double_dash) => {
                        self.unchain(b_star);
                        self.chain(b_double_dash, b_dash);
                        break_chain = true;
                    }
                }
            } else {
                break_chain = true;
            }
        }

        self.b1 += 1;
        if break_chain {
            self.break_chain(b_star);
        }
    }

    fn is_connected(&self, bi: usize) -> bool {
        let is_left_unchained = bi <= self.b1 && self.chained_to(bi).is_none();
        let is_right_chained = bi > self.b1 && self.chained_to(bi).is_some();
        is_left_unchained || is_right_chained
    }

    fn init_block(&mut self, bi: usize) {
        let wi = Self::blk_to_wrd(bi);
        self.a[wi] = 0;
        self.a[wi + 1] = 0;
    }

    fn chained_to(&self, bi: usize) -> Option<usize> {
        let wi = Self::blk_to_wrd(bi);
        let bk = self.a[wi] as usize;

        if bk == 0 || bk > self.max_block() {
            return None;
        }

        let wk = Self::blk_to_wrd(bk);

        if ((bi <= self.b1 && self.b1 < bk) || (bk <= self.b1 && self.b1 < bi))
            && self.a[wi] == bk as Word
            && self.a[wk] == bi as Word
        {
            return Some(bk);
        }

        None
    }

    fn block_size() -> usize {
        2
    }

    fn max_block(&self) -> usize {
        self.a.len() / 2
    }

    fn get_bit(v: Word, i: usize) -> Word {
        Word::from(v & (1 << i) != 0)
    }

    fn idx_to_wrd(i: usize) -> usize {
        i / Word::BITS as usize
    }

    fn wrd_to_blk(i: usize) -> usize {
        i / Self::block_size() + 1
    }

    fn blk_to_wrd(b: usize) -> usize {
        //   assert!(b > 0);
        b * Self::block_size() - Self::block_size()
    }
}

#[cfg(test)]
mod tests {
    use rand::{rngs::StdRng, seq::SliceRandom, Rng, SeedableRng};

    use super::{ChoiceDict, Word};

    #[test]
    fn test() {
        let blocks: Vec<usize> = (0..16).collect();
        let size = blocks.len() * 2 * Word::BITS as usize;
        let seed = [0; 32];
        let mut rng = StdRng::from_seed(seed);

        for _ in 0..1000 {
            let mut dict = ChoiceDict::new(size);
            let mut vec = vec![0; size];
            let mut blocks = blocks.clone();
            blocks.shuffle(&mut rng);

            for b in blocks {
                let idx = b * 2 * Word::BITS as usize;

                if rng.gen_bool(0.5) {
                    set_and_compare(&mut dict, &mut vec, idx);
                } else {
                    remove_and_compare(&mut dict, &mut vec, idx);
                }
            }
        }
    }

    #[test]
    fn random() {
        let seed = [0; 32];
        let mut rng = StdRng::from_seed(seed);

        for _ in 0..10000 {
            let blocks = 0..(rng.gen_range(2..16));
            let size = blocks.len() * 2 * Word::BITS as usize;
            let mut dict = ChoiceDict::from_vec(
                (0..(blocks.len() * 2))
                    .map(|_| rng.gen_range(0..Word::MAX))
                    .collect(),
            );
            let mut vec = vec![0; size];

            println!("NEW");

            for _ in 0..(size * 3) {
                let idx = rng.gen_range(0..size);
                println!("{idx}");

                if rng.gen_bool(1.) {
                    set_and_compare(&mut dict, &mut vec, idx);
                } else {
                    remove_and_compare(&mut dict, &mut vec, idx);
                }

                if rng.gen_bool(0.2) {
                    println!("a: {:?} b1: {}", dict.a, dict.b1);
                    println!("RESET");
                    reset_and_compare(&mut dict, &mut vec);
                }
            }
        }
    }

    #[test]
    fn reset() {
        let mut dict = ChoiceDict::from_vec(vec![32, 4, 4, 0, 1, 6, 2, 64]);
        let mut vec = vec![0; 8 * Word::BITS as usize];

        println!("a: {:?}, b1: {}", dict.a, dict.b1);
        reset_and_compare(&mut dict, &mut vec);
        println!("a: {:?}, b1: {}", dict.a, dict.b1);
        set_and_compare(&mut dict, &mut vec, 18);
        println!("a: {:?}, b1: {}", dict.a, dict.b1);
        set_and_compare(&mut dict, &mut vec, 0);
    }

    fn set_and_compare(dict: &mut ChoiceDict, vec: &mut Vec<u8>, idx: usize) {
        dict.set(idx);
        vec[idx] = 1;
        println!("a: {:?}, b1: {}", dict.a, dict.b1);
        assert_eq!(dict.to_vec(), *vec);
    }

    fn remove_and_compare(dict: &mut ChoiceDict, vec: &mut Vec<u8>, idx: usize) {
        dict.remove(idx);
        vec[idx] = 0;

        assert_eq!(dict.to_vec(), *vec);
    }

    fn reset_and_compare(dict: &mut ChoiceDict, vec: &mut Vec<u8>) {
        dict.reset();
        for v in vec.iter_mut() {
            *v = 0;
        }

        assert_eq!(dict.to_vec(), *vec);
    }
}
