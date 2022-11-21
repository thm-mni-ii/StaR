use std::ops::Index;

pub struct InitArray {
    a: Vec<usize>,
    initv: usize,
    b: usize,
}

impl InitArray {
    pub fn new(initv: usize, size: usize) -> Self {
        InitArray {
            a: vec![initv; size],
            initv,
            b: 0,
        }
    }

    pub fn from_vec(initv: usize, vec: Vec<usize>) -> Self {
        let mut init_arr = InitArray {
            a: vec,
            initv,
            b: 0,
        };

        let len = init_arr.len();
        if len % 2 != 0 {
            init_arr.a[len - 1] = initv;
        }

        init_arr
    }

    pub fn len(&self) -> usize {
        self.a.len()
    }

    pub fn is_empty(&self) -> bool {
        self.a.is_empty()
    }

    pub fn init(&mut self, v: usize) {
        let len = self.len();
        if len % 2 != 0 {
            self.a[len - 1] = v;
        }

        self.initv = v;
        self.b = 0;
    }

    pub fn to_vec(&self) -> Vec<usize> {
        let mut vec = vec![0; self.a.len()];

        for (i, v) in vec.iter_mut().enumerate() {
            *v = *self.read_ref(i);
        }

        vec
    }

    pub fn read_ref(&self, i: usize) -> &usize {
        if self.len() % 2 != 0 && i == self.len() - 1 {
            return &self.a[i];
        }

        let bi = i / 2;
        let bk = self.chained_to(bi);

        if i < 2 * self.b {
            if bk.is_some() {
                &self.initv
            } else {
                &self.a[i]
            }
        } else if bk.is_some() {
            if i % 2 == 0 {
                &self.a[self.a[i] + 1]
            } else {
                &self.a[i]
            }
        } else {
            &self.initv
        }
    }

    pub fn write(&mut self, i: usize, v: usize) {
        if self.len() % 2 != 0 && i == self.len() - 1 {
            self.a[i] = v;
            return;
        }

        let bi = i / 2;
        let bk = self.chained_to(bi);

        if bi < self.b {
            match bk {
                None => {
                    self.write_and_break(i, v);
                }
                Some(bk) => {
                    let bj = self.extend();

                    if bi == bj {
                        self.write_and_break(i, v);
                    } else {
                        self.a[2 * bj + 1] = self.a[2 * bi + 1];
                        self.make_chain(bj, bk);
                        self.init_block(bi);
                        self.write_and_break(i, v);
                    }
                }
            }
        } else {
            match bk {
                Some(bk) => {
                    self.write_chained(i, v, bk);
                }
                None => {
                    let bk = self.extend();

                    if bi == bk {
                        self.write_and_break(i, v);
                    } else {
                        self.init_block(bi);
                        self.make_chain(bk, bi);
                        self.write_chained(i, v, bk);
                    }
                }
            }
        }
    }

    fn write_chained(&mut self, i: usize, v: usize, bk: usize) {
        if i % 2 == 0 {
            self.a[2 * bk + 1] = v;
        } else {
            self.a[i] = v;
        }
    }

    fn write_and_break(&mut self, i: usize, v: usize) {
        self.a[i] = v;
        self.break_chain(i / 2);
    }

    fn chained_to(&self, bi: usize) -> Option<usize> {
        let k = self.a[2 * bi];
        let bk = k / 2;

        if k % 2 == 0
            && ((bi < self.b && self.b <= bk && bk < self.a.len() / 2)
                || (bk < self.b && self.b <= bi))
            && self.a[k] == 2 * bi
        {
            return Some(bk);
        }

        None
    }

    fn make_chain(&mut self, bi: usize, bj: usize) {
        self.a[2 * bi] = 2 * bj;
        self.a[2 * bj] = 2 * bi;
    }

    fn break_chain(&mut self, bi: usize) {
        if let Some(bk) = self.chained_to(bi) {
            self.a[2 * bk] = 2 * bk;
        }
    }

    fn init_block(&mut self, bi: usize) {
        self.a[2 * bi] = self.initv;
        self.a[2 * bi + 1] = self.initv;
    }

    fn extend(&mut self) -> usize {
        let bs = self.b;
        let bk = self.chained_to(bs);
        self.b += 1;

        match bk {
            None => {
                self.init_block(bs);
                self.break_chain(bs);
                bs
            }
            Some(bk) => {
                self.a[2 * bs] = self.a[2 * bk + 1];
                self.break_chain(bs);
                self.init_block(bk);
                self.break_chain(bk);
                bk
            }
        }
    }
}

impl Index<usize> for InitArray {
    type Output = usize;
    fn index<'a>(&'_ self, i: usize) -> &'_ usize {
        self.read_ref(i)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, Rng, SeedableRng};

    #[test]
    fn new_even_length() {
        new(100, false)
    }

    #[test]
    fn from_vec_even_length() {
        new(100, true)
    }

    #[test]
    fn new_uneven_length() {
        new(101, false)
    }

    #[test]
    fn from_vec_uneven_length() {
        new(101, true)
    }

    #[test]
    fn multiple_inits() {
        let size = 100;
        let mut init_arr = InitArray::new(0, size);
        init_arr.init(1);
        assert_eq!(vec![1; size], init_arr.to_vec());
        init_arr.init(2);
        assert_eq!(vec![2; size], init_arr.to_vec());
        init_arr.init(3);
        assert_eq!(vec![3; size], init_arr.to_vec());
        init_arr.init(4);
        assert_eq!(vec![4; size], init_arr.to_vec());
    }

    #[test]
    fn writes_and_inits() {
        let size = 100;
        let mut init_arr = InitArray::new(0, size);
        let mut vec = vec![0; size];

        write_and_compare(&mut vec, &mut init_arr, 0, 1);
        write_and_compare(&mut vec, &mut init_arr, 22, 2);
        init_and_compare(&mut vec, &mut init_arr, 77);
        write_and_compare(&mut vec, &mut init_arr, 60, 4);
        write_and_compare(&mut vec, &mut init_arr, size - 1, 5);
        init_and_compare(&mut vec, &mut init_arr, 100);
    }

    #[test]
    fn random_writes_and_inits_even_length() {
        random_writes_and_inits(100, false);
    }

    #[test]
    fn random_writes_and_inits_uneven_length() {
        random_writes_and_inits(101, false);
    }

    #[test]
    fn random_writes_and_inits_even_length_from_vec() {
        random_writes_and_inits(100, true);
    }

    #[test]
    fn random_writes_and_inits_uneven_length_from_vec() {
        random_writes_and_inits(101, true);
    }

    #[test]
    fn accidental_chain() {
        let size = 8;
        let mut init_arr = InitArray::new(0, size);
        let mut vec = vec![0; size];
        write_and_compare(&mut vec, &mut init_arr, 0, 4);
    }

    fn new(size: usize, from_vec: bool) {
        let initv = 7;
        let init_arr = if from_vec {
            InitArray::from_vec(initv, vec![0; size])
        } else {
            InitArray::new(initv, size)
        };
        assert_eq!(vec![initv; size], init_arr.to_vec());
    }

    fn random_writes_and_inits(size: usize, from_vec: bool) {
        let initv = 7;
        let mut init_arr = if from_vec {
            InitArray::from_vec(initv, vec![0; size])
        } else {
            InitArray::new(initv, size)
        };
        let mut arr = vec![initv; size];

        let seed = [0; 32];
        let mut rng = StdRng::from_seed(seed);

        for v in 0..100 {
            if rng.gen_bool(0.03) {
                init_and_compare(&mut arr, &mut init_arr, v);
            } else {
                let i = rng.gen_range(0..size);
                write_and_compare(&mut arr, &mut init_arr, i, v);
            }
        }
    }

    fn init_and_compare(vec: &mut Vec<usize>, init_arr: &mut InitArray, initv: usize) {
        *vec = vec![initv; init_arr.a.len()];
        init_arr.init(initv);
        assert_eq!(*vec, init_arr.to_vec());
    }

    fn write_and_compare(vec: &mut Vec<usize>, init_arr: &mut InitArray, i: usize, v: usize) {
        vec[i] = v;
        init_arr.write(i, v);
        assert_eq!(*vec, init_arr.to_vec());
    }
}
