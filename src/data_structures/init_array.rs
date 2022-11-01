use std::{mem::MaybeUninit, ops::Index};

pub struct InitArray<const LEN: usize> {
    a: [MaybeUninit<i32>; LEN],
    initv: i32,
    b: usize,
}

impl<const LEN: usize> InitArray<LEN> {
    pub fn new(v: i32) -> Self {
        InitArray {
            a: unsafe { MaybeUninit::uninit().assume_init() },
            initv: v,
            b: 0,
        }
    }

    pub fn init(&mut self, v: i32) {
        self.initv = v;
        self.b = 0;
    }

    pub fn to_array(&self) -> [i32; LEN] {
        let mut arr = [0; LEN];

        for (i, v) in arr.iter_mut().enumerate() {
            *v = *self.read_ref(i);
        }

        arr
    }

    pub fn read_ref(&self, i: usize) -> &i32 {
        let bi = i / 2;
        let bk = self.chained_to(bi);

        if i < 2 * self.b {
            if bk.is_some() {
                &self.initv
            } else {
                self.unsafe_get_ref(i)
            }
        } else if bk.is_some() {
            if i % 2 == 0 {
                self.unsafe_get_ref(self.unsafe_get(i) as usize + 1)
            } else {
                self.unsafe_get_ref(i)
            }
        } else {
            &self.initv
        }
    }

    pub fn write(&mut self, i: usize, v: i32) {
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
                        self.a[bj * 2 + 1].write(self.unsafe_get(bi * 2 + 1));
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

    fn write_chained(&mut self, i: usize, v: i32, bk: usize) {
        if i % 2 == 0 {
            self.a[bk * 2 + 1].write(v);
        } else {
            self.a[i].write(v);
        }
    }

    fn write_and_break(&mut self, i: usize, v: i32) {
        self.a[i].write(v);
        self.break_chain(i / 2);
    }

    fn unsafe_get(&self, i: usize) -> i32 {
        unsafe { self.a[i].assume_init_read() }
    }

    fn unsafe_get_ref(&self, i: usize) -> &i32 {
        unsafe { self.a[i].assume_init_ref() }
    }

    fn chained_to(&self, bi: usize) -> Option<usize> {
        let k = self.unsafe_get(2 * bi) as usize;
        let bk = k / 2;

        if k % 2 == 0
            && ((0 <= bi as i32 && bi < self.b && self.b <= bk && bk < self.a.len() / 2)
                || (0 <= bk as i32 && bk < self.b && self.b <= bi))
            && self.unsafe_get(k) as usize == 2 * bi
        {
            return Some(bk);
        }

        None
    }

    fn make_chain(&mut self, bi: usize, bj: usize) {
        self.a[2 * bi].write(2 * bj as i32);
        self.a[2 * bj].write(2 * bi as i32);
    }

    fn break_chain(&mut self, bi: usize) {
        if let Some(bk) = self.chained_to(bi) {
            self.a[2 * bk].write(2 * bk as i32);
        }
    }

    fn init_block(&mut self, bi: usize) {
        self.a[2 * bi].write(self.initv);
        self.a[2 * bi + 1].write(self.initv);
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
                self.a[bs * 2].write(self.unsafe_get(bk * 2 + 1));
                self.break_chain(bs);
                self.init_block(bk);
                self.break_chain(bk);
                bk
            }
        }
    }
}

impl<const LEN: usize> Index<usize> for InitArray<LEN> {
    type Output = i32;
    fn index<'a>(&'_ self, i: usize) -> &'_ i32 {
        self.read_ref(i)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, Rng, SeedableRng};

    #[test]
    fn new() {
        let initv = 7;
        let init_arr = InitArray::new(initv);
        assert_eq!([initv; 100], init_arr.to_array());
    }

    #[test]
    fn multiple_inits() {
        let mut init_arr = InitArray::new(0);
        init_arr.init(1);
        assert_eq!([1; 100], init_arr.to_array());
        init_arr.init(2);
        assert_eq!([2; 100], init_arr.to_array());
        init_arr.init(3);
        assert_eq!([3; 100], init_arr.to_array());
        init_arr.init(4);
        assert_eq!([4; 100], init_arr.to_array());
    }

    #[test]
    fn writes_and_inits() {
        let mut init_arr = InitArray::new(0);
        let mut arr = [0; 100];

        write_and_compare(&mut arr, &mut init_arr, 3, 1);
        write_and_compare(&mut arr, &mut init_arr, 22, 2);
        init_and_compare(&mut arr, &mut init_arr, 77);
        write_and_compare(&mut arr, &mut init_arr, 60, 4);
        write_and_compare(&mut arr, &mut init_arr, 0, 5);
        init_and_compare(&mut arr, &mut init_arr, 100);
    }

    #[test]
    fn random_writes_and_inits() {
        let initv = 7;
        const LEN: usize = 100;
        let mut init_arr = InitArray::new(initv);
        let mut arr = [initv; LEN];

        let seed = [0; 32];
        let mut rng = StdRng::from_seed(seed);

        for v in 0..1000 {
            if rng.gen_bool(0.03) {
                init_and_compare(&mut arr, &mut init_arr, v);
            } else {
                let i = rng.gen_range(0..LEN);
                write_and_compare(&mut arr, &mut init_arr, i, v);
            }
        }
    }

    fn init_and_compare<const LEN: usize>(
        arr: &mut [i32; LEN],
        init_arr: &mut InitArray<LEN>,
        initv: i32,
    ) {
        *arr = [initv; LEN];
        init_arr.init(initv);
        assert_eq!(*arr, init_arr.to_array());
    }

    fn write_and_compare<const LEN: usize>(
        arr: &mut [i32; LEN],
        init_arr: &mut InitArray<LEN>,
        i: usize,
        v: i32,
    ) {
        arr[i] = v;
        init_arr.write(i, v);
        assert_eq!(*arr, init_arr.to_array());
    }
}
