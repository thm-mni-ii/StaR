use std::mem::MaybeUninit;

pub fn sub(left: usize, right: usize) -> usize {
    unsafe {
        let arr: [MaybeUninit<u32>; 3] = MaybeUninit::uninit().assume_init();
        println!("{}", arr[2].assume_init());
    }
    left - right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = sub(2, 2);
        assert_eq!(result, 0);
    }
}
