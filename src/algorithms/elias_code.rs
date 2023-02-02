use bitvec::{prelude::Msb0, slice::BitSlice, vec::BitVec};

type Encoded = BitVec<u32, Msb0>;
type Decoded = Vec<u32>;
type Input = Decoded;

pub fn elias_gamma_encode(numbers: &Input) -> Encoded {
    let mut bv = Encoded::new();

    for x in numbers {
        let pow = (*x as f64).log2().floor() as u32;

        for _ in 0..pow {
            bv.push(false)
        }

        let xb = Encoded::from_element(*x);
        let bits = (pow + 1) as usize;
        bv.extend(xb[xb.len() - bits..].iter());
    }

    bv
}

pub fn elias_gamma_decode(encoded: &Encoded) -> Decoded {
    let mut numbers = vec![];

    let mut i = 0;
    let mut n = 0;

    while i < encoded.len() {
        if !encoded[i] {
            n += 1;
            i += 1
        } else {
            let bits = &encoded[i..(i + n + 1)];
            numbers.push(to_u32(bits));
            i += n + 1;
            n = 0;
        }
    }

    numbers
}

fn to_u32(bits: &BitSlice<u32, Msb0>) -> u32 {
    bits.iter().fold(0, |res, bit| (res << 1) ^ u32::from(*bit))
}

#[cfg(test)]
mod tests {
    use rand::{rngs::StdRng, Rng, SeedableRng};

    use super::*;

    #[test]
    fn gamma_encode_and_decode() {
        encode_and_decode(elias_gamma_encode, elias_gamma_decode)
    }

    fn encode_and_decode(enc: fn(&Input) -> Encoded, dec: fn(&Encoded) -> Decoded) {
        let seed = [0; 32];
        let mut rng = StdRng::from_seed(seed);

        for size in 0..100 {
            let input = (0..size)
                .map(|_| rng.gen_range(u32::MIN..u32::MAX))
                .collect();
            let encoded = enc(&input);
            let decoded = dec(&encoded);
            assert_eq!(input, decoded)
        }
    }
}
