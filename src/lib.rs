mod bdd;
mod cache;

pub use bdd::ruddy::Ruddy;
pub use bdd::Bdd;
pub use bdd::{BddIO, BddManager, BddOp, PrintSet};

mod prime {
    fn is_prime(n: u32) -> bool {
        if n < 2 {
            return false;
        }
        if n == 2 {
            return true;
        }
        if n % 2 == 0 {
            return false;
        }
        let mut i = 3;
        while i * i <= n {
            if n % i == 0 {
                return false;
            }
            i += 2;
        }
        true
    }

    pub fn prime_lte(n: u32) -> u32 {
        let mut num = n;
        if n % 2 == 0 {
            num -= 1;
        }
        while !is_prime(num) {
            num -= 2;
        }
        num
    }
}

mod hash {
    macro_rules! hash_2 {
        ($a:expr, $b:expr) => {
            (($a + $b) * ($a + $b + 1) >> 1) + $a
        };
    }

    macro_rules! hash_3 {
        ($a:expr, $b:expr, $c:expr) => {
            hash_2!(hash_2!($a, $b), $c)
        };
    }

    pub(crate) use hash_2;
    pub(crate) use hash_3;
}
