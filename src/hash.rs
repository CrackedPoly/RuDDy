#[macro_export]
macro_rules! hash_2 {
    ($a:expr, $b:expr) => {
        (($a + $b) * ($a + $b + 1) >> 1) + $a
    };
}

#[macro_export]
macro_rules! hash_3 {
    ($a:expr, $b:expr, $c:expr) => {
        hash_2!(hash_2!($a, $b), $c)
    };
}

pub(crate) use hash_2;
pub(crate) use hash_3;
