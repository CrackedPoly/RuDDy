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
    return true;
}

pub fn prime_lte(n: u32) -> u32 {
    let mut num = n;
    if n % 2 == 0 {
        num -= 1;
    }
    while !is_prime(num) {
        num -= 2;
    }
    return num;
}
