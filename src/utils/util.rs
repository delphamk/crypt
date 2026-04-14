pub fn mod_pow(mut base: u128, mut exp: u128, modulus: u128) -> u128 {
    let mut res = 1;
    base %= modulus;
    while exp > 0 {
        if exp % 2 == 1 {
            res = (res * base) % modulus;
        }
        base = (base * base) % modulus;
        exp /= 2;
    }
    res
}

pub fn mod_inverse(a: i128, m: i128) -> i128 {
    let (m0, mut x0, mut x1) = (m, 0, 1);
    let (mut a, mut m) = (a, m);

    while a > 1 {
        let q = a / m;
        let mut t = m;
        m = a % m;
        a = t;
        t = x0;
        x0 = x1 - q * x0;
        x1 = t;
    }

    if x1 < 0 {
        x1 += m0;
    }
    x1
}
