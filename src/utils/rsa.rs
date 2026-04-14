use crate::utils::util::*;

pub fn rsa() {
    // 1. Choose two small primes (p, q)
    let p: u128 = 61;
    let q: u128 = 53;

    // 2. Calculate n = p * q
    let n = p * q;

    // 3. Calculate totient: phi = (p - 1) * (q - 1)
    let phi = (p - 1) * (q - 1);

    // 4. Choose public exponent e (must be coprime with phi)
    let e: u128 = 17;

    // 5. Calculate private key d (modular multiplicative inverse of e mod phi)
    let d = mod_inverse(e as i128, phi as i128) as u128;

    // The data to encrypt
    let message: u128 = 42;

    // Encryption: c = m^e mod n
    let encrypted = mod_pow(message, e, n);

    // Decryption: m = c^d mod n
    let decrypted = mod_pow(encrypted, d, n);

    println!("Public Key (n: {}, e: {})", n, e);
    println!("Private Key (d: {})", d);
    println!("Original:  {}", message);
    println!("Encrypted: {}", encrypted);
    println!("Decrypted: {}", decrypted);
}
