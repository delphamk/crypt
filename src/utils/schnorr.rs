use crate::utils::util::mod_pow;
use rand::RngExt;

/// The transcript sent from Prover to Verifier
pub struct Proof {
    pub a: u128, // Commitment
    pub z: u128, // Response
}

/// Prover's role: Generates the commitment and the response based on the challenge
pub fn prove(p: u128, g: u128, w: u128, e: u128) -> Proof {
    let mut rng = rand::rng();

    // Move 1: Commitment (a)
    let r = rng.random_range(1..p - 1);
    let a = mod_pow(g, r, p);

    // Move 3: Response (z)
    let z = (r + (e * w)) % (p - 1);

    Proof { a, z }
}

/// Verifier's role: Checks if the proof holds given the public parameters
pub fn verify(p: u128, g: u128, x: u128, e: u128, proof: &Proof) -> bool {
    let left_side = mod_pow(g, proof.z, p);
    let right_side = (proof.a * mod_pow(x, e, p)) % p;

    left_side == right_side
}

pub fn discrete_log_demo() {
    let p: u128 = 104729;
    let g: u128 = 2;
    let w: u128 = 12345; // Secret
    let x = mod_pow(g, w, p); // Public Key

    println!("Proving knowledge of secret for x: {}", x);

    // Verifier picks a random challenge
    let mut rng = rand::rng();
    let e: u128 = rng.random_range(1..1000);

    // Generate proof
    let proof = prove(p, g, w, e);
    println!("Proof generated: a={}, z={}", proof.a, proof.z);

    // Run verification
    if verify(p, g, x, e, &proof) {
        println!("Verification SUCCESS!");
    } else {
        println!("Verification FAILED.");
    }
}
