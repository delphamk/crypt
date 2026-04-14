use crate::utils::util::mod_pow;
use rand::RngExt;
use sha2::{Digest, Sha256};

pub struct SchnorrProof {
    pub commitment: u128,
    pub response: u128,
}

/// Prover: Generates a proof of knowledge for a secret key
pub fn prove_knowledge(
    prime_modulus: u128,
    generator: u128,
    secret_key: u128,
    public_key: u128,
) -> SchnorrProof {
    let mut rng = rand::rng();

    // 1. Generate a secret nonce (random blinding factor)
    let secret_nonce = rng.random_range(1..prime_modulus - 1);

    // 2. Create a public commitment from the nonce
    let commitment = mod_pow(generator, secret_nonce, prime_modulus);

    // 3. Fiat-Shamir: Generate a challenge by hashing public context + commitment
    let mut hasher = Sha256::new();
    hasher.update(generator.to_be_bytes());
    hasher.update(public_key.to_be_bytes());
    hasher.update(commitment.to_be_bytes());
    let hash_result = hasher.finalize();

    // Convert hash to u128 challenge (ensuring it's within group order)
    let challenge =
        u128::from_be_bytes(hash_result[..16].try_into().unwrap()) % (prime_modulus - 1);

    // 4. Create the response: z = r + (e * w)
    let response = (secret_nonce + (challenge * secret_key)) % (prime_modulus - 1);

    SchnorrProof {
        commitment,
        response,
    }
}

/// Verifier: Validates the proof without needing to interact with the prover
pub fn verify_knowledge(
    prime_modulus: u128,
    generator: u128,
    public_key: u128,
    proof: &SchnorrProof,
) -> bool {
    // 1. Reconstruct the challenge using the same hash logic
    let mut hasher = Sha256::new();
    hasher.update(generator.to_be_bytes());
    hasher.update(public_key.to_be_bytes());
    hasher.update(proof.commitment.to_be_bytes());
    let hash_result = hasher.finalize();

    let challenge =
        u128::from_be_bytes(hash_result[..16].try_into().unwrap()) % (prime_modulus - 1);

    // 2. Check the verification equation: g^z == commitment * public_key^challenge
    let left_side = mod_pow(generator, proof.response, prime_modulus);
    let right_side =
        (proof.commitment * mod_pow(public_key, challenge, prime_modulus)) % prime_modulus;

    left_side == right_side
}

pub fn run() {
    let prime_modulus: u128 = 104729;
    let generator: u128 = 2;

    // Prover's Setup
    let secret_key: u128 = 12345;
    let public_key = mod_pow(generator, secret_key, prime_modulus);

    println!("Public Key: {}", public_key);

    // Generation
    let proof = prove_knowledge(prime_modulus, generator, secret_key, public_key);
    println!(
        "Proof generated: [commitment: {}, response: {}]",
        proof.commitment, proof.response
    );

    // Verification
    if verify_knowledge(prime_modulus, generator, public_key, &proof) {
        println!("Verification SUCCESS: Prover holds the secret key!");
    } else {
        println!("Verification FAILED!");
    }
}

