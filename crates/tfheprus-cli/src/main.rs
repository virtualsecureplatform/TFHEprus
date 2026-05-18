use std::env;
use std::error::Error;

use tfheprus_circuits::PolyMulInstance;
use tfheprus_core::{Goldilocks, Params, Polynomial};
use tfheprus_prover::{prove_poly_mul, verify_poly_mul_proof};

fn main() -> Result<(), Box<dyn Error>> {
    match env::args().nth(1).as_deref() {
        None | Some("params") => print_params(),
        Some("prove-poly-mul") => prove_poly_mul_demo()?,
        Some("-h" | "--help" | "help") => print_help(),
        Some(command) => {
            eprintln!("unknown command: {command}");
            print_help();
            std::process::exit(2);
        }
    }

    Ok(())
}

fn print_params() {
    let params = Params::paper_v1();
    println!(
        "TFHEprus scaffold ready: q=2^64-2^32+1, n={}, N={}, k={}, B=2^{}, l={}",
        params.lwe_dimension,
        params.polynomial_size,
        params.glwe_dimension,
        params.decomposition_base_log,
        params.decomposition_level_count
    );
}

fn prove_poly_mul_demo() -> Result<(), Box<dyn Error>> {
    let lhs = polynomial(&[1, 2, 3, 4]);
    let rhs = polynomial(&[5, 6, 7, 8]);
    let instance = PolyMulInstance::new(lhs, rhs);

    let proof = prove_poly_mul(&instance)?;
    verify_poly_mul_proof(&instance, &proof)?;

    println!(
        "poly-mul proof verified: degree={}, public_inputs={}",
        proof.degree,
        proof.public_inputs.len()
    );
    println!("product={}", format_polynomial(&instance.product));

    Ok(())
}

fn polynomial(coeffs: &[u64]) -> Polynomial {
    Polynomial::from_coeffs(coeffs.iter().copied().map(Goldilocks::from_u64).collect())
}

fn format_polynomial(poly: &Polynomial) -> String {
    let coeffs = poly
        .coeffs()
        .iter()
        .map(|coeff| coeff.value().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{coeffs}]")
}

fn print_help() {
    println!("Usage: tfheprus [params|prove-poly-mul]");
}
