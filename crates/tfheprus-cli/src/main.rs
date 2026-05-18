use std::env;
use std::error::Error;

use tfheprus_circuits::{
    MulXaiInstance, PolyMulInstance, SampleExtractInstance, TrivialPbsInstance,
};
use tfheprus_core::{
    decode_message, encode_message, GlweCiphertext, Goldilocks, LweCiphertext, Params, Polynomial,
    TestPolynomial,
};
use tfheprus_prover::{
    prove_mul_xai, prove_poly_mul, prove_sample_extract, prove_trivial_pbs, verify_mul_xai_proof,
    verify_poly_mul_proof, verify_sample_extract_proof, verify_trivial_pbs_proof,
};

fn main() -> Result<(), Box<dyn Error>> {
    match env::args().nth(1).as_deref() {
        None | Some("params") => print_params(),
        Some("prove-poly-mul") => prove_poly_mul_demo()?,
        Some("prove-mul-xai") => prove_mul_xai_demo()?,
        Some("prove-sample-extract") => prove_sample_extract_demo()?,
        Some("prove-trivial-pbs") => prove_trivial_pbs_demo()?,
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

fn prove_mul_xai_demo() -> Result<(), Box<dyn Error>> {
    let input = polynomial(&[1, 2, 3, 4]);
    let exponent = 5;
    let instance = MulXaiInstance::new(input, exponent);

    let proof = prove_mul_xai(&instance)?;
    verify_mul_xai_proof(&instance, &proof)?;

    println!(
        "mul_xai proof verified: degree={}, exponent={}, public_inputs={}",
        proof.degree,
        proof.exponent,
        proof.public_inputs.len()
    );
    println!("output={}", format_polynomial(&instance.output));

    Ok(())
}

fn prove_sample_extract_demo() -> Result<(), Box<dyn Error>> {
    let glwe = GlweCiphertext {
        mask: vec![polynomial(&[1, 2, 3, 4])],
        body: polynomial(&[5, 6, 7, 8]),
    };
    let instance = SampleExtractInstance::new(glwe);

    let proof = prove_sample_extract(&instance)?;
    verify_sample_extract_proof(&instance, &proof)?;

    println!(
        "sample-extract proof verified: glwe_dimension={}, degree={}, public_inputs={}",
        proof.glwe_dimension,
        proof.degree,
        proof.public_inputs.len()
    );
    println!("lwe_mask={}", format_coefficients(&instance.lwe.mask));
    println!("lwe_body={}", instance.lwe.body.value());

    Ok(())
}

fn prove_trivial_pbs_demo() -> Result<(), Box<dyn Error>> {
    let params = Params::toy();
    let input_message = 1;
    let output_message = 3;
    let input = LweCiphertext {
        mask: vec![Goldilocks::ZERO; params.lwe_dimension],
        body: encode_message(&params, input_message),
    };
    let test_polynomial = TestPolynomial::single_slot(&params, input_message, output_message);
    let instance = TrivialPbsInstance::new(params.clone(), input, test_polynomial);

    let proof = prove_trivial_pbs(&instance)?;
    verify_trivial_pbs_proof(&instance, &proof)?;

    println!(
        "trivial-pbs proof verified: lwe_dimension={}, glwe_dimension={}, degree={}, initial_exponent={}, public_inputs={}",
        proof.params.lwe_dimension,
        proof.params.glwe_dimension,
        proof.params.polynomial_size,
        proof.initial_exponent,
        proof.public_inputs.len()
    );
    println!(
        "input_message={}, output_message={}",
        input_message,
        decode_message(&params, instance.output.body)
    );

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

fn format_coefficients(coeffs: &[Goldilocks]) -> String {
    let coeffs = coeffs
        .iter()
        .map(|coeff| coeff.value().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{coeffs}]")
}

fn print_help() {
    println!(
        "Usage: tfheprus [params|prove-poly-mul|prove-mul-xai|prove-sample-extract|prove-trivial-pbs]"
    );
}
