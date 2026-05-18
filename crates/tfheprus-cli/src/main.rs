use std::env;
use std::error::Error;
use std::time::Instant;

use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use tfheprus_circuits::{
    ActualPbsInstance, MulXaiInstance, PolyMulInstance, SampleExtractInstance,
};
use tfheprus_core::{
    bootstrap_without_keyswitch, bootstrap_without_keyswitch_ntt, EvaluationKey, GlweCiphertext,
    Goldilocks, LweCiphertext, Params, Polynomial, SecretKey, TestPolynomial, GOLDILOCKS_MODULUS,
};
use tfheprus_prover::{
    prove_actual_pbs, prove_mul_xai, prove_poly_mul, prove_sample_extract, verify_actual_pbs_proof,
    verify_mul_xai_proof, verify_poly_mul_proof, verify_sample_extract_proof,
};

fn main() -> Result<(), Box<dyn Error>> {
    let args = env::args().collect::<Vec<_>>();
    match args.get(1).map(String::as_str) {
        None | Some("params") => print_params(),
        Some("prove-poly-mul") => prove_poly_mul_demo()?,
        Some("prove-mul-xai") => prove_mul_xai_demo()?,
        Some("prove-sample-extract") => prove_sample_extract_demo()?,
        Some("prove-actual-pbs") => prove_actual_pbs_demo(parse_prove_preset_arg(&args)?)?,
        Some("profile-actual-pbs") => profile_actual_pbs_demo(parse_preset_arg(&args)?),
        Some("run-actual-pbs-native") => run_actual_pbs_native_demo(parse_preset_arg(&args)?),
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
    println!("TFHEprus scaffold ready: q=2^64-2^32+1");
    for (name, params) in [
        ("toy", Params::toy()),
        ("moderate", Params::moderate_toy()),
        ("paper-v1", Params::paper_v1()),
    ] {
        print_param_line(name, &params);
    }
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

fn prove_actual_pbs_demo(preset: ParamPreset) -> Result<(), Box<dyn Error>> {
    let (params, sk, instance) = actual_pbs_instance(preset.params());
    let prove_started = Instant::now();
    let proof = prove_actual_pbs(&instance)?;
    let prove_time = prove_started.elapsed();

    let verify_started = Instant::now();
    verify_actual_pbs_proof(&instance, &proof)?;
    let verify_time = verify_started.elapsed();

    println!(
        "actual-pbs proof verified: lwe_dimension={}, glwe_dimension={}, degree={}, nonzero_rotations={}, public_inputs={}",
        proof.params.lwe_dimension,
        proof.params.glwe_dimension,
        proof.params.polynomial_size,
        proof.nonzero_rotation_count,
        proof.public_inputs.len()
    );
    println!(
        "prove_ms={}, prove_us={}, verify_ms={}, verify_us={}",
        prove_time.as_millis(),
        prove_time.as_micros(),
        verify_time.as_millis(),
        verify_time.as_micros()
    );
    println!(
        "input_message={}, output_message={}",
        1,
        instance
            .output
            .decrypt(&params, &sk.extracted_output_lwe_key())
    );

    Ok(())
}

fn profile_actual_pbs_demo(preset: ParamPreset) {
    let (params, _sk, evaluation_key, input, test_polynomial) =
        actual_pbs_materials(preset.params());
    let instance = ActualPbsInstance::new(params.clone(), input, test_polynomial, evaluation_key);
    let public_inputs = instance.public_inputs().len();
    let private_inputs = instance.private_inputs().len();

    print_param_line(preset.name(), &params);
    println!(
        "actual-pbs profile: nonzero_rotations={}, public_inputs={}, private_inputs={}",
        instance.nonzero_rotation_count(),
        public_inputs,
        private_inputs
    );
}

fn run_actual_pbs_native_demo(preset: ParamPreset) {
    let params = preset.params();
    let mut rng = ChaCha20Rng::seed_from_u64(101);

    let sk_started = Instant::now();
    let sk = SecretKey::generate(&params, &mut rng);
    let sk_time = sk_started.elapsed();

    let ek_started = Instant::now();
    let evaluation_key = EvaluationKey::generate(&params, &sk, &mut rng);
    let ek_time = ek_started.elapsed();

    let (input, test_polynomial) = actual_pbs_input(&params, &sk);

    let coeff_started = Instant::now();
    let coeff_output =
        bootstrap_without_keyswitch(&params, &evaluation_key, &input, &test_polynomial);
    let coeff_time = coeff_started.elapsed();

    let key_started = Instant::now();
    let evaluation_key_ntt = evaluation_key.to_ntt();
    let key_ntt_time = key_started.elapsed();

    let ntt_started = Instant::now();
    let output =
        bootstrap_without_keyswitch_ntt(&params, &evaluation_key_ntt, &input, &test_polynomial);
    let ntt_time = ntt_started.elapsed();
    assert_eq!(output, coeff_output);

    println!(
        "actual-pbs native run: preset={}, lwe_dimension={}, glwe_dimension={}, degree={}",
        preset.name(),
        params.lwe_dimension,
        params.glwe_dimension,
        params.polynomial_size
    );
    println!(
        "secret_keygen_ms={}, secret_keygen_us={}, eval_keygen_ms={}, eval_keygen_us={}, native_coeff_ms={}, native_coeff_us={}, key_ntt_precompute_ms={}, key_ntt_precompute_us={}, native_ntt_ms={}, native_ntt_us={}",
        sk_time.as_millis(),
        sk_time.as_micros(),
        ek_time.as_millis(),
        ek_time.as_micros(),
        coeff_time.as_millis(),
        coeff_time.as_micros(),
        key_ntt_time.as_millis(),
        key_ntt_time.as_micros(),
        ntt_time.as_millis(),
        ntt_time.as_micros()
    );
    println!(
        "input_message={}, output_message={}",
        1,
        output.decrypt(&params, &sk.extracted_output_lwe_key())
    );
}

fn actual_pbs_instance(params: Params) -> (Params, SecretKey, ActualPbsInstance) {
    let (params, sk, evaluation_key, input, test_polynomial) = actual_pbs_materials(params);
    let instance = ActualPbsInstance::new(params.clone(), input, test_polynomial, evaluation_key);
    (params, sk, instance)
}

fn actual_pbs_materials(
    params: Params,
) -> (
    Params,
    SecretKey,
    EvaluationKey,
    LweCiphertext,
    TestPolynomial,
) {
    let mut rng = ChaCha20Rng::seed_from_u64(101);
    let sk = SecretKey::generate(&params, &mut rng);
    let evaluation_key = EvaluationKey::generate(&params, &sk, &mut rng);
    let (input, test_polynomial) = actual_pbs_input(&params, &sk);
    (params, sk, evaluation_key, input, test_polynomial)
}

fn actual_pbs_input(params: &Params, sk: &SecretKey) -> (LweCiphertext, TestPolynomial) {
    let input_message = 1;
    let output_message = 3;
    let mask_step = GOLDILOCKS_MODULUS / params.exponent_modulus() as u64;
    let mask = (0..params.lwe_dimension)
        .map(|index| {
            let exponent = (index % (params.exponent_modulus() - 1)) + 1;
            Goldilocks::from_u64(mask_step * exponent as u64)
        })
        .collect();
    let input = LweCiphertext::encrypt_with_mask(params, &sk.input_lwe, input_message, mask);
    let test_polynomial = TestPolynomial::single_slot(params, input_message, output_message);
    (input, test_polynomial)
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
        "Usage: tfheprus [params|prove-poly-mul|prove-mul-xai|prove-sample-extract|prove-actual-pbs|profile-actual-pbs [toy|moderate]|run-actual-pbs-native [toy|moderate]]"
    );
}

#[derive(Clone, Copy, Debug)]
enum ParamPreset {
    Toy,
    Moderate,
}

impl ParamPreset {
    fn name(self) -> &'static str {
        match self {
            Self::Toy => "toy",
            Self::Moderate => "moderate",
        }
    }

    fn params(self) -> Params {
        match self {
            Self::Toy => Params::toy(),
            Self::Moderate => Params::moderate_toy(),
        }
    }
}

fn parse_preset_arg(args: &[String]) -> Result<ParamPreset, Box<dyn Error>> {
    match args.get(2).map(String::as_str) {
        None | Some("toy") => Ok(ParamPreset::Toy),
        Some("moderate" | "moderate-toy" | "mid") => Ok(ParamPreset::Moderate),
        Some(other) => Err(format!("unknown parameter preset: {other}").into()),
    }
}

fn parse_prove_preset_arg(args: &[String]) -> Result<ParamPreset, Box<dyn Error>> {
    let preset = parse_preset_arg(args)?;
    if matches!(preset, ParamPreset::Moderate) {
        return Err(
            "prove-actual-pbs moderate is intentionally disabled; use profile-actual-pbs moderate and run-actual-pbs-native moderate first".into(),
        );
    }
    Ok(preset)
}

fn print_param_line(name: &str, params: &Params) {
    println!(
        "{name}: n={}, N={}, k={}, B=2^{}, l={}, p={}",
        params.lwe_dimension,
        params.polynomial_size,
        params.glwe_dimension,
        params.decomposition_base_log,
        params.decomposition_level_count,
        params.plaintext_modulus
    );
}
