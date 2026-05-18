use std::env;
use std::error::Error;
use std::time::{Duration, Instant};

use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use tfheprus_circuits::{
    pbs_bsk_digest_initial, pbs_mask_digest_initial, ActualPbsChainChunkInstance,
    ActualPbsCircuitProfile, ActualPbsInstance, ActualPbsStepChainInstance, ActualPbsStepInstance,
    ActualPbsStepPrivateInstance, MulXaiInstance, PolyMulInstance, SampleExtractInstance,
    SELECTOR_DIGEST_WIDTH,
};
use tfheprus_core::{
    bootstrap_without_keyswitch, bootstrap_without_keyswitch_ntt, sample_extract_index_zero,
    EvaluationKey, GlweCiphertext, Goldilocks, LweCiphertext, Params, Polynomial, SecretKey,
    TestPolynomial, GOLDILOCKS_MODULUS,
};
use tfheprus_prover::{
    prove_actual_pbs, prove_actual_pbs_chain_chunk, prove_actual_pbs_step,
    prove_actual_pbs_step_chain, prove_actual_pbs_step_private,
    prove_aggregated_recursive_actual_pbs_chain_chunk_pair,
    prove_aggregated_recursive_actual_pbs_chain_chunk_tree, prove_mul_xai, prove_poly_mul,
    prove_recursive_actual_pbs_chain_chunk, prove_sample_extract,
    verify_actual_pbs_chain_chunk_proof, verify_actual_pbs_proof,
    verify_actual_pbs_step_chain_proof, verify_actual_pbs_step_private_proof,
    verify_actual_pbs_step_proof,
    verify_aggregated_recursive_actual_pbs_chain_chunk_pair_statement_proof,
    verify_aggregated_recursive_actual_pbs_chain_chunk_tree_statement_proof, verify_mul_xai_proof,
    verify_poly_mul_proof, verify_recursive_actual_pbs_chain_chunk_statement_proof,
    verify_sample_extract_proof, ActualPbsChainChunkStatement,
};

fn main() -> Result<(), Box<dyn Error>> {
    let args = env::args().collect::<Vec<_>>();
    match args.get(1).map(String::as_str) {
        None | Some("params") => print_params(),
        Some("prove-poly-mul") => prove_poly_mul_demo()?,
        Some("prove-mul-xai") => prove_mul_xai_demo()?,
        Some("prove-sample-extract") => prove_sample_extract_demo()?,
        Some("prove-actual-pbs") => prove_actual_pbs_demo(parse_prove_preset_arg(&args)?)?,
        Some("prove-pbs-step") => prove_pbs_step_demo(parse_preset_arg(&args)?)?,
        Some("prove-pbs-step-private") => prove_pbs_step_private_demo(parse_preset_arg(&args)?)?,
        Some("prove-pbs-step-chain") => prove_pbs_step_chain_demo(parse_preset_arg(&args)?)?,
        Some("prove-pbs-chain-chunk") => prove_pbs_chain_chunk_demo(
            parse_preset_arg(&args)?,
            parse_chunk_step_count_arg(&args)?,
        )?,
        Some("prove-pbs-chain-chunk-recursive") => prove_pbs_chain_chunk_recursive_demo(
            parse_preset_arg(&args)?,
            parse_chunk_step_count_arg(&args)?,
        )?,
        Some("prove-pbs-chain-prefix-recursive") => prove_pbs_chain_prefix_recursive_demo(
            parse_preset_arg(&args)?,
            parse_chunk_step_count_arg(&args)?,
            parse_optional_total_step_count_arg(&args)?,
        )?,
        Some("prove-pbs-chain-pair-aggregate-recursive") => {
            prove_pbs_chain_pair_aggregate_recursive_demo(
                parse_preset_arg(&args)?,
                parse_chunk_step_count_arg(&args)?,
            )?
        }
        Some("prove-pbs-chain-tree-aggregate-recursive") => {
            prove_pbs_chain_tree_aggregate_recursive_demo(
                parse_preset_arg(&args)?,
                parse_chunk_step_count_arg(&args)?,
                parse_optional_chunk_count_arg(&args)?,
            )?
        }
        Some("profile-pbs-chain-tree") => profile_pbs_chain_tree_demo(
            parse_preset_arg(&args)?,
            parse_chunk_step_count_arg(&args)?,
            parse_optional_total_step_count_arg(&args)?,
        )?,
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

fn prove_pbs_step_demo(preset: ParamPreset) -> Result<(), Box<dyn Error>> {
    let (params, instance) = actual_pbs_first_step_instance(preset.params());
    let prove_started = Instant::now();
    let proof = prove_actual_pbs_step(&instance)?;
    let prove_time = prove_started.elapsed();

    let verify_started = Instant::now();
    verify_actual_pbs_step_proof(&instance, &proof)?;
    let verify_time = verify_started.elapsed();

    println!(
        "pbs-step proof verified: preset={}, exponent={}, glwe_dimension={}, degree={}, public_inputs={}",
        preset.name(),
        proof.exponent,
        proof.params.glwe_dimension,
        proof.params.polynomial_size,
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
        "output_body0={}, params_n={}",
        instance.output_accumulator.body[0].value(),
        params.lwe_dimension
    );

    Ok(())
}

fn prove_pbs_step_private_demo(preset: ParamPreset) -> Result<(), Box<dyn Error>> {
    let (params, public_instance) = actual_pbs_first_step_instance(preset.params());
    let instance = ActualPbsStepPrivateInstance::new(
        public_instance.params.clone(),
        public_instance.mask_value,
        public_instance.input_accumulator,
        public_instance.selector,
    );
    let public_inputs = instance.public_inputs().len();
    let private_inputs = instance.private_inputs().len();

    let prove_started = Instant::now();
    let proof = prove_actual_pbs_step_private(&instance)?;
    let prove_time = prove_started.elapsed();

    let verify_started = Instant::now();
    verify_actual_pbs_step_private_proof(&instance, &proof)?;
    let verify_time = verify_started.elapsed();

    println!(
        "pbs-step-private proof verified: preset={}, exponent={}, glwe_dimension={}, degree={}, public_inputs={}, private_inputs={}",
        preset.name(),
        proof.exponent,
        proof.params.glwe_dimension,
        proof.params.polynomial_size,
        public_inputs,
        private_inputs
    );
    println!(
        "prove_ms={}, prove_us={}, verify_ms={}, verify_us={}",
        prove_time.as_millis(),
        prove_time.as_micros(),
        verify_time.as_millis(),
        verify_time.as_micros()
    );
    println!(
        "selector_digest={}, output_body0={}, params_n={}",
        format_coefficients(&instance.selector_digest),
        instance.output_accumulator.body[0].value(),
        params.lwe_dimension
    );

    Ok(())
}

fn prove_pbs_step_chain_demo(preset: ParamPreset) -> Result<(), Box<dyn Error>> {
    let (params, public_instance) = actual_pbs_first_step_instance(preset.params());
    let instance = ActualPbsStepChainInstance::new(
        public_instance.params.clone(),
        public_instance.mask_value,
        public_instance.input_accumulator,
        public_instance.selector,
        pbs_bsk_digest_initial(),
        pbs_mask_digest_initial(),
    );
    let public_inputs = instance.public_inputs().len();
    let private_inputs = instance.private_inputs().len();

    let prove_started = Instant::now();
    let proof = prove_actual_pbs_step_chain(&instance)?;
    let prove_time = prove_started.elapsed();

    let verify_started = Instant::now();
    verify_actual_pbs_step_chain_proof(&instance, &proof)?;
    let verify_time = verify_started.elapsed();

    println!(
        "pbs-step-chain proof verified: preset={}, exponent={}, glwe_dimension={}, degree={}, public_inputs={}, private_inputs={}",
        preset.name(),
        proof.exponent,
        proof.params.glwe_dimension,
        proof.params.polynomial_size,
        public_inputs,
        private_inputs
    );
    println!(
        "prove_ms={}, prove_us={}, verify_ms={}, verify_us={}",
        prove_time.as_millis(),
        prove_time.as_micros(),
        verify_time.as_millis(),
        verify_time.as_micros()
    );
    println!(
        "bsk_digest_out={}, mask_digest_out={}, output_body0={}, params_n={}",
        format_coefficients(&instance.bsk_digest_out),
        format_coefficients(&instance.mask_digest_out),
        instance.output_accumulator.body[0].value(),
        params.lwe_dimension
    );

    Ok(())
}

fn prove_pbs_chain_chunk_demo(
    preset: ParamPreset,
    step_count: usize,
) -> Result<(), Box<dyn Error>> {
    let (params, instance) = actual_pbs_chain_chunk_instance(preset.params(), step_count)?;
    let public_inputs = instance.public_inputs().len();
    let private_inputs = instance.private_inputs().len();

    let prove_started = Instant::now();
    let proof = prove_actual_pbs_chain_chunk(&instance)?;
    let prove_time = prove_started.elapsed();

    let verify_started = Instant::now();
    verify_actual_pbs_chain_chunk_proof(&instance, &proof)?;
    let verify_time = verify_started.elapsed();

    println!(
        "pbs-chain-chunk proof verified: preset={}, steps={}, glwe_dimension={}, degree={}, public_inputs={}, private_inputs={}",
        preset.name(),
        proof.step_count,
        proof.params.glwe_dimension,
        proof.params.polynomial_size,
        public_inputs,
        private_inputs
    );
    println!(
        "prove_ms={}, prove_us={}, verify_ms={}, verify_us={}",
        prove_time.as_millis(),
        prove_time.as_micros(),
        verify_time.as_millis(),
        verify_time.as_micros()
    );
    println!(
        "exponents={:?}, bsk_digest_out={}, mask_digest_out={}, output_body0={}, params_n={}",
        proof.exponents,
        format_coefficients(&instance.bsk_digest_out),
        format_coefficients(&instance.mask_digest_out),
        instance.output_accumulator.body[0].value(),
        params.lwe_dimension
    );

    Ok(())
}

fn prove_pbs_chain_chunk_recursive_demo(
    preset: ParamPreset,
    step_count: usize,
) -> Result<(), Box<dyn Error>> {
    let (params, instance) = actual_pbs_chain_chunk_instance(preset.params(), step_count)?;

    let prove_started = Instant::now();
    let proof = prove_recursive_actual_pbs_chain_chunk(&instance)?;
    let prove_time = prove_started.elapsed();

    let verify_started = Instant::now();
    let statement = ActualPbsChainChunkStatement::from_instance(&instance);
    verify_recursive_actual_pbs_chain_chunk_statement_proof(&statement, &proof)?;
    let verify_time = verify_started.elapsed();

    println!(
        "pbs-chain-chunk recursive proof verified: preset={}, steps={}, recursive_tables={}, recursive_public_inputs={}",
        preset.name(),
        proof.base.step_count,
        proof.recursion.table_count(),
        proof.recursion.public_input_count()
    );
    println!(
        "prove_ms={}, prove_us={}, verify_ms={}, verify_us={}",
        prove_time.as_millis(),
        prove_time.as_micros(),
        verify_time.as_millis(),
        verify_time.as_micros()
    );
    println!(
        "base_public_inputs={}, base_private_inputs={}, output_body0={}, params_n={}",
        proof.base.public_inputs.len(),
        instance.private_inputs().len(),
        instance.output_accumulator.body[0].value(),
        params.lwe_dimension
    );

    Ok(())
}

fn prove_pbs_chain_prefix_recursive_demo(
    preset: ParamPreset,
    chunk_step_count: usize,
    requested_total_steps: Option<usize>,
) -> Result<(), Box<dyn Error>> {
    let params = preset.params();
    let total_steps = requested_total_steps.unwrap_or(params.lwe_dimension);
    if total_steps == 0 || total_steps > params.lwe_dimension {
        return Err(format!(
            "total step count must be in 1..={} for this preset",
            params.lwe_dimension
        )
        .into());
    }

    let (params, sk, evaluation_key, input, test_polynomial) = actual_pbs_materials(params);
    let body_exponent = tfheprus_core::mod_switch_to_exponent(&params, input.body);
    let initial_exponent = (params.exponent_modulus() - body_exponent) % params.exponent_modulus();
    let mut accumulator = GlweCiphertext::trivial(
        test_polynomial.poly.mul_xai(initial_exponent),
        params.glwe_dimension,
    );
    let mut bsk_digest = pbs_bsk_digest_initial();
    let mut mask_digest = pbs_mask_digest_initial();
    let mut total_prove_time = Duration::ZERO;
    let mut total_verify_time = Duration::ZERO;
    let mut chunk_count = 0usize;
    let mut max_base_public_inputs = 0usize;
    let mut max_base_private_inputs = 0usize;
    let mut max_recursive_public_inputs = 0usize;

    for chunk_start in (0..total_steps).step_by(chunk_step_count) {
        let chunk_end = (chunk_start + chunk_step_count).min(total_steps);
        let instance = ActualPbsChainChunkInstance::new(
            params.clone(),
            input.mask[chunk_start..chunk_end].to_vec(),
            accumulator.clone(),
            evaluation_key.bootstrapping_key[chunk_start..chunk_end].to_vec(),
            bsk_digest,
            mask_digest,
        );
        let base_public_inputs = instance.public_inputs().len();
        let base_private_inputs = instance.private_inputs().len();

        let prove_started = Instant::now();
        let proof = prove_recursive_actual_pbs_chain_chunk(&instance)?;
        let prove_time = prove_started.elapsed();

        let verify_started = Instant::now();
        let statement = ActualPbsChainChunkStatement::from_instance(&instance);
        verify_recursive_actual_pbs_chain_chunk_statement_proof(&statement, &proof)?;
        let verify_time = verify_started.elapsed();

        println!(
            "pbs-chain-prefix recursive chunk verified: preset={}, chunk={}, steps={}..{}, prove_us={}, verify_us={}, base_public_inputs={}, base_private_inputs={}, recursive_public_inputs={}",
            preset.name(),
            chunk_count,
            chunk_start,
            chunk_end,
            prove_time.as_micros(),
            verify_time.as_micros(),
            base_public_inputs,
            base_private_inputs,
            proof.recursion.public_input_count()
        );

        total_prove_time += prove_time;
        total_verify_time += verify_time;
        chunk_count += 1;
        max_base_public_inputs = max_base_public_inputs.max(base_public_inputs);
        max_base_private_inputs = max_base_private_inputs.max(base_private_inputs);
        max_recursive_public_inputs =
            max_recursive_public_inputs.max(proof.recursion.public_input_count());
        accumulator = instance.output_accumulator;
        bsk_digest = instance.bsk_digest_out;
        mask_digest = instance.mask_digest_out;
    }

    if total_steps == params.lwe_dimension {
        let evaluation_key_ntt = evaluation_key.to_ntt();
        let native_output =
            bootstrap_without_keyswitch_ntt(&params, &evaluation_key_ntt, &input, &test_polynomial);
        let chunked_output = sample_extract_index_zero(&accumulator);
        assert_eq!(chunked_output, native_output);
        println!(
            "full_prefix_output_message={}",
            chunked_output.decrypt(&params, &sk.extracted_output_lwe_key())
        );
    }

    println!(
        "pbs-chain-prefix recursive proof list verified: preset={}, total_steps={}, chunk_step_count={}, chunks={}, total_prove_ms={}, total_prove_us={}, total_verify_ms={}, total_verify_us={}, max_base_public_inputs={}, max_base_private_inputs={}, max_recursive_public_inputs={}, bsk_digest_out={}, mask_digest_out={}",
        preset.name(),
        total_steps,
        chunk_step_count,
        chunk_count,
        total_prove_time.as_millis(),
        total_prove_time.as_micros(),
        total_verify_time.as_millis(),
        total_verify_time.as_micros(),
        max_base_public_inputs,
        max_base_private_inputs,
        max_recursive_public_inputs,
        format_coefficients(&bsk_digest),
        format_coefficients(&mask_digest)
    );

    Ok(())
}

fn prove_pbs_chain_pair_aggregate_recursive_demo(
    preset: ParamPreset,
    chunk_step_count: usize,
) -> Result<(), Box<dyn Error>> {
    let params = preset.params();
    if chunk_step_count >= params.lwe_dimension {
        return Err(format!(
            "chunk step count must leave room for a second chunk, got {chunk_step_count} for n={}",
            params.lwe_dimension
        )
        .into());
    }

    let (params, _sk, evaluation_key, input, test_polynomial) = actual_pbs_materials(params);
    let body_exponent = tfheprus_core::mod_switch_to_exponent(&params, input.body);
    let initial_exponent = (params.exponent_modulus() - body_exponent) % params.exponent_modulus();
    let input_accumulator = GlweCiphertext::trivial(
        test_polynomial.poly.mul_xai(initial_exponent),
        params.glwe_dimension,
    );
    let left_end = chunk_step_count;
    let right_end = (chunk_step_count * 2).min(params.lwe_dimension);

    let left_instance = ActualPbsChainChunkInstance::new(
        params.clone(),
        input.mask[..left_end].to_vec(),
        input_accumulator,
        evaluation_key.bootstrapping_key[..left_end].to_vec(),
        pbs_bsk_digest_initial(),
        pbs_mask_digest_initial(),
    );
    let left_statement = ActualPbsChainChunkStatement::from_instance(&left_instance);

    let left_started = Instant::now();
    let left_proof = prove_recursive_actual_pbs_chain_chunk(&left_instance)?;
    let left_time = left_started.elapsed();

    let right_instance = ActualPbsChainChunkInstance::new(
        params.clone(),
        input.mask[left_end..right_end].to_vec(),
        left_instance.output_accumulator.clone(),
        evaluation_key.bootstrapping_key[left_end..right_end].to_vec(),
        left_instance.bsk_digest_out,
        left_instance.mask_digest_out,
    );
    let right_statement = ActualPbsChainChunkStatement::from_instance(&right_instance);

    let right_started = Instant::now();
    let right_proof = prove_recursive_actual_pbs_chain_chunk(&right_instance)?;
    let right_time = right_started.elapsed();

    let aggregate_started = Instant::now();
    let proof = prove_aggregated_recursive_actual_pbs_chain_chunk_pair(left_proof, right_proof)?;
    let aggregate_time = aggregate_started.elapsed();

    let verify_started = Instant::now();
    verify_aggregated_recursive_actual_pbs_chain_chunk_pair_statement_proof(
        &left_statement,
        &right_statement,
        &proof,
    )?;
    let verify_time = verify_started.elapsed();

    println!(
        "pbs-chain-pair aggregate recursive proof verified: preset={}, chunk_steps={}, covered_steps=0..{}, left_recursive_inputs={}, right_recursive_inputs={}, aggregate_tables={}, aggregate_public_inputs={}",
        preset.name(),
        chunk_step_count,
        right_end,
        proof.left.recursion.public_input_count(),
        proof.right.recursion.public_input_count(),
        proof.aggregation.table_count(),
        proof.aggregation.public_input_count()
    );
    println!(
        "left_prove_ms={}, left_prove_us={}, right_prove_ms={}, right_prove_us={}, aggregate_prove_ms={}, aggregate_prove_us={}, verify_ms={}, verify_us={}",
        left_time.as_millis(),
        left_time.as_micros(),
        right_time.as_millis(),
        right_time.as_micros(),
        aggregate_time.as_millis(),
        aggregate_time.as_micros(),
        verify_time.as_millis(),
        verify_time.as_micros()
    );
    println!(
        "left_base_private_inputs={}, right_base_private_inputs={}, output_body0={}, params_n={}",
        left_instance.private_inputs().len(),
        right_instance.private_inputs().len(),
        right_instance.output_accumulator.body[0].value(),
        params.lwe_dimension
    );

    Ok(())
}

fn prove_pbs_chain_tree_aggregate_recursive_demo(
    preset: ParamPreset,
    chunk_step_count: usize,
    requested_chunk_count: Option<usize>,
) -> Result<(), Box<dyn Error>> {
    let params = preset.params();
    let chunk_count = requested_chunk_count.unwrap_or(4);
    if chunk_count < 2 {
        return Err("chunk count must be at least 2".into());
    }
    let total_steps = chunk_step_count
        .checked_mul(chunk_count)
        .ok_or("chunk_steps * chunk_count overflowed")?;
    if total_steps == 0 || total_steps > params.lwe_dimension {
        return Err(format!(
            "chunk_steps * chunk_count must be in 1..={} for this preset",
            params.lwe_dimension
        )
        .into());
    }

    let (params, sk, evaluation_key, input, test_polynomial) = actual_pbs_materials(params);
    let body_exponent = tfheprus_core::mod_switch_to_exponent(&params, input.body);
    let initial_exponent = (params.exponent_modulus() - body_exponent) % params.exponent_modulus();
    let mut accumulator = GlweCiphertext::trivial(
        test_polynomial.poly.mul_xai(initial_exponent),
        params.glwe_dimension,
    );
    let mut bsk_digest = pbs_bsk_digest_initial();
    let mut mask_digest = pbs_mask_digest_initial();
    let mut statements = Vec::with_capacity(chunk_count);
    let mut leaves = Vec::with_capacity(chunk_count);
    let mut total_leaf_prove_time = Duration::ZERO;
    let mut max_base_private_inputs = 0usize;
    let mut max_recursive_public_inputs = 0usize;

    for chunk_index in 0..chunk_count {
        let chunk_start = chunk_index * chunk_step_count;
        let chunk_end = chunk_start + chunk_step_count;
        let instance = ActualPbsChainChunkInstance::new(
            params.clone(),
            input.mask[chunk_start..chunk_end].to_vec(),
            accumulator.clone(),
            evaluation_key.bootstrapping_key[chunk_start..chunk_end].to_vec(),
            bsk_digest,
            mask_digest,
        );
        let base_private_inputs = instance.private_inputs().len();
        let statement = ActualPbsChainChunkStatement::from_instance(&instance);

        let leaf_started = Instant::now();
        let proof = prove_recursive_actual_pbs_chain_chunk(&instance)?;
        let leaf_time = leaf_started.elapsed();
        println!(
            "pbs-chain-tree recursive leaf proved: preset={}, leaf={}, steps={}..{}, prove_us={}, base_private_inputs={}, recursive_public_inputs={}",
            preset.name(),
            chunk_index,
            chunk_start,
            chunk_end,
            leaf_time.as_micros(),
            base_private_inputs,
            proof.recursion.public_input_count()
        );

        total_leaf_prove_time += leaf_time;
        max_base_private_inputs = max_base_private_inputs.max(base_private_inputs);
        max_recursive_public_inputs =
            max_recursive_public_inputs.max(proof.recursion.public_input_count());
        accumulator = instance.output_accumulator;
        bsk_digest = instance.bsk_digest_out;
        mask_digest = instance.mask_digest_out;
        statements.push(statement);
        leaves.push(proof);
    }

    let aggregate_started = Instant::now();
    let proof = prove_aggregated_recursive_actual_pbs_chain_chunk_tree(leaves)?;
    let aggregate_time = aggregate_started.elapsed();

    let verify_started = Instant::now();
    verify_aggregated_recursive_actual_pbs_chain_chunk_tree_statement_proof(&statements, &proof)?;
    let verify_time = verify_started.elapsed();

    if total_steps == params.lwe_dimension {
        let evaluation_key_ntt = evaluation_key.to_ntt();
        let native_output =
            bootstrap_without_keyswitch_ntt(&params, &evaluation_key_ntt, &input, &test_polynomial);
        let chunked_output = sample_extract_index_zero(&accumulator);
        assert_eq!(chunked_output, native_output);
        println!(
            "full_tree_output_message={}",
            chunked_output.decrypt(&params, &sk.extracted_output_lwe_key())
        );
    }

    let layer_sizes = proof
        .layers
        .iter()
        .map(|layer| layer.len().to_string())
        .collect::<Vec<_>>()
        .join(",");
    println!(
        "pbs-chain-tree aggregate recursive proof verified: preset={}, chunk_steps={}, chunk_count={}, total_steps={}, leaves={}, layers={}, layer_sizes=[{}], root_tables={}, root_public_inputs={}",
        preset.name(),
        chunk_step_count,
        chunk_count,
        total_steps,
        proof.leaf_count(),
        proof.layer_count(),
        layer_sizes,
        proof.root_table_count().unwrap_or(0),
        proof.root_public_input_count().unwrap_or(0)
    );
    println!(
        "leaf_prove_ms={}, leaf_prove_us={}, aggregate_prove_ms={}, aggregate_prove_us={}, verify_ms={}, verify_us={}, max_base_private_inputs={}, max_recursive_public_inputs={}, bsk_digest_out={}, mask_digest_out={}",
        total_leaf_prove_time.as_millis(),
        total_leaf_prove_time.as_micros(),
        aggregate_time.as_millis(),
        aggregate_time.as_micros(),
        verify_time.as_millis(),
        verify_time.as_micros(),
        max_base_private_inputs,
        max_recursive_public_inputs,
        format_coefficients(&bsk_digest),
        format_coefficients(&mask_digest)
    );

    Ok(())
}

fn profile_pbs_chain_tree_demo(
    preset: ParamPreset,
    chunk_step_count: usize,
    requested_total_steps: Option<usize>,
) -> Result<(), Box<dyn Error>> {
    let params = preset.params();
    let total_steps = requested_total_steps.unwrap_or(params.lwe_dimension);
    if total_steps == 0 || total_steps > params.lwe_dimension {
        return Err(format!(
            "total step count must be in 1..={} for this preset",
            params.lwe_dimension
        )
        .into());
    }

    let chunk_count = total_steps.div_ceil(chunk_step_count);
    let full_chunk_count = total_steps / chunk_step_count;
    let last_chunk_steps = if total_steps.is_multiple_of(chunk_step_count) {
        chunk_step_count
    } else {
        total_steps % chunk_step_count
    };
    let layer_sizes = aggregation_layer_sizes(chunk_count);
    let aggregation_nodes = layer_sizes.iter().sum::<usize>();
    let chunk_public_inputs = estimated_chain_chunk_public_inputs(&params);
    let step_private_inputs = estimated_chain_chunk_step_private_inputs(&params);
    let full_chunk_private_inputs = estimated_chain_chunk_private_inputs(&params, chunk_step_count);
    let last_chunk_private_inputs = estimated_chain_chunk_private_inputs(&params, last_chunk_steps);
    let total_leaf_private_inputs = full_chunk_count
        .checked_mul(full_chunk_private_inputs)
        .and_then(|value| {
            if last_chunk_steps == chunk_step_count {
                Some(value)
            } else {
                value.checked_add(last_chunk_private_inputs)
            }
        })
        .ok_or("total private input estimate overflowed")?;

    print_param_line(preset.name(), &params);
    println!(
        "pbs-chain-tree profile: preset={}, total_steps={}, chunk_steps={}, chunk_count={}, full_chunk_count={}, last_chunk_steps={}, tree_depth={}, aggregation_nodes={}, layer_sizes=[{}]",
        preset.name(),
        total_steps,
        chunk_step_count,
        chunk_count,
        full_chunk_count,
        last_chunk_steps,
        layer_sizes.len(),
        aggregation_nodes,
        layer_sizes
            .iter()
            .map(|size| size.to_string())
            .collect::<Vec<_>>()
            .join(",")
    );
    println!(
        "leaf_shape: chunk_public_inputs={}, step_private_inputs={}, full_chunk_private_inputs={}, last_chunk_private_inputs={}, total_leaf_private_inputs={}, total_leaf_private_mib={:.2}",
        chunk_public_inputs,
        step_private_inputs,
        full_chunk_private_inputs,
        last_chunk_private_inputs,
        total_leaf_private_inputs,
        field_elements_to_mib(total_leaf_private_inputs)
    );

    Ok(())
}

fn profile_actual_pbs_demo(preset: ParamPreset) {
    let params = preset.params();
    let profile = ActualPbsCircuitProfile::estimate(&params, params.lwe_dimension);

    print_param_line(preset.name(), &params);
    println!(
        "actual-pbs profile: cmux_count={}, nonzero_rotations={}, bsk_public_inputs={}, public_inputs={}, public_input_mib={:.2}, private_inputs={}, private_input_mib={:.2}",
        profile.cmux_count,
        profile.nonzero_rotation_count,
        profile.bootstrapping_key_public_inputs,
        profile.public_inputs,
        field_elements_to_mib(profile.public_inputs),
        profile.private_inputs,
        field_elements_to_mib(profile.private_inputs),
    );
    println!(
        "decomposition: approximate={}, coeffs={}, private_inputs_per_coeff={}, torus_private_inputs={}",
        profile.approximate_decomposition,
        profile.decomposition_coefficients,
        profile.decomposition_private_inputs_per_coeff,
        profile.torus_private_inputs
    );
}

fn aggregation_layer_sizes(mut node_count: usize) -> Vec<usize> {
    let mut layer_sizes = Vec::new();
    while node_count > 1 {
        let pair_count = node_count / 2;
        layer_sizes.push(pair_count);
        node_count = pair_count + usize::from(!node_count.is_multiple_of(2));
    }
    layer_sizes
}

fn estimated_chain_chunk_public_inputs(params: &Params) -> usize {
    let glwe_field_count = (params.glwe_dimension + 1) * params.polynomial_size;
    2 * glwe_field_count + 4 * SELECTOR_DIGEST_WIDTH
}

fn estimated_chain_chunk_step_private_inputs(params: &Params) -> usize {
    let glwe_polynomial_count = params.glwe_dimension + 1;
    let ggsw_ntt_private_inputs = glwe_polynomial_count
        * params.decomposition_level_count
        * glwe_polynomial_count
        * params.polynomial_size;
    let decomposition_private_inputs_per_coeff = params.decomposition_level_count
        + if uses_exact_binary_decomposition(params) {
            0
        } else {
            2
        };
    let decomposition_private_inputs =
        glwe_polynomial_count * params.polynomial_size * decomposition_private_inputs_per_coeff;
    ggsw_ntt_private_inputs + 1 + 64 + decomposition_private_inputs
}

fn estimated_chain_chunk_private_inputs(params: &Params, step_count: usize) -> usize {
    step_count * estimated_chain_chunk_step_private_inputs(params)
}

fn uses_exact_binary_decomposition(params: &Params) -> bool {
    params.decomposition_base_log * params.decomposition_level_count == 64
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

    let coeff_result = if preset.runs_coeff_reference() {
        let started = Instant::now();
        let output =
            bootstrap_without_keyswitch(&params, &evaluation_key, &input, &test_polynomial);
        Some((output, started.elapsed()))
    } else {
        None
    };

    let key_started = Instant::now();
    let evaluation_key_ntt = evaluation_key.to_ntt();
    let key_ntt_time = key_started.elapsed();

    let ntt_started = Instant::now();
    let output =
        bootstrap_without_keyswitch_ntt(&params, &evaluation_key_ntt, &input, &test_polynomial);
    let ntt_time = ntt_started.elapsed();
    if let Some((coeff_output, _)) = &coeff_result {
        assert_eq!(&output, coeff_output);
    }

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
        optional_millis(coeff_result.as_ref().map(|(_, time)| *time)),
        optional_micros(coeff_result.as_ref().map(|(_, time)| *time)),
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

fn actual_pbs_first_step_instance(params: Params) -> (Params, ActualPbsStepInstance) {
    let (params, _sk, evaluation_key, input, test_polynomial) = actual_pbs_materials(params);
    let body_exponent = tfheprus_core::mod_switch_to_exponent(&params, input.body);
    let initial_exponent = (params.exponent_modulus() - body_exponent) % params.exponent_modulus();
    let input_accumulator = GlweCiphertext::trivial(
        test_polynomial.poly.mul_xai(initial_exponent),
        params.glwe_dimension,
    );
    let instance = ActualPbsStepInstance::new(
        params.clone(),
        input.mask[0],
        input_accumulator,
        evaluation_key.bootstrapping_key[0].clone(),
    );
    (params, instance)
}

fn actual_pbs_chain_chunk_instance(
    params: Params,
    step_count: usize,
) -> Result<(Params, ActualPbsChainChunkInstance), Box<dyn Error>> {
    if step_count == 0 || step_count > params.lwe_dimension {
        return Err(format!(
            "chunk step count must be in 1..={} for this preset",
            params.lwe_dimension
        )
        .into());
    }

    let (params, _sk, evaluation_key, input, test_polynomial) = actual_pbs_materials(params);
    let body_exponent = tfheprus_core::mod_switch_to_exponent(&params, input.body);
    let initial_exponent = (params.exponent_modulus() - body_exponent) % params.exponent_modulus();
    let input_accumulator = GlweCiphertext::trivial(
        test_polynomial.poly.mul_xai(initial_exponent),
        params.glwe_dimension,
    );
    let instance = ActualPbsChainChunkInstance::new(
        params.clone(),
        input.mask[..step_count].to_vec(),
        input_accumulator,
        evaluation_key.bootstrapping_key[..step_count].to_vec(),
        pbs_bsk_digest_initial(),
        pbs_mask_digest_initial(),
    );
    Ok((params, instance))
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
        "Usage: tfheprus [params|prove-poly-mul|prove-mul-xai|prove-sample-extract|prove-pbs-step [toy|moderate|paper-v1]|prove-pbs-step-private [toy|moderate|paper-v1]|prove-pbs-step-chain [toy|moderate|paper-v1]|prove-pbs-chain-chunk [toy|moderate|paper-v1] [steps]|prove-pbs-chain-chunk-recursive [toy|moderate|paper-v1] [steps]|prove-pbs-chain-prefix-recursive [toy|moderate|paper-v1] [chunk_steps] [total_steps]|prove-pbs-chain-pair-aggregate-recursive [toy|moderate|paper-v1] [chunk_steps]|prove-pbs-chain-tree-aggregate-recursive [toy|moderate|paper-v1] [chunk_steps] [chunk_count]|profile-pbs-chain-tree [toy|moderate|paper-v1] [chunk_steps] [total_steps]|prove-actual-pbs|profile-actual-pbs [toy|moderate|paper-v1]|run-actual-pbs-native [toy|moderate|paper-v1]]"
    );
}

#[derive(Clone, Copy, Debug)]
enum ParamPreset {
    Toy,
    Moderate,
    PaperV1,
}

impl ParamPreset {
    fn name(self) -> &'static str {
        match self {
            Self::Toy => "toy",
            Self::Moderate => "moderate",
            Self::PaperV1 => "paper-v1",
        }
    }

    fn params(self) -> Params {
        match self {
            Self::Toy => Params::toy(),
            Self::Moderate => Params::moderate_toy(),
            Self::PaperV1 => Params::paper_v1(),
        }
    }

    fn runs_coeff_reference(self) -> bool {
        !matches!(self, Self::PaperV1)
    }
}

fn parse_preset_arg(args: &[String]) -> Result<ParamPreset, Box<dyn Error>> {
    match args.get(2).map(String::as_str) {
        None | Some("toy") => Ok(ParamPreset::Toy),
        Some("moderate" | "moderate-toy" | "mid") => Ok(ParamPreset::Moderate),
        Some("paper" | "paper-v1") => Ok(ParamPreset::PaperV1),
        Some(other) => Err(format!("unknown parameter preset: {other}").into()),
    }
}

fn parse_prove_preset_arg(args: &[String]) -> Result<ParamPreset, Box<dyn Error>> {
    let preset = parse_preset_arg(args)?;
    if !matches!(preset, ParamPreset::Toy) {
        return Err(
            "prove-actual-pbs is currently enabled only for toy; use profile-actual-pbs and run-actual-pbs-native for larger presets until the recursive proof split is implemented".into(),
        );
    }
    Ok(preset)
}

fn parse_chunk_step_count_arg(args: &[String]) -> Result<usize, Box<dyn Error>> {
    match args.get(3) {
        None => Ok(2),
        Some(value) => {
            let parsed = value.parse::<usize>()?;
            if parsed == 0 {
                return Err("chunk step count must be nonzero".into());
            }
            Ok(parsed)
        }
    }
}

fn parse_optional_total_step_count_arg(args: &[String]) -> Result<Option<usize>, Box<dyn Error>> {
    match args.get(4) {
        None => Ok(None),
        Some(value) => {
            let parsed = value.parse::<usize>()?;
            if parsed == 0 {
                return Err("total step count must be nonzero".into());
            }
            Ok(Some(parsed))
        }
    }
}

fn parse_optional_chunk_count_arg(args: &[String]) -> Result<Option<usize>, Box<dyn Error>> {
    match args.get(4) {
        None => Ok(None),
        Some(value) => {
            let parsed = value.parse::<usize>()?;
            if parsed == 0 {
                return Err("chunk count must be nonzero".into());
            }
            Ok(Some(parsed))
        }
    }
}

fn field_elements_to_mib(field_elements: usize) -> f64 {
    field_elements as f64 * 8.0 / (1024.0 * 1024.0)
}

fn optional_millis(duration: Option<std::time::Duration>) -> String {
    duration.map_or_else(
        || "skipped".to_string(),
        |time| time.as_millis().to_string(),
    )
}

fn optional_micros(duration: Option<std::time::Duration>) -> String {
    duration.map_or_else(
        || "skipped".to_string(),
        |time| time.as_micros().to_string(),
    )
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
