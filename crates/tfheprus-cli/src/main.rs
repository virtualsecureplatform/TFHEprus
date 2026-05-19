use std::env;
use std::error::Error;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use tfheprus_circuits::{
    pbs_bsk_digest_initial, pbs_bsk_digest_update, pbs_mask_digest_initial, pbs_mask_digest_update,
    ActualPbsChainChunkInstance, ActualPbsCircuitProfile, ActualPbsInstance,
    ActualPbsStepChainInstance, ActualPbsStepInstance, ActualPbsStepPrivateInstance,
    MulXaiInstance, PolyMulInstance, SampleExtractInstance, SELECTOR_DIGEST_WIDTH,
};
use tfheprus_core::{
    bootstrap_without_keyswitch, bootstrap_without_keyswitch_ntt, ggsw::cmux_ntt,
    sample_extract_index_zero, EvaluationKey, GlweCiphertext, Goldilocks, LweCiphertext, Params,
    Polynomial, SecretKey, TestPolynomial, GOLDILOCKS_MODULUS,
};
use tfheprus_prover::{
    build_aggregated_recursive_actual_pbs_chain_frontier_proof,
    deserialize_aggregated_recursive_actual_pbs_chain_frontier_proof,
    deserialize_aggregated_recursive_actual_pbs_chain_node_proof,
    deserialize_aggregated_recursive_actual_pbs_chain_root_proof,
    deserialize_compact_aggregated_recursive_actual_pbs_chain_node_proof,
    deserialize_compact_aggregated_recursive_actual_pbs_chain_root_proof,
    deserialize_compact_recursive_actual_pbs_chain_chunk_proof,
    deserialize_recursive_actual_pbs_chain_chunk_proof, prove_actual_pbs,
    prove_actual_pbs_chain_chunk, prove_actual_pbs_step, prove_actual_pbs_step_chain,
    prove_actual_pbs_step_private, prove_aggregated_recursive_actual_pbs_chain_chunk_pair,
    prove_aggregated_recursive_actual_pbs_chain_chunk_tree,
    prove_aggregated_recursive_actual_pbs_chain_node_pair, prove_mul_xai, prove_poly_mul,
    prove_private_aggregated_recursive_actual_pbs_chain_chunk_tree,
    prove_private_aggregated_recursive_actual_pbs_chain_node_pair,
    prove_private_compact_aggregated_recursive_actual_pbs_chain_node_pair,
    prove_private_compact_recursive_actual_pbs_chain_chunk,
    prove_private_recursive_actual_pbs_chain_chunk, prove_recursive_actual_pbs_chain_chunk,
    prove_sample_extract, serialize_aggregated_recursive_actual_pbs_chain_frontier_proof,
    serialize_aggregated_recursive_actual_pbs_chain_node_proof,
    serialize_aggregated_recursive_actual_pbs_chain_root_proof,
    serialize_compact_aggregated_recursive_actual_pbs_chain_node_proof,
    serialize_compact_aggregated_recursive_actual_pbs_chain_root_proof,
    serialize_compact_recursive_actual_pbs_chain_chunk_proof,
    serialize_recursive_actual_pbs_chain_chunk_proof, verify_actual_pbs_chain_chunk_proof,
    verify_actual_pbs_proof, verify_actual_pbs_step_chain_proof,
    verify_actual_pbs_step_private_proof, verify_actual_pbs_step_proof,
    verify_aggregated_recursive_actual_pbs_chain_chunk_pair_statement_proof,
    verify_aggregated_recursive_actual_pbs_chain_chunk_tree_statement_proof,
    verify_aggregated_recursive_actual_pbs_chain_frontier_summary_proof,
    verify_aggregated_recursive_actual_pbs_chain_root_summary_proof,
    verify_compact_aggregated_recursive_actual_pbs_chain_root_summary_proof, verify_mul_xai_proof,
    verify_poly_mul_proof, verify_private_compact_recursive_actual_pbs_chain_chunk_statement_proof,
    verify_private_recursive_actual_pbs_chain_chunk_statement_proof,
    verify_recursive_actual_pbs_chain_chunk_statement_proof, verify_sample_extract_proof,
    ActualPbsChainChunkStatement, ActualPbsChainSummary,
    AggregatedRecursiveActualPbsChainNodeProof, CompactActualPbsChainSummary,
    CompactAggregatedRecursiveActualPbsChainNodeProof, CompactRecursiveActualPbsChainChunkProof,
    CompactRecursiveActualPbsChainNode, RecursiveActualPbsChainChunkProof,
    RecursiveActualPbsChainNode, RecursiveProofSizeBreakdown,
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
        Some("prove-pbs-chain-private-tree-aggregate-recursive") => {
            prove_pbs_chain_private_tree_aggregate_recursive_demo(
                parse_preset_arg(&args)?,
                parse_chunk_step_count_arg(&args)?,
                parse_optional_chunk_count_arg(&args)?,
            )?
        }
        Some("prove-pbs-chain-leaf-recursive") => prove_pbs_chain_leaf_recursive_artifact_demo(
            parse_preset_arg(&args)?,
            parse_chunk_step_count_arg(&args)?,
            parse_chunk_index_arg(&args)?,
            parse_required_arg(&args, 5, "leaf artifact output path")?,
            false,
        )?,
        Some("prove-pbs-chain-private-leaf-recursive") => {
            prove_pbs_chain_leaf_recursive_artifact_demo(
                parse_preset_arg(&args)?,
                parse_chunk_step_count_arg(&args)?,
                parse_chunk_index_arg(&args)?,
                parse_required_arg(&args, 5, "leaf artifact output path")?,
                true,
            )?
        }
        Some("prove-pbs-chain-leaves-recursive") => {
            prove_pbs_chain_leaves_recursive_artifacts_demo(
                parse_preset_arg(&args)?,
                parse_chunk_step_count_arg(&args)?,
                parse_required_chunk_count_arg(&args)?,
                parse_required_arg(&args, 5, "leaf artifact output directory")?,
                false,
                true,
            )?
        }
        Some("prove-pbs-chain-private-leaves-recursive") => {
            prove_pbs_chain_leaves_recursive_artifacts_demo(
                parse_preset_arg(&args)?,
                parse_chunk_step_count_arg(&args)?,
                parse_required_chunk_count_arg(&args)?,
                parse_required_arg(&args, 5, "leaf artifact output directory")?,
                true,
                true,
            )?
        }
        Some("prove-pbs-chain-private-leaves-recursive-fast") => {
            prove_pbs_chain_leaves_recursive_artifacts_demo(
                parse_preset_arg(&args)?,
                parse_chunk_step_count_arg(&args)?,
                parse_required_chunk_count_arg(&args)?,
                parse_required_arg(&args, 5, "leaf artifact output directory")?,
                true,
                false,
            )?
        }
        Some("prove-pbs-chain-private-leaves-compact-fast") => {
            prove_pbs_chain_private_compact_leaves_recursive_artifacts_demo(
                parse_preset_arg(&args)?,
                parse_chunk_step_count_arg(&args)?,
                parse_required_chunk_count_arg(&args)?,
                parse_required_arg(&args, 5, "leaf artifact output directory")?,
                false,
            )?
        }
        Some("aggregate-pbs-chain-leaves-recursive") => {
            aggregate_pbs_chain_leaf_artifacts_recursive_demo(
                parse_required_arg(&args, 2, "root artifact output path")?,
                parse_repeated_args(&args, 3, "leaf artifact paths")?,
            )?
        }
        Some("aggregate-pbs-chain-leaf-dir-recursive") => {
            aggregate_pbs_chain_leaf_artifact_dir_recursive_demo(
                parse_required_arg(&args, 2, "root artifact output path")?,
                parse_required_arg(&args, 3, "leaf artifact directory")?,
                parse_optional_leaf_count_arg(&args)?,
                false,
            )?
        }
        Some("aggregate-pbs-chain-private-leaf-dir-recursive") => {
            aggregate_pbs_chain_leaf_artifact_dir_recursive_demo(
                parse_required_arg(&args, 2, "root artifact output path")?,
                parse_required_arg(&args, 3, "leaf artifact directory")?,
                parse_optional_leaf_count_arg(&args)?,
                true,
            )?
        }
        Some("aggregate-pbs-chain-private-compact-leaf-dir-recursive") => {
            aggregate_pbs_chain_private_compact_leaf_artifact_dir_recursive_demo(
                parse_required_arg(&args, 2, "root artifact output path")?,
                parse_required_arg(&args, 3, "leaf artifact directory")?,
                parse_optional_leaf_count_arg(&args)?,
            )?
        }
        Some("package-pbs-chain-frontier-recursive") => {
            package_pbs_chain_frontier_artifacts_recursive_demo(
                parse_required_arg(&args, 2, "frontier artifact output path")?,
                parse_repeated_args(&args, 3, "aggregate artifact paths")?,
            )?
        }
        Some("package-pbs-chain-frontier-dir-recursive") => {
            package_pbs_chain_frontier_artifact_dir_recursive_demo(
                parse_required_arg(&args, 2, "frontier artifact output path")?,
                parse_required_arg(&args, 3, "aggregate artifact directory")?,
            )?
        }
        Some("verify-pbs-chain-root-artifact-recursive") => {
            verify_pbs_chain_root_artifact_recursive_demo(parse_required_arg(
                &args,
                2,
                "root artifact path",
            )?)?
        }
        Some("verify-pbs-chain-compact-root-artifact-recursive") => {
            verify_pbs_chain_compact_root_artifact_recursive_demo(parse_required_arg(
                &args,
                2,
                "root artifact path",
            )?)?
        }
        Some("verify-pbs-chain-frontier-artifact-recursive") => {
            verify_pbs_chain_frontier_artifact_recursive_demo(parse_required_arg(
                &args,
                2,
                "frontier artifact path",
            )?)?
        }
        Some("inspect-pbs-chain-artifact") => inspect_pbs_chain_artifact_demo(
            parse_required_arg(&args, 2, "artifact kind")?,
            parse_required_arg(&args, 3, "artifact path")?,
        )?,
        Some("bench-pbs-chain-private-recursive") => bench_pbs_chain_private_recursive_demo(
            parse_preset_arg(&args)?,
            parse_chunk_step_count_arg(&args)?,
            parse_required_chunk_count_arg(&args)?,
            parse_required_arg(&args, 5, "benchmark artifact directory")?,
            false,
        )?,
        Some("bench-pbs-chain-private-compact") => bench_pbs_chain_private_recursive_demo(
            parse_preset_arg(&args)?,
            parse_chunk_step_count_arg(&args)?,
            parse_required_chunk_count_arg(&args)?,
            parse_required_arg(&args, 5, "benchmark artifact directory")?,
            true,
        )?,
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
        "pbs-chain-chunk recursive proof verified: preset={}, steps={}, recursive_tables={}, recursive_public_inputs={}, chain_summary_fields={}",
        preset.name(),
        proof.base.step_count,
        proof.recursion.table_count(),
        proof.recursion.public_input_count(),
        proof.chain_summary.field_values().len()
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
        "pbs-chain-pair aggregate recursive proof verified: preset={}, chunk_steps={}, covered_steps=0..{}, left_recursive_inputs={}, right_recursive_inputs={}, aggregate_tables={}, aggregate_public_inputs={}, chain_summary_fields={}",
        preset.name(),
        chunk_step_count,
        right_end,
        proof.left.recursion.public_input_count(),
        proof.right.recursion.public_input_count(),
        proof.aggregation.table_count(),
        proof.aggregation.public_input_count(),
        proof.chain_summary.field_values().len()
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
    let root_table_count = proof.root_table_count().unwrap_or(0);
    let root_public_input_count = proof.root_public_input_count().unwrap_or(0);
    let chain_summary_fields = proof.chain_summary.field_values().len();
    let leaf_count = proof.leaf_count();
    let layer_count = proof.layer_count();
    let root_summary = proof.chain_summary.clone();
    let root_proof = proof.into_root_proof()?;
    let root_proof_bytes = serialize_aggregated_recursive_actual_pbs_chain_root_proof(&root_proof)?;
    let decoded_root_proof =
        deserialize_aggregated_recursive_actual_pbs_chain_root_proof(&root_proof_bytes)?;
    let root_verify_started = Instant::now();
    verify_aggregated_recursive_actual_pbs_chain_root_summary_proof(
        &root_summary,
        &decoded_root_proof,
    )?;
    let root_verify_time = root_verify_started.elapsed();
    println!(
        "pbs-chain-tree aggregate recursive proof verified: preset={}, chunk_steps={}, chunk_count={}, total_steps={}, leaves={}, layers={}, layer_sizes=[{}], root_tables={}, root_public_inputs={}, chain_summary_fields={}",
        preset.name(),
        chunk_step_count,
        chunk_count,
        total_steps,
        leaf_count,
        layer_count,
        layer_sizes,
        root_table_count,
        root_public_input_count,
        chain_summary_fields
    );
    println!(
        "leaf_prove_ms={}, leaf_prove_us={}, aggregate_prove_ms={}, aggregate_prove_us={}, verify_ms={}, verify_us={}, root_verify_ms={}, root_verify_us={}, root_proof_bytes={}, max_base_private_inputs={}, max_recursive_public_inputs={}, bsk_digest_out={}, mask_digest_out={}",
        total_leaf_prove_time.as_millis(),
        total_leaf_prove_time.as_micros(),
        aggregate_time.as_millis(),
        aggregate_time.as_micros(),
        verify_time.as_millis(),
        verify_time.as_micros(),
        root_verify_time.as_millis(),
        root_verify_time.as_micros(),
        root_proof_bytes.len(),
        max_base_private_inputs,
        max_recursive_public_inputs,
        format_coefficients(&bsk_digest),
        format_coefficients(&mask_digest)
    );

    Ok(())
}

fn prove_pbs_chain_private_tree_aggregate_recursive_demo(
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

        let leaf_started = Instant::now();
        let proof = prove_private_recursive_actual_pbs_chain_chunk(&instance)?;
        let leaf_time = leaf_started.elapsed();
        println!(
            "pbs-chain-private-tree recursive leaf proved: preset={}, leaf={}, steps={}..{}, prove_us={}, base_private_inputs={}, recursive_public_inputs={}",
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
        leaves.push(proof);
    }

    let aggregate_started = Instant::now();
    let proof = prove_private_aggregated_recursive_actual_pbs_chain_chunk_tree(leaves)?;
    let aggregate_time = aggregate_started.elapsed();

    if total_steps == params.lwe_dimension {
        let evaluation_key_ntt = evaluation_key.to_ntt();
        let native_output =
            bootstrap_without_keyswitch_ntt(&params, &evaluation_key_ntt, &input, &test_polynomial);
        let chunked_output = sample_extract_index_zero(&accumulator);
        assert_eq!(chunked_output, native_output);
        println!(
            "full_private_tree_output_message={}",
            chunked_output.decrypt(&params, &sk.extracted_output_lwe_key())
        );
    }

    let layer_sizes = proof
        .layers
        .iter()
        .map(|layer| layer.len().to_string())
        .collect::<Vec<_>>()
        .join(",");
    let root_table_count = proof.root_table_count().unwrap_or(0);
    let root_public_input_count = proof.root_public_input_count().unwrap_or(0);
    let chain_summary_fields = proof.chain_summary.field_values().len();
    let leaf_count = proof.leaf_count();
    let layer_count = proof.layer_count();
    let root_summary = proof.chain_summary.clone();
    let root_proof = proof.into_root_proof()?;
    let root_proof_bytes = serialize_aggregated_recursive_actual_pbs_chain_root_proof(&root_proof)?;
    let decoded_root_proof =
        deserialize_aggregated_recursive_actual_pbs_chain_root_proof(&root_proof_bytes)?;
    let root_verify_started = Instant::now();
    verify_aggregated_recursive_actual_pbs_chain_root_summary_proof(
        &root_summary,
        &decoded_root_proof,
    )?;
    let root_verify_time = root_verify_started.elapsed();
    println!(
        "pbs-chain-private-tree aggregate recursive proof verified: preset={}, chunk_steps={}, chunk_count={}, total_steps={}, leaves={}, layers={}, layer_sizes=[{}], root_tables={}, root_public_inputs={}, chain_summary_fields={}",
        preset.name(),
        chunk_step_count,
        chunk_count,
        total_steps,
        leaf_count,
        layer_count,
        layer_sizes,
        root_table_count,
        root_public_input_count,
        chain_summary_fields
    );
    println!(
        "leaf_prove_ms={}, leaf_prove_us={}, aggregate_prove_ms={}, aggregate_prove_us={}, root_verify_ms={}, root_verify_us={}, root_proof_bytes={}, max_base_private_inputs={}, max_recursive_public_inputs={}, bsk_digest_out={}, mask_digest_out={}",
        total_leaf_prove_time.as_millis(),
        total_leaf_prove_time.as_micros(),
        aggregate_time.as_millis(),
        aggregate_time.as_micros(),
        root_verify_time.as_millis(),
        root_verify_time.as_micros(),
        root_proof_bytes.len(),
        max_base_private_inputs,
        max_recursive_public_inputs,
        format_coefficients(&bsk_digest),
        format_coefficients(&mask_digest)
    );

    Ok(())
}

fn prove_pbs_chain_leaf_recursive_artifact_demo(
    preset: ParamPreset,
    chunk_step_count: usize,
    chunk_index: usize,
    output_path: &str,
    private_recursive: bool,
) -> Result<(), Box<dyn Error>> {
    let instance_started = Instant::now();
    let (chunk_start, chunk_end, instance) =
        actual_pbs_chain_chunk_instance_at(preset.params(), chunk_step_count, chunk_index)?;
    let instance_time = instance_started.elapsed();
    let base_private_inputs = instance.private_inputs().len();
    let statement = ActualPbsChainChunkStatement::from_instance(&instance);

    let prove_started = Instant::now();
    let proof = if private_recursive {
        prove_private_recursive_actual_pbs_chain_chunk(&instance)?
    } else {
        prove_recursive_actual_pbs_chain_chunk(&instance)?
    };
    let prove_time = prove_started.elapsed();

    let verify_started = Instant::now();
    verify_recursive_actual_pbs_chain_artifact_statement(&statement, &proof, private_recursive)?;
    let verify_time = verify_started.elapsed();

    let artifact = serialize_recursive_actual_pbs_chain_chunk_proof(&proof)?;
    fs::write(output_path, &artifact)?;

    println!(
        "pbs-chain recursive leaf artifact written: preset={}, private_recursive={}, chunk_steps={}, chunk_index={}, steps={}..{}, artifact={}, artifact_bytes={}, instance_ms={}, instance_us={}, prove_ms={}, prove_us={}, verify_ms={}, verify_us={}, base_private_inputs={}, recursive_public_inputs={}, chain_summary_fields={}",
        preset.name(),
        private_recursive,
        chunk_step_count,
        chunk_index,
        chunk_start,
        chunk_end,
        output_path,
        artifact.len(),
        instance_time.as_millis(),
        instance_time.as_micros(),
        prove_time.as_millis(),
        prove_time.as_micros(),
        verify_time.as_millis(),
        verify_time.as_micros(),
        base_private_inputs,
        proof.recursion.public_input_count(),
        proof.chain_summary.field_values().len()
    );

    Ok(())
}

fn verify_recursive_actual_pbs_chain_artifact_statement(
    statement: &ActualPbsChainChunkStatement,
    proof: &RecursiveActualPbsChainChunkProof,
    private_recursive: bool,
) -> Result<(), tfheprus_prover::ProofError> {
    if private_recursive {
        verify_private_recursive_actual_pbs_chain_chunk_statement_proof(statement, proof)
    } else {
        verify_recursive_actual_pbs_chain_chunk_statement_proof(statement, proof)
    }
}

fn prove_pbs_chain_leaves_recursive_artifacts_demo(
    preset: ParamPreset,
    chunk_step_count: usize,
    chunk_count: usize,
    output_dir: &str,
    private_recursive: bool,
    verify_leaf_artifacts: bool,
) -> Result<(), Box<dyn Error>> {
    if chunk_count < 2 {
        return Err("chunk count must be at least 2".into());
    }
    let params = preset.params();
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

    fs::create_dir_all(output_dir)?;
    let output_dir = Path::new(output_dir);
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
    let mut written_count = 0usize;
    let mut reused_count = 0usize;
    let mut max_base_private_inputs = 0usize;
    let mut max_recursive_public_inputs = 0usize;
    let mut total_artifact_bytes = 0usize;

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
        let expected_summary = ActualPbsChainSummary::from_chunk_statement(&statement)?;
        let artifact_path = output_dir.join(format!("leaf-{chunk_index:05}.bin"));

        let (proof, artifact_len, action, prove_time, verify_time) = if artifact_path.exists() {
            let bytes = fs::read(&artifact_path)?;
            let proof = deserialize_recursive_actual_pbs_chain_chunk_proof(&bytes)?;
            let verify_time = if verify_leaf_artifacts {
                let verify_started = Instant::now();
                verify_recursive_actual_pbs_chain_artifact_statement(
                    &statement,
                    &proof,
                    private_recursive,
                )
                .map_err(|error| {
                    format!(
                        "existing leaf artifact {} failed verification: {error}",
                        artifact_path.display()
                    )
                })?;
                verify_started.elapsed()
            } else {
                if proof.chain_summary != expected_summary {
                    return Err(format!(
                        "existing leaf artifact {} has wrong chain summary",
                        artifact_path.display()
                    )
                    .into());
                }
                Duration::ZERO
            };
            (proof, bytes.len(), "reused", Duration::ZERO, verify_time)
        } else {
            let prove_started = Instant::now();
            let proof = if private_recursive {
                prove_private_recursive_actual_pbs_chain_chunk(&instance)?
            } else {
                prove_recursive_actual_pbs_chain_chunk(&instance)?
            };
            let prove_time = prove_started.elapsed();
            let verify_time = if verify_leaf_artifacts {
                let verify_started = Instant::now();
                verify_recursive_actual_pbs_chain_artifact_statement(
                    &statement,
                    &proof,
                    private_recursive,
                )?;
                verify_started.elapsed()
            } else {
                if proof.chain_summary != expected_summary {
                    return Err("new leaf proof has wrong chain summary".into());
                }
                Duration::ZERO
            };
            let artifact = serialize_recursive_actual_pbs_chain_chunk_proof(&proof)?;
            fs::write(&artifact_path, &artifact)?;
            (proof, artifact.len(), "written", prove_time, verify_time)
        };

        if action == "written" {
            written_count += 1;
        } else {
            reused_count += 1;
        }
        total_prove_time += prove_time;
        total_verify_time += verify_time;
        total_artifact_bytes += artifact_len;
        max_base_private_inputs = max_base_private_inputs.max(base_private_inputs);
        max_recursive_public_inputs =
            max_recursive_public_inputs.max(proof.recursion.public_input_count());
        accumulator = instance.output_accumulator;
        bsk_digest = instance.bsk_digest_out;
        mask_digest = instance.mask_digest_out;

        println!(
            "pbs-chain recursive leaf artifact {action}: preset={}, private_recursive={}, verify_leaf_artifacts={}, chunk={}, steps={}..{}, artifact={}, artifact_bytes={}, prove_us={}, verify_us={}, base_private_inputs={}, recursive_public_inputs={}",
            preset.name(),
            private_recursive,
            verify_leaf_artifacts,
            chunk_index,
            chunk_start,
            chunk_end,
            artifact_path.display(),
            artifact_len,
            prove_time.as_micros(),
            verify_time.as_micros(),
            base_private_inputs,
            proof.recursion.public_input_count()
        );
    }

    if total_steps == params.lwe_dimension {
        let evaluation_key_ntt = evaluation_key.to_ntt();
        let native_output =
            bootstrap_without_keyswitch_ntt(&params, &evaluation_key_ntt, &input, &test_polynomial);
        let chunked_output = sample_extract_index_zero(&accumulator);
        assert_eq!(chunked_output, native_output);
        println!(
            "full_leaf_checkpoint_output_message={}",
            chunked_output.decrypt(&params, &sk.extracted_output_lwe_key())
        );
    }

    println!(
        "pbs-chain recursive leaf artifacts ready: preset={}, private_recursive={}, verify_leaf_artifacts={}, chunk_steps={}, chunk_count={}, total_steps={}, output_dir={}, written={}, reused={}, total_artifact_bytes={}, total_prove_ms={}, total_prove_us={}, total_verify_ms={}, total_verify_us={}, max_base_private_inputs={}, max_recursive_public_inputs={}, bsk_digest_out={}, mask_digest_out={}",
        preset.name(),
        private_recursive,
        verify_leaf_artifacts,
        chunk_step_count,
        chunk_count,
        total_steps,
        output_dir.display(),
        written_count,
        reused_count,
        total_artifact_bytes,
        total_prove_time.as_millis(),
        total_prove_time.as_micros(),
        total_verify_time.as_millis(),
        total_verify_time.as_micros(),
        max_base_private_inputs,
        max_recursive_public_inputs,
        format_coefficients(&bsk_digest),
        format_coefficients(&mask_digest)
    );

    Ok(())
}

fn prove_pbs_chain_private_compact_leaves_recursive_artifacts_demo(
    preset: ParamPreset,
    chunk_step_count: usize,
    chunk_count: usize,
    output_dir: &str,
    verify_leaf_artifacts: bool,
) -> Result<(), Box<dyn Error>> {
    if chunk_count < 2 {
        return Err("chunk count must be at least 2".into());
    }
    let params = preset.params();
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

    fs::create_dir_all(output_dir)?;
    let output_dir = Path::new(output_dir);
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
    let mut written_count = 0usize;
    let mut reused_count = 0usize;
    let mut max_base_private_inputs = 0usize;
    let mut max_recursive_public_inputs = 0usize;
    let mut total_artifact_bytes = 0usize;

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
        let expected_summary = CompactActualPbsChainSummary::from_chunk_statement(&statement)?;
        let artifact_path = output_dir.join(format!("leaf-{chunk_index:05}.bin"));

        let (proof, artifact_len, action, prove_time, verify_time) = if artifact_path.exists() {
            let bytes = fs::read(&artifact_path)?;
            let proof = deserialize_compact_recursive_actual_pbs_chain_chunk_proof(&bytes)?;
            let verify_time = if verify_leaf_artifacts {
                let verify_started = Instant::now();
                verify_private_compact_recursive_actual_pbs_chain_chunk_statement_proof(
                    &statement, &proof,
                )
                .map_err(|error| {
                    format!(
                        "existing compact leaf artifact {} failed verification: {error}",
                        artifact_path.display()
                    )
                })?;
                verify_started.elapsed()
            } else {
                if proof.chain_summary != expected_summary {
                    return Err(format!(
                        "existing compact leaf artifact {} has wrong chain summary",
                        artifact_path.display()
                    )
                    .into());
                }
                Duration::ZERO
            };
            (proof, bytes.len(), "reused", Duration::ZERO, verify_time)
        } else {
            let prove_started = Instant::now();
            let proof = prove_private_compact_recursive_actual_pbs_chain_chunk(&instance)?;
            let prove_time = prove_started.elapsed();
            let verify_time = if verify_leaf_artifacts {
                let verify_started = Instant::now();
                verify_private_compact_recursive_actual_pbs_chain_chunk_statement_proof(
                    &statement, &proof,
                )?;
                verify_started.elapsed()
            } else {
                if proof.chain_summary != expected_summary {
                    return Err("new compact leaf proof has wrong chain summary".into());
                }
                Duration::ZERO
            };
            let artifact = serialize_compact_recursive_actual_pbs_chain_chunk_proof(&proof)?;
            fs::write(&artifact_path, &artifact)?;
            (proof, artifact.len(), "written", prove_time, verify_time)
        };

        if action == "written" {
            written_count += 1;
        } else {
            reused_count += 1;
        }
        total_prove_time += prove_time;
        total_verify_time += verify_time;
        total_artifact_bytes += artifact_len;
        max_base_private_inputs = max_base_private_inputs.max(base_private_inputs);
        max_recursive_public_inputs =
            max_recursive_public_inputs.max(proof.recursion.public_input_count());
        accumulator = instance.output_accumulator;
        bsk_digest = instance.bsk_digest_out;
        mask_digest = instance.mask_digest_out;

        println!(
            "pbs-chain private compact recursive leaf artifact {action}: preset={}, verify_leaf_artifacts={}, chunk={}, steps={}..{}, artifact={}, artifact_bytes={}, prove_us={}, verify_us={}, base_private_inputs={}, recursive_public_inputs={}, compact_summary_fields={}",
            preset.name(),
            verify_leaf_artifacts,
            chunk_index,
            chunk_start,
            chunk_end,
            artifact_path.display(),
            artifact_len,
            prove_time.as_micros(),
            verify_time.as_micros(),
            base_private_inputs,
            proof.recursion.public_input_count(),
            proof.chain_summary.field_values().len()
        );
    }

    if total_steps == params.lwe_dimension {
        let evaluation_key_ntt = evaluation_key.to_ntt();
        let native_output =
            bootstrap_without_keyswitch_ntt(&params, &evaluation_key_ntt, &input, &test_polynomial);
        let chunked_output = sample_extract_index_zero(&accumulator);
        assert_eq!(chunked_output, native_output);
        println!(
            "full_compact_leaf_checkpoint_output_message={}",
            chunked_output.decrypt(&params, &sk.extracted_output_lwe_key())
        );
    }

    println!(
        "pbs-chain private compact recursive leaf artifacts ready: preset={}, verify_leaf_artifacts={}, chunk_steps={}, chunk_count={}, total_steps={}, output_dir={}, written={}, reused={}, total_artifact_bytes={}, total_prove_ms={}, total_prove_us={}, total_verify_ms={}, total_verify_us={}, max_base_private_inputs={}, max_recursive_public_inputs={}, bsk_digest_out={}, mask_digest_out={}",
        preset.name(),
        verify_leaf_artifacts,
        chunk_step_count,
        chunk_count,
        total_steps,
        output_dir.display(),
        written_count,
        reused_count,
        total_artifact_bytes,
        total_prove_time.as_millis(),
        total_prove_time.as_micros(),
        total_verify_time.as_millis(),
        total_verify_time.as_micros(),
        max_base_private_inputs,
        max_recursive_public_inputs,
        format_coefficients(&bsk_digest),
        format_coefficients(&mask_digest)
    );

    Ok(())
}

fn aggregate_pbs_chain_leaf_artifacts_recursive_demo(
    output_path: &str,
    leaf_paths: Vec<String>,
) -> Result<(), Box<dyn Error>> {
    if leaf_paths.len() < 2 {
        return Err("at least two leaf artifacts are required".into());
    }

    let read_started = Instant::now();
    let mut leaves = Vec::with_capacity(leaf_paths.len());
    for path in &leaf_paths {
        let bytes = fs::read(path)?;
        leaves.push(deserialize_recursive_actual_pbs_chain_chunk_proof(&bytes)?);
    }
    let read_time = read_started.elapsed();

    let statements = leaves
        .iter()
        .map(|leaf| leaf.base.public_statement())
        .collect::<Vec<_>>();
    tfheprus_prover::validate_actual_pbs_chain_chunk_statements(&statements)
        .map_err(|error| format!("leaf artifact continuity check failed: {error}"))?;
    let leaf_count = leaves.len();
    let full_wrapper_verify = leaf_count <= 8;
    if full_wrapper_verify {
        for (index, (statement, leaf)) in statements.iter().zip(leaves.iter()).enumerate() {
            verify_recursive_actual_pbs_chain_chunk_statement_proof(statement, leaf)
                .map_err(|error| format!("leaf artifact {index} verification failed: {error}"))?;
        }
    }
    let max_base_public_inputs = leaves
        .iter()
        .map(|leaf| leaf.base.public_inputs.len())
        .max()
        .unwrap_or(0);
    let max_recursive_public_inputs = leaves
        .iter()
        .map(|leaf| leaf.recursion.public_input_count())
        .max()
        .unwrap_or(0);

    let aggregate_started = Instant::now();
    let proof = prove_aggregated_recursive_actual_pbs_chain_chunk_tree(leaves)
        .map_err(|error| format!("aggregate leaf artifacts: {error}"))?;
    let aggregate_time = aggregate_started.elapsed();

    let verify_time = if full_wrapper_verify {
        let verify_started = Instant::now();
        verify_aggregated_recursive_actual_pbs_chain_chunk_tree_statement_proof(
            &statements,
            &proof,
        )
        .map_err(|error| format!("verify aggregated leaf artifacts: {error}"))?;
        Some(verify_started.elapsed())
    } else {
        None
    };

    let layer_sizes = proof
        .layers
        .iter()
        .map(|layer| layer.len().to_string())
        .collect::<Vec<_>>()
        .join(",");
    let root_table_count = proof.root_table_count().unwrap_or(0);
    let root_public_input_count = proof.root_public_input_count().unwrap_or(0);
    let chain_summary_fields = proof.chain_summary.field_values().len();
    let layer_count = proof.layer_count();
    let root_summary = proof.chain_summary.clone();
    let root_proof = proof.into_root_proof()?;
    let root_artifact = serialize_aggregated_recursive_actual_pbs_chain_root_proof(&root_proof)?;
    let decoded_root_proof =
        deserialize_aggregated_recursive_actual_pbs_chain_root_proof(&root_artifact)?;
    let root_verify_started = Instant::now();
    verify_aggregated_recursive_actual_pbs_chain_root_summary_proof(
        &root_summary,
        &decoded_root_proof,
    )?;
    let root_verify_time = root_verify_started.elapsed();
    fs::write(output_path, &root_artifact)?;

    println!(
        "pbs-chain leaf artifacts aggregated: output={}, leaves={}, layers={}, layer_sizes=[{}], root_tables={}, root_public_inputs={}, chain_summary_fields={}",
        output_path,
        leaf_count,
        layer_count,
        layer_sizes,
        root_table_count,
        root_public_input_count,
        chain_summary_fields
    );
    println!(
        "read_ms={}, read_us={}, aggregate_ms={}, aggregate_us={}, verify_ms={}, verify_us={}, root_verify_ms={}, root_verify_us={}, root_artifact_bytes={}, max_base_public_inputs={}, max_recursive_public_inputs={}",
        read_time.as_millis(),
        read_time.as_micros(),
        aggregate_time.as_millis(),
        aggregate_time.as_micros(),
        optional_millis(verify_time),
        optional_micros(verify_time),
        root_verify_time.as_millis(),
        root_verify_time.as_micros(),
        root_artifact.len(),
        max_base_public_inputs,
        max_recursive_public_inputs
    );

    Ok(())
}

fn aggregate_pbs_chain_leaf_artifact_dir_recursive_demo(
    output_path: &str,
    leaf_dir: &str,
    leaf_count: Option<usize>,
    private_recursive: bool,
) -> Result<(), Box<dyn Error>> {
    let leaf_paths = leaf_artifact_paths_from_dir(leaf_dir, leaf_count)?;
    let checkpoint_dir = if private_recursive {
        Path::new(leaf_dir).join("private-aggregation")
    } else {
        Path::new(leaf_dir).join("aggregation")
    };
    aggregate_pbs_chain_leaf_artifacts_checkpointed_recursive_demo(
        output_path,
        leaf_paths,
        &checkpoint_dir,
        private_recursive,
    )
}

fn aggregate_pbs_chain_private_compact_leaf_artifact_dir_recursive_demo(
    output_path: &str,
    leaf_dir: &str,
    leaf_count: Option<usize>,
) -> Result<(), Box<dyn Error>> {
    let leaf_paths = leaf_artifact_paths_from_dir(leaf_dir, leaf_count)?;
    let checkpoint_dir = Path::new(leaf_dir).join("private-compact-aggregation");
    aggregate_pbs_chain_private_compact_leaf_artifacts_checkpointed_recursive_demo(
        output_path,
        leaf_paths,
        &checkpoint_dir,
    )
}

#[derive(Clone)]
enum RecursivePbsChainNodeArtifact {
    Leaf(PathBuf),
    Aggregate(PathBuf),
}

enum LoadedRecursivePbsChainNode {
    Leaf(Box<RecursiveActualPbsChainChunkProof>),
    Aggregate(Box<AggregatedRecursiveActualPbsChainNodeProof>),
}

impl RecursivePbsChainNodeArtifact {
    fn path(&self) -> &Path {
        match self {
            Self::Leaf(path) | Self::Aggregate(path) => path,
        }
    }
}

impl LoadedRecursivePbsChainNode {
    fn chain_summary(&self) -> &ActualPbsChainSummary {
        match self {
            Self::Leaf(proof) => &proof.chain_summary,
            Self::Aggregate(proof) => &proof.chain_summary,
        }
    }

    fn as_prover_node(&self) -> RecursiveActualPbsChainNode<'_> {
        match self {
            Self::Leaf(proof) => RecursiveActualPbsChainNode::Leaf(proof),
            Self::Aggregate(proof) => RecursiveActualPbsChainNode::Aggregate(proof),
        }
    }
}

fn aggregate_pbs_chain_leaf_artifacts_checkpointed_recursive_demo(
    output_path: &str,
    leaf_paths: Vec<String>,
    checkpoint_dir: &Path,
    private_recursive: bool,
) -> Result<(), Box<dyn Error>> {
    if leaf_paths.len() < 2 {
        return Err("at least two leaf artifacts are required".into());
    }

    fs::create_dir_all(checkpoint_dir)?;
    let read_started = Instant::now();
    let mut statements = Vec::with_capacity(leaf_paths.len());
    let mut current_nodes = Vec::with_capacity(leaf_paths.len());
    let mut current_summaries = Vec::with_capacity(leaf_paths.len());
    let mut total_leaf_artifact_bytes = 0usize;
    let mut max_base_public_inputs = 0usize;
    let mut max_recursive_public_inputs = 0usize;
    for path in leaf_paths {
        let path = PathBuf::from(path);
        let bytes = fs::read(&path)?;
        total_leaf_artifact_bytes = total_leaf_artifact_bytes
            .checked_add(bytes.len())
            .ok_or("leaf artifact byte count overflow")?;
        let leaf = deserialize_recursive_actual_pbs_chain_chunk_proof(&bytes)?;
        max_base_public_inputs = max_base_public_inputs.max(leaf.base.public_inputs.len());
        max_recursive_public_inputs =
            max_recursive_public_inputs.max(leaf.recursion.public_input_count());
        statements.push(leaf.base.public_statement());
        current_summaries.push(leaf.chain_summary.clone());
        current_nodes.push(RecursivePbsChainNodeArtifact::Leaf(path));
    }
    tfheprus_prover::validate_actual_pbs_chain_chunk_statements(&statements)
        .map_err(|error| format!("leaf artifact continuity check failed: {error}"))?;
    let read_time = read_started.elapsed();

    let mut layer_sizes = Vec::new();
    let mut written_count = 0usize;
    let mut reused_count = 0usize;
    let mut total_aggregate_time = Duration::ZERO;
    let mut total_aggregate_artifact_bytes = 0usize;
    let leaf_count = current_nodes.len();

    let mut layer_index = 0usize;
    while current_nodes.len() > 1 {
        let pair_count = current_nodes.len() / 2;
        let layer_dir = checkpoint_dir.join(format!("layer-{layer_index:03}"));
        fs::create_dir_all(&layer_dir)?;
        let mut next_nodes = Vec::with_capacity(current_nodes.len().div_ceil(2));
        let mut next_summaries = Vec::with_capacity(current_summaries.len().div_ceil(2));
        layer_sizes.push(pair_count);

        for node_index in 0..pair_count {
            let output_node_path = layer_dir.join(format!("agg-{node_index:05}.bin"));
            let expected_summary = ActualPbsChainSummary::combine(
                &current_summaries[node_index * 2],
                &current_summaries[node_index * 2 + 1],
            )?;

            if output_node_path.exists() {
                let bytes = fs::read(&output_node_path)?;
                total_aggregate_artifact_bytes = total_aggregate_artifact_bytes
                    .checked_add(bytes.len())
                    .ok_or("aggregate artifact byte count overflow")?;
                let proof = deserialize_aggregated_recursive_actual_pbs_chain_node_proof(&bytes)?;
                if proof.chain_summary != expected_summary {
                    return Err(format!(
                        "stale aggregate checkpoint has wrong summary: {}",
                        output_node_path.display()
                    )
                    .into());
                }
                reused_count += 1;
                eprintln!(
                    "reused pbs-chain aggregate checkpoint: layer={}, node={}, artifact={}, bytes={}",
                    layer_index,
                    node_index,
                    output_node_path.display(),
                    bytes.len()
                );
            } else {
                let left = load_recursive_pbs_chain_node(&current_nodes[node_index * 2])?;
                let right = load_recursive_pbs_chain_node(&current_nodes[node_index * 2 + 1])?;
                if left.chain_summary() != &current_summaries[node_index * 2]
                    || right.chain_summary() != &current_summaries[node_index * 2 + 1]
                {
                    return Err("node summary changed while aggregating checkpoints".into());
                }
                let aggregate_started = Instant::now();
                let proof = if private_recursive {
                    prove_private_aggregated_recursive_actual_pbs_chain_node_pair(
                        left.as_prover_node(),
                        right.as_prover_node(),
                    )?
                } else {
                    prove_aggregated_recursive_actual_pbs_chain_node_pair(
                        left.as_prover_node(),
                        right.as_prover_node(),
                    )?
                };
                let aggregate_time = aggregate_started.elapsed();
                total_aggregate_time += aggregate_time;
                if proof.chain_summary != expected_summary {
                    return Err("aggregate proof summary mismatch".into());
                }
                let bytes = serialize_aggregated_recursive_actual_pbs_chain_node_proof(&proof)?;
                write_artifact_atomic(&output_node_path, &bytes)?;
                total_aggregate_artifact_bytes = total_aggregate_artifact_bytes
                    .checked_add(bytes.len())
                    .ok_or("aggregate artifact byte count overflow")?;
                written_count += 1;
                eprintln!(
                    "wrote pbs-chain aggregate checkpoint: layer={}, node={}, artifact={}, bytes={}, aggregate_us={}",
                    layer_index,
                    node_index,
                    output_node_path.display(),
                    bytes.len(),
                    aggregate_time.as_micros()
                );
            }

            next_nodes.push(RecursivePbsChainNodeArtifact::Aggregate(output_node_path));
            next_summaries.push(expected_summary);
        }

        if current_nodes.len() % 2 == 1 {
            next_nodes.push(
                current_nodes
                    .last()
                    .ok_or("missing carried aggregate node")?
                    .clone(),
            );
            next_summaries.push(
                current_summaries
                    .last()
                    .ok_or("missing carried aggregate summary")?
                    .clone(),
            );
        }

        current_nodes = next_nodes;
        current_summaries = next_summaries;
        layer_index += 1;
    }

    let final_node = current_nodes
        .pop()
        .ok_or("missing final aggregate checkpoint")?;
    let root_summary = current_summaries
        .pop()
        .ok_or("missing final aggregate summary")?;
    let RecursivePbsChainNodeArtifact::Aggregate(final_node_path) = final_node else {
        return Err("final node must be an aggregate proof".into());
    };
    let final_node_bytes = fs::read(&final_node_path)?;
    let final_node_proof =
        deserialize_aggregated_recursive_actual_pbs_chain_node_proof(&final_node_bytes)?;
    if final_node_proof.chain_summary != root_summary {
        return Err("final aggregate summary mismatch".into());
    }
    let root_table_count = final_node_proof.table_count();
    let root_public_input_count = final_node_proof.public_input_count();
    let chain_summary_fields = final_node_proof.chain_summary.field_values().len();
    let root_proof = final_node_proof.into_root_proof();
    let root_artifact = serialize_aggregated_recursive_actual_pbs_chain_root_proof(&root_proof)?;
    let decoded_root_proof =
        deserialize_aggregated_recursive_actual_pbs_chain_root_proof(&root_artifact)?;
    let root_verify_started = Instant::now();
    verify_aggregated_recursive_actual_pbs_chain_root_summary_proof(
        &root_summary,
        &decoded_root_proof,
    )?;
    let root_verify_time = root_verify_started.elapsed();
    write_artifact_atomic(Path::new(output_path), &root_artifact)?;

    let layer_sizes = layer_sizes
        .iter()
        .map(|size| size.to_string())
        .collect::<Vec<_>>()
        .join(",");
    println!(
        "pbs-chain leaf artifacts checkpoint-aggregated: output={}, private_recursive={}, checkpoint_dir={}, leaves={}, layers={}, layer_sizes=[{}], aggregation_nodes={}, written={}, reused={}, root_tables={}, root_public_inputs={}, chain_summary_fields={}",
        output_path,
        private_recursive,
        checkpoint_dir.display(),
        leaf_count,
        layer_index,
        layer_sizes,
        written_count + reused_count,
        written_count,
        reused_count,
        root_table_count,
        root_public_input_count,
        chain_summary_fields
    );
    println!(
        "read_ms={}, read_us={}, aggregate_ms={}, aggregate_us={}, root_verify_ms={}, root_verify_us={}, leaf_artifact_bytes={}, aggregate_artifact_bytes={}, root_artifact_bytes={}, max_base_public_inputs={}, max_recursive_public_inputs={}",
        read_time.as_millis(),
        read_time.as_micros(),
        total_aggregate_time.as_millis(),
        total_aggregate_time.as_micros(),
        root_verify_time.as_millis(),
        root_verify_time.as_micros(),
        total_leaf_artifact_bytes,
        total_aggregate_artifact_bytes,
        root_artifact.len(),
        max_base_public_inputs,
        max_recursive_public_inputs
    );

    Ok(())
}

#[derive(Clone)]
enum CompactRecursivePbsChainNodeArtifact {
    Leaf(PathBuf),
    Aggregate(PathBuf),
}

enum LoadedCompactRecursivePbsChainNode {
    Leaf(Box<CompactRecursiveActualPbsChainChunkProof>),
    Aggregate(Box<CompactAggregatedRecursiveActualPbsChainNodeProof>),
}

impl CompactRecursivePbsChainNodeArtifact {
    fn path(&self) -> &Path {
        match self {
            Self::Leaf(path) | Self::Aggregate(path) => path,
        }
    }
}

impl LoadedCompactRecursivePbsChainNode {
    fn chain_summary(&self) -> &CompactActualPbsChainSummary {
        match self {
            Self::Leaf(proof) => &proof.chain_summary,
            Self::Aggregate(proof) => &proof.chain_summary,
        }
    }

    fn as_prover_node(&self) -> CompactRecursiveActualPbsChainNode<'_> {
        match self {
            Self::Leaf(proof) => CompactRecursiveActualPbsChainNode::Leaf(proof),
            Self::Aggregate(proof) => CompactRecursiveActualPbsChainNode::Aggregate(proof),
        }
    }
}

fn aggregate_pbs_chain_private_compact_leaf_artifacts_checkpointed_recursive_demo(
    output_path: &str,
    leaf_paths: Vec<String>,
    checkpoint_dir: &Path,
) -> Result<(), Box<dyn Error>> {
    if leaf_paths.len() < 2 {
        return Err("at least two compact leaf artifacts are required".into());
    }

    fs::create_dir_all(checkpoint_dir)?;
    let read_started = Instant::now();
    let mut statements = Vec::with_capacity(leaf_paths.len());
    let mut current_nodes = Vec::with_capacity(leaf_paths.len());
    let mut current_summaries = Vec::with_capacity(leaf_paths.len());
    let mut total_leaf_artifact_bytes = 0usize;
    let mut max_base_public_inputs = 0usize;
    let mut max_recursive_public_inputs = 0usize;
    for path in leaf_paths {
        let path = PathBuf::from(path);
        let bytes = fs::read(&path)?;
        total_leaf_artifact_bytes = total_leaf_artifact_bytes
            .checked_add(bytes.len())
            .ok_or("compact leaf artifact byte count overflow")?;
        let leaf = deserialize_compact_recursive_actual_pbs_chain_chunk_proof(&bytes)?;
        max_base_public_inputs = max_base_public_inputs.max(leaf.base.public_inputs.len());
        max_recursive_public_inputs =
            max_recursive_public_inputs.max(leaf.recursion.public_input_count());
        statements.push(leaf.base.public_statement());
        current_summaries.push(leaf.chain_summary.clone());
        current_nodes.push(CompactRecursivePbsChainNodeArtifact::Leaf(path));
    }
    tfheprus_prover::validate_actual_pbs_chain_chunk_statements(&statements)
        .map_err(|error| format!("compact leaf artifact continuity check failed: {error}"))?;
    let read_time = read_started.elapsed();

    let mut layer_sizes = Vec::new();
    let mut written_count = 0usize;
    let mut reused_count = 0usize;
    let mut total_aggregate_time = Duration::ZERO;
    let mut total_aggregate_artifact_bytes = 0usize;
    let leaf_count = current_nodes.len();

    let mut layer_index = 0usize;
    while current_nodes.len() > 1 {
        let pair_count = current_nodes.len() / 2;
        let layer_dir = checkpoint_dir.join(format!("layer-{layer_index:03}"));
        fs::create_dir_all(&layer_dir)?;
        let mut next_nodes = Vec::with_capacity(current_nodes.len().div_ceil(2));
        let mut next_summaries = Vec::with_capacity(current_summaries.len().div_ceil(2));
        layer_sizes.push(pair_count);

        for node_index in 0..pair_count {
            let output_node_path = layer_dir.join(format!("agg-{node_index:05}.bin"));
            let expected_summary = CompactActualPbsChainSummary::combine(
                &current_summaries[node_index * 2],
                &current_summaries[node_index * 2 + 1],
            )?;

            if output_node_path.exists() {
                let bytes = fs::read(&output_node_path)?;
                total_aggregate_artifact_bytes = total_aggregate_artifact_bytes
                    .checked_add(bytes.len())
                    .ok_or("compact aggregate artifact byte count overflow")?;
                let proof =
                    deserialize_compact_aggregated_recursive_actual_pbs_chain_node_proof(&bytes)?;
                if proof.chain_summary != expected_summary {
                    return Err(format!(
                        "stale compact aggregate checkpoint has wrong summary: {}",
                        output_node_path.display()
                    )
                    .into());
                }
                reused_count += 1;
                eprintln!(
                    "reused pbs-chain compact aggregate checkpoint: layer={}, node={}, artifact={}, bytes={}",
                    layer_index,
                    node_index,
                    output_node_path.display(),
                    bytes.len()
                );
            } else {
                let left = load_compact_recursive_pbs_chain_node(&current_nodes[node_index * 2])?;
                let right =
                    load_compact_recursive_pbs_chain_node(&current_nodes[node_index * 2 + 1])?;
                if left.chain_summary() != &current_summaries[node_index * 2]
                    || right.chain_summary() != &current_summaries[node_index * 2 + 1]
                {
                    return Err("compact node summary changed while aggregating checkpoints".into());
                }
                let aggregate_started = Instant::now();
                let proof = prove_private_compact_aggregated_recursive_actual_pbs_chain_node_pair(
                    left.as_prover_node(),
                    right.as_prover_node(),
                )?;
                let aggregate_time = aggregate_started.elapsed();
                total_aggregate_time += aggregate_time;
                if proof.chain_summary != expected_summary {
                    return Err("compact aggregate proof summary mismatch".into());
                }
                let bytes =
                    serialize_compact_aggregated_recursive_actual_pbs_chain_node_proof(&proof)?;
                write_artifact_atomic(&output_node_path, &bytes)?;
                total_aggregate_artifact_bytes = total_aggregate_artifact_bytes
                    .checked_add(bytes.len())
                    .ok_or("compact aggregate artifact byte count overflow")?;
                written_count += 1;
                eprintln!(
                    "wrote pbs-chain compact aggregate checkpoint: layer={}, node={}, artifact={}, bytes={}, aggregate_us={}",
                    layer_index,
                    node_index,
                    output_node_path.display(),
                    bytes.len(),
                    aggregate_time.as_micros()
                );
            }

            next_nodes.push(CompactRecursivePbsChainNodeArtifact::Aggregate(
                output_node_path,
            ));
            next_summaries.push(expected_summary);
        }

        if current_nodes.len() % 2 == 1 {
            next_nodes.push(
                current_nodes
                    .last()
                    .ok_or("missing carried compact aggregate node")?
                    .clone(),
            );
            next_summaries.push(
                current_summaries
                    .last()
                    .ok_or("missing carried compact aggregate summary")?
                    .clone(),
            );
        }

        current_nodes = next_nodes;
        current_summaries = next_summaries;
        layer_index += 1;
    }

    let final_node = current_nodes
        .pop()
        .ok_or("missing final compact aggregate checkpoint")?;
    let root_summary = current_summaries
        .pop()
        .ok_or("missing final compact aggregate summary")?;
    let CompactRecursivePbsChainNodeArtifact::Aggregate(final_node_path) = final_node else {
        return Err("final compact node must be an aggregate proof".into());
    };
    let final_node_bytes = fs::read(&final_node_path)?;
    let final_node_proof =
        deserialize_compact_aggregated_recursive_actual_pbs_chain_node_proof(&final_node_bytes)?;
    if final_node_proof.chain_summary != root_summary {
        return Err("final compact aggregate summary mismatch".into());
    }
    let root_table_count = final_node_proof.table_count();
    let root_public_input_count = final_node_proof.public_input_count();
    let compact_summary_fields = final_node_proof.chain_summary.field_values().len();
    let root_proof = final_node_proof.into_root_proof();
    let root_artifact =
        serialize_compact_aggregated_recursive_actual_pbs_chain_root_proof(&root_proof)?;
    let decoded_root_proof =
        deserialize_compact_aggregated_recursive_actual_pbs_chain_root_proof(&root_artifact)?;
    let root_verify_started = Instant::now();
    verify_compact_aggregated_recursive_actual_pbs_chain_root_summary_proof(
        &root_summary,
        &decoded_root_proof,
    )?;
    let root_verify_time = root_verify_started.elapsed();
    write_artifact_atomic(Path::new(output_path), &root_artifact)?;

    let layer_sizes = layer_sizes
        .iter()
        .map(|size| size.to_string())
        .collect::<Vec<_>>()
        .join(",");
    println!(
        "pbs-chain compact leaf artifacts checkpoint-aggregated: output={}, checkpoint_dir={}, leaves={}, layers={}, layer_sizes=[{}], aggregation_nodes={}, written={}, reused={}, root_tables={}, root_public_inputs={}, compact_summary_fields={}",
        output_path,
        checkpoint_dir.display(),
        leaf_count,
        layer_index,
        layer_sizes,
        written_count + reused_count,
        written_count,
        reused_count,
        root_table_count,
        root_public_input_count,
        compact_summary_fields
    );
    println!(
        "read_ms={}, read_us={}, aggregate_ms={}, aggregate_us={}, root_verify_ms={}, root_verify_us={}, leaf_artifact_bytes={}, aggregate_artifact_bytes={}, root_artifact_bytes={}, max_base_public_inputs={}, max_recursive_public_inputs={}",
        read_time.as_millis(),
        read_time.as_micros(),
        total_aggregate_time.as_millis(),
        total_aggregate_time.as_micros(),
        root_verify_time.as_millis(),
        root_verify_time.as_micros(),
        total_leaf_artifact_bytes,
        total_aggregate_artifact_bytes,
        root_artifact.len(),
        max_base_public_inputs,
        max_recursive_public_inputs
    );

    Ok(())
}

fn load_compact_recursive_pbs_chain_node(
    node: &CompactRecursivePbsChainNodeArtifact,
) -> Result<LoadedCompactRecursivePbsChainNode, Box<dyn Error>> {
    let bytes = fs::read(node.path())?;
    match node {
        CompactRecursivePbsChainNodeArtifact::Leaf(_) => {
            let proof = deserialize_compact_recursive_actual_pbs_chain_chunk_proof(&bytes)?;
            Ok(LoadedCompactRecursivePbsChainNode::Leaf(Box::new(proof)))
        }
        CompactRecursivePbsChainNodeArtifact::Aggregate(_) => {
            let proof =
                deserialize_compact_aggregated_recursive_actual_pbs_chain_node_proof(&bytes)?;
            Ok(LoadedCompactRecursivePbsChainNode::Aggregate(Box::new(
                proof,
            )))
        }
    }
}

fn load_recursive_pbs_chain_node(
    node: &RecursivePbsChainNodeArtifact,
) -> Result<LoadedRecursivePbsChainNode, Box<dyn Error>> {
    let bytes = fs::read(node.path())?;
    match node {
        RecursivePbsChainNodeArtifact::Leaf(_) => {
            let proof = deserialize_recursive_actual_pbs_chain_chunk_proof(&bytes)?;
            Ok(LoadedRecursivePbsChainNode::Leaf(Box::new(proof)))
        }
        RecursivePbsChainNodeArtifact::Aggregate(_) => {
            let proof = deserialize_aggregated_recursive_actual_pbs_chain_node_proof(&bytes)?;
            Ok(LoadedRecursivePbsChainNode::Aggregate(Box::new(proof)))
        }
    }
}

fn write_artifact_atomic(path: &Path, bytes: &[u8]) -> Result<(), Box<dyn Error>> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or("artifact path must have a UTF-8 file name")?;
    let temp_path = path.with_file_name(format!("{file_name}.tmp"));
    fs::write(&temp_path, bytes)?;
    fs::rename(temp_path, path)?;
    Ok(())
}

fn package_pbs_chain_frontier_artifact_dir_recursive_demo(
    output_path: &str,
    aggregate_dir: &str,
) -> Result<(), Box<dyn Error>> {
    let aggregate_paths = aggregate_artifact_paths_from_dir(aggregate_dir)?;
    package_pbs_chain_frontier_artifacts_recursive_demo(output_path, aggregate_paths)
}

fn package_pbs_chain_frontier_artifacts_recursive_demo(
    output_path: &str,
    aggregate_paths: Vec<String>,
) -> Result<(), Box<dyn Error>> {
    if aggregate_paths.is_empty() {
        return Err("at least one aggregate artifact is required".into());
    }

    let read_started = Instant::now();
    let mut nodes = Vec::with_capacity(aggregate_paths.len());
    let mut total_input_bytes = 0usize;
    for path in aggregate_paths {
        let bytes = fs::read(&path)?;
        total_input_bytes = total_input_bytes
            .checked_add(bytes.len())
            .ok_or("frontier input byte count overflow")?;
        nodes.push(deserialize_aggregated_recursive_actual_pbs_chain_node_proof(&bytes)?);
    }
    let read_time = read_started.elapsed();

    let frontier = build_aggregated_recursive_actual_pbs_chain_frontier_proof(nodes)?;
    let node_count = frontier.node_count();
    let total_public_inputs = frontier.total_public_input_count();
    let max_public_inputs = frontier.max_public_input_count();
    let summary = frontier.chain_summary.clone();
    let artifact = serialize_aggregated_recursive_actual_pbs_chain_frontier_proof(&frontier)?;
    let decoded = deserialize_aggregated_recursive_actual_pbs_chain_frontier_proof(&artifact)?;
    let verify_started = Instant::now();
    verify_aggregated_recursive_actual_pbs_chain_frontier_summary_proof(&summary, &decoded)?;
    let verify_time = verify_started.elapsed();
    write_artifact_atomic(Path::new(output_path), &artifact)?;

    println!(
        "pbs-chain frontier artifact packaged: output={}, nodes={}, params_n={}, total_steps={}, chain_summary_fields={}, total_public_inputs={}, max_public_inputs={}",
        output_path,
        node_count,
        summary.params.lwe_dimension,
        summary.step_count,
        summary.field_values().len(),
        total_public_inputs,
        max_public_inputs
    );
    println!(
        "read_ms={}, read_us={}, verify_ms={}, verify_us={}, input_artifact_bytes={}, frontier_artifact_bytes={}",
        read_time.as_millis(),
        read_time.as_micros(),
        verify_time.as_millis(),
        verify_time.as_micros(),
        total_input_bytes,
        artifact.len()
    );

    Ok(())
}

fn verify_pbs_chain_root_artifact_recursive_demo(path: &str) -> Result<(), Box<dyn Error>> {
    let bytes = fs::read(path)?;
    let proof = deserialize_aggregated_recursive_actual_pbs_chain_root_proof(&bytes)?;
    let summary = proof.chain_summary.clone();
    let verify_started = Instant::now();
    verify_aggregated_recursive_actual_pbs_chain_root_summary_proof(&summary, &proof)?;
    let verify_time = verify_started.elapsed();

    println!(
        "pbs-chain root artifact verified: artifact={}, artifact_bytes={}, params_n={}, total_steps={}, chain_summary_fields={}, root_public_inputs={}, verify_ms={}, verify_us={}",
        path,
        bytes.len(),
        summary.params.lwe_dimension,
        summary.step_count,
        summary.field_values().len(),
        proof.root.public_input_count(),
        verify_time.as_millis(),
        verify_time.as_micros()
    );

    Ok(())
}

fn verify_pbs_chain_compact_root_artifact_recursive_demo(path: &str) -> Result<(), Box<dyn Error>> {
    let bytes = fs::read(path)?;
    let proof = deserialize_compact_aggregated_recursive_actual_pbs_chain_root_proof(&bytes)?;
    let summary = proof.chain_summary.clone();
    let verify_started = Instant::now();
    verify_compact_aggregated_recursive_actual_pbs_chain_root_summary_proof(&summary, &proof)?;
    let verify_time = verify_started.elapsed();

    println!(
        "pbs-chain compact root artifact verified: artifact={}, artifact_bytes={}, params_n={}, total_steps={}, compact_summary_fields={}, root_public_inputs={}, verify_ms={}, verify_us={}",
        path,
        bytes.len(),
        summary.params.lwe_dimension,
        summary.step_count,
        summary.field_values().len(),
        proof.root.public_input_count(),
        verify_time.as_millis(),
        verify_time.as_micros()
    );

    Ok(())
}

fn verify_pbs_chain_frontier_artifact_recursive_demo(path: &str) -> Result<(), Box<dyn Error>> {
    let bytes = fs::read(path)?;
    let proof = deserialize_aggregated_recursive_actual_pbs_chain_frontier_proof(&bytes)?;
    let summary = proof.chain_summary.clone();
    let node_count = proof.node_count();
    let total_public_inputs = proof.total_public_input_count();
    let max_public_inputs = proof.max_public_input_count();
    let verify_started = Instant::now();
    verify_aggregated_recursive_actual_pbs_chain_frontier_summary_proof(&summary, &proof)?;
    let verify_time = verify_started.elapsed();

    println!(
        "pbs-chain frontier artifact verified: artifact={}, artifact_bytes={}, nodes={}, params_n={}, total_steps={}, chain_summary_fields={}, total_public_inputs={}, max_public_inputs={}, verify_ms={}, verify_us={}",
        path,
        bytes.len(),
        node_count,
        summary.params.lwe_dimension,
        summary.step_count,
        summary.field_values().len(),
        total_public_inputs,
        max_public_inputs,
        verify_time.as_millis(),
        verify_time.as_micros()
    );

    Ok(())
}

fn inspect_pbs_chain_artifact_demo(kind: &str, path: &str) -> Result<(), Box<dyn Error>> {
    let bytes = fs::read(path)?;
    match kind {
        "leaf" => {
            let proof = deserialize_recursive_actual_pbs_chain_chunk_proof(&bytes)?;
            println!(
                "pbs-chain artifact inspected: kind=leaf, artifact={}, artifact_bytes={}, params_n={}, steps={}, base_public_inputs={}, recursive_public_inputs={}, chain_summary_fields={}",
                path,
                bytes.len(),
                proof.chain_summary.params.lwe_dimension,
                proof.chain_summary.step_count,
                proof.base.public_inputs.len(),
                proof.recursion.public_input_count(),
                proof.chain_summary.field_values().len()
            );
        }
        "compact-leaf" => {
            let proof = deserialize_compact_recursive_actual_pbs_chain_chunk_proof(&bytes)?;
            println!(
                "pbs-chain artifact inspected: kind=compact-leaf, artifact={}, artifact_bytes={}, params_n={}, steps={}, base_public_inputs={}, recursive_public_inputs={}, compact_summary_fields={}",
                path,
                bytes.len(),
                proof.chain_summary.params.lwe_dimension,
                proof.chain_summary.step_count,
                proof.base.public_inputs.len(),
                proof.recursion.public_input_count(),
                proof.chain_summary.field_values().len()
            );
        }
        "node" => {
            let proof = deserialize_aggregated_recursive_actual_pbs_chain_node_proof(&bytes)?;
            println!(
                "pbs-chain artifact inspected: kind=node, artifact={}, artifact_bytes={}, params_n={}, total_steps={}, node_tables={}, node_public_inputs={}, chain_summary_fields={}",
                path,
                bytes.len(),
                proof.chain_summary.params.lwe_dimension,
                proof.chain_summary.step_count,
                proof.table_count(),
                proof.public_input_count(),
                proof.chain_summary.field_values().len()
            );
        }
        "compact-node" => {
            let proof =
                deserialize_compact_aggregated_recursive_actual_pbs_chain_node_proof(&bytes)?;
            println!(
                "pbs-chain artifact inspected: kind=compact-node, artifact={}, artifact_bytes={}, params_n={}, total_steps={}, node_tables={}, node_public_inputs={}, compact_summary_fields={}",
                path,
                bytes.len(),
                proof.chain_summary.params.lwe_dimension,
                proof.chain_summary.step_count,
                proof.table_count(),
                proof.public_input_count(),
                proof.chain_summary.field_values().len()
            );
        }
        "root" => {
            let proof = deserialize_aggregated_recursive_actual_pbs_chain_root_proof(&bytes)?;
            let breakdown = proof.root.size_breakdown()?;
            println!(
                "pbs-chain artifact inspected: kind=root, artifact={}, artifact_bytes={}, params_n={}, total_steps={}, root_tables={}, root_public_inputs={}, chain_summary_fields={}",
                path,
                bytes.len(),
                proof.chain_summary.params.lwe_dimension,
                proof.chain_summary.step_count,
                proof.root.table_count(),
                proof.root.public_input_count(),
                proof.chain_summary.field_values().len()
            );
            print_recursive_size_breakdown("root", path, &breakdown);
        }
        "compact-root" => {
            let proof =
                deserialize_compact_aggregated_recursive_actual_pbs_chain_root_proof(&bytes)?;
            let breakdown = proof.root.size_breakdown()?;
            println!(
                "pbs-chain artifact inspected: kind=compact-root, artifact={}, artifact_bytes={}, params_n={}, total_steps={}, root_tables={}, root_public_inputs={}, compact_summary_fields={}",
                path,
                bytes.len(),
                proof.chain_summary.params.lwe_dimension,
                proof.chain_summary.step_count,
                proof.root.table_count(),
                proof.root.public_input_count(),
                proof.chain_summary.field_values().len()
            );
            print_recursive_size_breakdown("compact-root", path, &breakdown);
        }
        "frontier" => {
            let proof = deserialize_aggregated_recursive_actual_pbs_chain_frontier_proof(&bytes)?;
            println!(
                "pbs-chain artifact inspected: kind=frontier, artifact={}, artifact_bytes={}, params_n={}, total_steps={}, nodes={}, total_public_inputs={}, max_public_inputs={}, chain_summary_fields={}",
                path,
                bytes.len(),
                proof.chain_summary.params.lwe_dimension,
                proof.chain_summary.step_count,
                proof.node_count(),
                proof.total_public_input_count(),
                proof.max_public_input_count(),
                proof.chain_summary.field_values().len()
            );
        }
        other => {
            return Err(format!(
                "unknown PBS chain artifact kind: {other}; expected leaf, compact-leaf, node, compact-node, root, compact-root, or frontier"
            )
            .into());
        }
    }

    Ok(())
}

fn print_recursive_size_breakdown(kind: &str, path: &str, breakdown: &RecursiveProofSizeBreakdown) {
    println!(
        "pbs-chain recursive size breakdown: kind={}, artifact={}, public_inputs_bytes={}, batch_stark_bytes={}, core_proof_bytes={}, commitments_bytes={}, opened_values_bytes={}, opening_proof_bytes={}, global_lookup_data_bytes={}, degree_bits_bytes={}, primitive_public_values_bytes={}, non_primitives_bytes={}, structural_metadata_bytes={}",
        kind,
        path,
        breakdown.public_inputs_bytes,
        breakdown.batch_stark_bytes,
        breakdown.core_proof_bytes,
        breakdown.commitments_bytes,
        breakdown.opened_values_bytes,
        breakdown.opening_proof_bytes,
        breakdown.global_lookup_data_bytes,
        breakdown.degree_bits_bytes,
        breakdown.primitive_public_values_bytes,
        breakdown.non_primitives_bytes,
        breakdown.structural_metadata_bytes
    );
}

fn bench_pbs_chain_private_recursive_demo(
    preset: ParamPreset,
    chunk_step_count: usize,
    chunk_count: usize,
    output_dir: &str,
    compact: bool,
) -> Result<(), Box<dyn Error>> {
    let mode = if compact { "compact" } else { "full" };
    let mode_dir = Path::new(output_dir).join(mode);
    let root_path = mode_dir.join("root.bin");
    let mode_dir = path_to_string(mode_dir)?;
    let root_path = path_to_string(root_path)?;
    let total_steps = chunk_step_count
        .checked_mul(chunk_count)
        .ok_or("chunk_steps * chunk_count overflowed")?;
    let started = Instant::now();
    println!(
        "pbs-chain private benchmark start: mode={}, preset={}, chunk_steps={}, chunk_count={}, total_steps={}, artifact_dir={}, rayon_num_threads={}, rustflags={}",
        mode,
        preset.name(),
        chunk_step_count,
        chunk_count,
        total_steps,
        mode_dir,
        env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "unset".to_string()),
        env::var("RUSTFLAGS").unwrap_or_else(|_| "unset".to_string())
    );

    if compact {
        prove_pbs_chain_private_compact_leaves_recursive_artifacts_demo(
            preset,
            chunk_step_count,
            chunk_count,
            &mode_dir,
            false,
        )?;
        aggregate_pbs_chain_private_compact_leaf_artifact_dir_recursive_demo(
            &root_path,
            &mode_dir,
            Some(chunk_count),
        )?;
        verify_pbs_chain_compact_root_artifact_recursive_demo(&root_path)?;
    } else {
        prove_pbs_chain_leaves_recursive_artifacts_demo(
            preset,
            chunk_step_count,
            chunk_count,
            &mode_dir,
            true,
            false,
        )?;
        aggregate_pbs_chain_leaf_artifact_dir_recursive_demo(
            &root_path,
            &mode_dir,
            Some(chunk_count),
            true,
        )?;
        verify_pbs_chain_root_artifact_recursive_demo(&root_path)?;
    }

    let elapsed = started.elapsed();
    println!(
        "pbs-chain private benchmark done: mode={}, root_artifact={}, total_ms={}, total_us={}",
        mode,
        root_path,
        elapsed.as_millis(),
        elapsed.as_micros()
    );

    Ok(())
}

fn leaf_artifact_paths_from_dir(
    leaf_dir: &str,
    leaf_count: Option<usize>,
) -> Result<Vec<String>, Box<dyn Error>> {
    let leaf_dir = Path::new(leaf_dir);
    let paths = if let Some(leaf_count) = leaf_count {
        if leaf_count < 2 {
            return Err("leaf count must be at least 2".into());
        }
        let mut paths = Vec::with_capacity(leaf_count);
        for index in 0..leaf_count {
            let path = leaf_dir.join(format!("leaf-{index:05}.bin"));
            if !path.exists() {
                return Err(format!("missing leaf artifact: {}", path.display()).into());
            }
            paths.push(path);
        }
        paths
    } else {
        let mut paths = Vec::new();
        for entry in fs::read_dir(leaf_dir)? {
            let entry = entry?;
            let path = entry.path();
            let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
                continue;
            };
            if file_name.starts_with("leaf-") && file_name.ends_with(".bin") {
                paths.push(path);
            }
        }
        paths.sort();
        if paths.len() < 2 {
            return Err("at least two leaf artifacts are required".into());
        }
        paths
    };

    paths
        .into_iter()
        .map(path_to_string)
        .collect::<Result<Vec<_>, _>>()
}

fn aggregate_artifact_paths_from_dir(aggregate_dir: &str) -> Result<Vec<String>, Box<dyn Error>> {
    let aggregate_dir = Path::new(aggregate_dir);
    let mut paths = Vec::new();
    for entry in fs::read_dir(aggregate_dir)? {
        let entry = entry?;
        let path = entry.path();
        let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if file_name.starts_with("agg-") && file_name.ends_with(".bin") {
            paths.push(path);
        }
    }
    paths.sort();
    if paths.is_empty() {
        return Err("at least one aggregate artifact is required".into());
    }
    paths
        .into_iter()
        .map(path_to_string)
        .collect::<Result<Vec<_>, _>>()
}

fn path_to_string(path: PathBuf) -> Result<String, Box<dyn Error>> {
    path.into_os_string()
        .into_string()
        .map_err(|path| format!("non-UTF-8 path is not supported: {path:?}").into())
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
    let chain_summary_fields = chunk_public_inputs + 7;
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
        "leaf_shape: chunk_public_inputs={}, chain_summary_fields={}, step_private_inputs={}, full_chunk_private_inputs={}, last_chunk_private_inputs={}, total_leaf_private_inputs={}, total_leaf_private_mib={:.2}",
        chunk_public_inputs,
        chain_summary_fields,
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

fn actual_pbs_chain_chunk_instance_at(
    params: Params,
    chunk_step_count: usize,
    chunk_index: usize,
) -> Result<(usize, usize, ActualPbsChainChunkInstance), Box<dyn Error>> {
    if chunk_step_count == 0 {
        return Err("chunk step count must be nonzero".into());
    }
    let chunk_start = chunk_step_count
        .checked_mul(chunk_index)
        .ok_or("chunk_steps * chunk_index overflowed")?;
    if chunk_start >= params.lwe_dimension {
        return Err(format!(
            "chunk start must be less than params_n={}",
            params.lwe_dimension
        )
        .into());
    }
    let chunk_end = (chunk_start + chunk_step_count).min(params.lwe_dimension);

    let (params, _sk, evaluation_key, input, test_polynomial) = actual_pbs_materials(params);
    let body_exponent = tfheprus_core::mod_switch_to_exponent(&params, input.body);
    let initial_exponent = (params.exponent_modulus() - body_exponent) % params.exponent_modulus();
    let mut accumulator = GlweCiphertext::trivial(
        test_polynomial.poly.mul_xai(initial_exponent),
        params.glwe_dimension,
    );
    let mut bsk_digest = pbs_bsk_digest_initial();
    let mut mask_digest = pbs_mask_digest_initial();
    if chunk_start > 0 {
        let evaluation_key_ntt = evaluation_key.to_ntt();
        for step_index in 0..chunk_start {
            let mask_value = input.mask[step_index];
            let exponent = tfheprus_core::mod_switch_to_exponent(&params, mask_value);
            let rotated = accumulator.mul_xai(exponent);
            accumulator = cmux_ntt(
                &params,
                &accumulator,
                &rotated,
                &evaluation_key_ntt.bootstrapping_key[step_index],
            );
            bsk_digest =
                pbs_bsk_digest_update(bsk_digest, &evaluation_key.bootstrapping_key[step_index]);
            mask_digest = pbs_mask_digest_update(mask_digest, mask_value);
        }
    }

    let instance = ActualPbsChainChunkInstance::new(
        params.clone(),
        input.mask[chunk_start..chunk_end].to_vec(),
        accumulator,
        evaluation_key.bootstrapping_key[chunk_start..chunk_end].to_vec(),
        bsk_digest,
        mask_digest,
    );

    Ok((chunk_start, chunk_end, instance))
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
        "Usage: tfheprus [params|prove-poly-mul|prove-mul-xai|prove-sample-extract|prove-pbs-step [toy|moderate|paper-v1]|prove-pbs-step-private [toy|moderate|paper-v1]|prove-pbs-step-chain [toy|moderate|paper-v1]|prove-pbs-chain-chunk [toy|moderate|paper-v1] [steps]|prove-pbs-chain-chunk-recursive [toy|moderate|paper-v1] [steps]|prove-pbs-chain-prefix-recursive [toy|moderate|paper-v1] [chunk_steps] [total_steps]|prove-pbs-chain-pair-aggregate-recursive [toy|moderate|paper-v1] [chunk_steps]|prove-pbs-chain-tree-aggregate-recursive [toy|moderate|paper-v1] [chunk_steps] [chunk_count]|prove-pbs-chain-private-tree-aggregate-recursive [toy|moderate|paper-v1] [chunk_steps] [chunk_count]|prove-pbs-chain-leaf-recursive [toy|moderate|paper-v1] [chunk_steps] [chunk_index] <leaf_artifact>|prove-pbs-chain-private-leaf-recursive [toy|moderate|paper-v1] [chunk_steps] [chunk_index] <leaf_artifact>|prove-pbs-chain-leaves-recursive [toy|moderate|paper-v1] [chunk_steps] <chunk_count> <leaf_artifact_dir>|prove-pbs-chain-private-leaves-recursive [toy|moderate|paper-v1] [chunk_steps] <chunk_count> <leaf_artifact_dir>|prove-pbs-chain-private-leaves-recursive-fast [toy|moderate|paper-v1] [chunk_steps] <chunk_count> <leaf_artifact_dir>|prove-pbs-chain-private-leaves-compact-fast [toy|moderate|paper-v1] [chunk_steps] <chunk_count> <leaf_artifact_dir>|aggregate-pbs-chain-leaves-recursive <root_artifact> <leaf_artifact>...|aggregate-pbs-chain-leaf-dir-recursive <root_artifact> <leaf_artifact_dir> [leaf_count]|aggregate-pbs-chain-private-leaf-dir-recursive <root_artifact> <leaf_artifact_dir> [leaf_count]|aggregate-pbs-chain-private-compact-leaf-dir-recursive <root_artifact> <leaf_artifact_dir> [leaf_count]|package-pbs-chain-frontier-recursive <frontier_artifact> <aggregate_artifact>...|package-pbs-chain-frontier-dir-recursive <frontier_artifact> <aggregate_artifact_dir>|verify-pbs-chain-root-artifact-recursive <root_artifact>|verify-pbs-chain-compact-root-artifact-recursive <root_artifact>|verify-pbs-chain-frontier-artifact-recursive <frontier_artifact>|inspect-pbs-chain-artifact <leaf|compact-leaf|node|compact-node|root|compact-root|frontier> <artifact>|bench-pbs-chain-private-recursive [toy|moderate|paper-v1] [chunk_steps] <chunk_count> <artifact_dir>|bench-pbs-chain-private-compact [toy|moderate|paper-v1] [chunk_steps] <chunk_count> <artifact_dir>|profile-pbs-chain-tree [toy|moderate|paper-v1] [chunk_steps] [total_steps]|prove-actual-pbs|profile-actual-pbs [toy|moderate|paper-v1]|run-actual-pbs-native [toy|moderate|paper-v1]]"
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

fn parse_required_chunk_count_arg(args: &[String]) -> Result<usize, Box<dyn Error>> {
    match args.get(4) {
        None => Err("chunk count is required".into()),
        Some(value) => {
            let parsed = value.parse::<usize>()?;
            if parsed == 0 {
                return Err("chunk count must be nonzero".into());
            }
            Ok(parsed)
        }
    }
}

fn parse_optional_leaf_count_arg(args: &[String]) -> Result<Option<usize>, Box<dyn Error>> {
    match args.get(4) {
        None => Ok(None),
        Some(value) => {
            let parsed = value.parse::<usize>()?;
            if parsed == 0 {
                return Err("leaf count must be nonzero".into());
            }
            Ok(Some(parsed))
        }
    }
}

fn parse_chunk_index_arg(args: &[String]) -> Result<usize, Box<dyn Error>> {
    match args.get(4) {
        None => Err("chunk index is required".into()),
        Some(value) => Ok(value.parse::<usize>()?),
    }
}

fn parse_required_arg<'a>(
    args: &'a [String],
    index: usize,
    name: &str,
) -> Result<&'a str, Box<dyn Error>> {
    args.get(index)
        .map(String::as_str)
        .ok_or_else(|| format!("{name} is required").into())
}

fn parse_repeated_args(
    args: &[String],
    start: usize,
    name: &str,
) -> Result<Vec<String>, Box<dyn Error>> {
    let values = args.get(start..).unwrap_or_default().to_vec();
    if values.is_empty() {
        Err(format!("{name} are required").into())
    } else {
        Ok(values)
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
