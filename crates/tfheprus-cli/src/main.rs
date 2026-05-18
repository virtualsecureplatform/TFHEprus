use tfheprus_core::Params;

fn main() {
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
