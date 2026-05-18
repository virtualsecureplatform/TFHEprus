#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Params {
    pub lwe_dimension: usize,
    pub polynomial_size: usize,
    pub glwe_dimension: usize,
    pub decomposition_base_log: usize,
    pub decomposition_level_count: usize,
    pub plaintext_modulus: u64,
}

impl Params {
    pub fn new(
        lwe_dimension: usize,
        polynomial_size: usize,
        glwe_dimension: usize,
        decomposition_base_log: usize,
        decomposition_level_count: usize,
        plaintext_modulus: u64,
    ) -> Self {
        assert!(lwe_dimension > 0);
        assert!(polynomial_size.is_power_of_two());
        assert!(glwe_dimension > 0);
        assert!((1..=32).contains(&decomposition_base_log));
        assert!(decomposition_level_count > 0);
        assert!(decomposition_base_log * decomposition_level_count <= 64);
        assert!(plaintext_modulus > 1);
        Self {
            lwe_dimension,
            polynomial_size,
            glwe_dimension,
            decomposition_base_log,
            decomposition_level_count,
            plaintext_modulus,
        }
    }

    /// Small exact-decomposition parameters used by fast correctness tests.
    pub fn toy() -> Self {
        Self::new(8, 8, 1, 16, 4, 4)
    }

    /// Medium-sized exact-decomposition parameters for native PBS profiling.
    ///
    /// This is still not a secure TFHE parameter set. It keeps the same exact
    /// Goldilocks gadget decomposition as `toy()` but increases both the LWE
    /// dimension and polynomial size enough to make transform/key bottlenecks
    /// visible in local benchmark runs.
    pub fn moderate_toy() -> Self {
        Self::new(32, 64, 1, 16, 4, 4)
    }

    /// The parameter shape described in 451.pdf. This is available for API
    /// integration, but v1 correctness tests use `toy()` until the approximate
    /// TFHE decomposition and key switch are implemented.
    pub fn paper_v1() -> Self {
        Self::new(728, 1024, 1, 5, 4, 4)
    }

    pub fn gadget_base(&self) -> u64 {
        1u64 << self.decomposition_base_log
    }

    pub fn exponent_modulus(&self) -> usize {
        2 * self.polynomial_size
    }
}
