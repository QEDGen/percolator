//! Kernel-vs-spec proptests for `src/wide_math.rs`, closing the falcon-style
//! verification loop:
//!
//!   - Lean (formal_verification/) proves the math identity over ∀ inputs:
//!       lo + hi * 2^128 = a * b   in ℕ.
//!   - Kani (proofs_v16_arithmetic.rs) proves the operations against a
//!     small-reference at bounded inputs (≤ 40).
//!   - **This file** is the bridge: diff the production U256 / wide-math
//!     operations against a `num-bigint` reference at randomly-sampled
//!     u128 / u256 inputs across the full domain.
//!
//! The Lean theorems prove the *math* is correct over ∀ u128; the proptests
//! here prove the *Rust impl* tracks that math at runtime. Without this
//! file, the Lean theorems prove things about a Lean-side model only —
//! they don't catch drift in shipping Rust.
//!
//! See `formal_verification/Percolator/WideMath.lean` for the formal
//! statements these proptests operationally verify.

use num_bigint::{BigInt, BigUint, Sign};
use percolator::wide_math::{div_rem_u256, mul_div_floor_u256, I256, U256};
use proptest::prelude::*;

// ============================================================================
// U256 <-> BigUint bridges
// ============================================================================

/// Convert a U256 to a BigUint (the "spec" representation).
fn u256_to_biguint(x: U256) -> BigUint {
    BigUint::from(x.lo()) + (BigUint::from(x.hi()) << 128)
}

/// Convert a BigUint that fits in U256 back to U256, or None if it exceeds 2^256.
fn biguint_to_u256(x: &BigUint) -> Option<U256> {
    let limit_256 = BigUint::from(1u8) << 256;
    if x >= &limit_256 {
        return None;
    }
    let mask_128: BigUint = (BigUint::from(1u8) << 128) - 1u32;
    let lo_bigint: BigUint = x & &mask_128;
    let hi_bigint: BigUint = x >> 128;
    let lo: u128 = lo_bigint.try_into().ok()?;
    let hi: u128 = hi_bigint.try_into().ok()?;
    Some(U256::new(lo, hi))
}

/// Convert an I256 to a BigInt using `abs_u256` (magnitude) + `is_negative`/`is_zero`
/// (sign). Special-cases MIN since `abs_u256` panics on it.
fn i256_to_bigint(x: I256) -> BigInt {
    if x == I256::MIN {
        let m: BigInt = -(BigInt::from(1u8) << 255u32);
        return m;
    }
    let mag = u256_to_biguint(x.abs_u256());
    if x.is_negative() {
        BigInt::from_biguint(Sign::Minus, mag)
    } else {
        BigInt::from_biguint(Sign::Plus, mag)
    }
}

// ============================================================================
// Refinement proptests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// **U256::checked_mul refinement**.
    ///
    /// For arbitrary U256 inputs `a`, `b`, the production `checked_mul`
    /// returns `Some(p)` iff the unbounded product `a · b` fits in U256,
    /// and `p` equals that product. Diffs against a BigUint spec.
    ///
    /// This is the Rust-runtime correspondent of the Lean theorem
    /// `wideningMulU128_correct` + the inner-cross-product accounting
    /// done by `U256::checkedMul` (Lean spec at
    /// `formal_verification/Percolator/U256.lean`).
    #[test]
    fn u256_checked_mul_matches_biguint_spec(
        a_lo: u128, a_hi: u128, b_lo: u128, b_hi: u128,
    ) {
        let a = U256::new(a_lo, a_hi);
        let b = U256::new(b_lo, b_hi);

        let bigint_product = u256_to_biguint(a) * u256_to_biguint(b);
        let expected = biguint_to_u256(&bigint_product);
        let got = a.checked_mul(b);

        match (got, expected) {
            (Some(g), Some(e)) => {
                prop_assert_eq!(
                    u256_to_biguint(g),
                    u256_to_biguint(e),
                    "checked_mul returned a value but it disagrees with the spec"
                );
            }
            (None, None) => {
                // Both agree: product overflows U256.
            }
            (Some(g), None) => {
                prop_assert!(
                    false,
                    "checked_mul returned Some({}, {}) but spec says overflow",
                    g.lo(),
                    g.hi()
                );
            }
            (None, Some(_)) => {
                prop_assert!(
                    false,
                    "checked_mul returned None but spec says product fits ({} bits)",
                    bigint_product.bits()
                );
            }
        }
    }

    /// **`mul_div_floor_u256` refinement** at u128-shaped inputs.
    ///
    /// `mul_div_floor_u256(a, b, d)` computes `floor((a · b) / d)`. We
    /// restrict to U128-sized inputs here so the quotient fits in U256
    /// without further bookkeeping (since `(2^128 - 1)^2 / 1 < 2^256`).
    ///
    /// Diffs against a BigUint spec. This is the operationally important
    /// refinement — `mul_div_floor_u256` is called 4× in
    /// `proofs_v16_arithmetic.rs` at bounded inputs ≤ 40; this lifts to
    /// arbitrary u128 sampling.
    #[test]
    fn mul_div_floor_u256_matches_biguint_spec_u128_inputs(
        a: u128,
        b: u128,
        d in 1u128..,  // exclude zero
    ) {
        let a256 = U256::from_u128(a);
        let b256 = U256::from_u128(b);
        let d256 = U256::from_u128(d);

        let got = mul_div_floor_u256(a256, b256, d256);
        let spec_bigint = (BigUint::from(a) * BigUint::from(b)) / BigUint::from(d);

        prop_assert_eq!(
            u256_to_biguint(got),
            spec_bigint,
            "mul_div_floor_u256({}, {}, {}) drift from floor((a·b)/d)",
            a,
            b,
            d
        );
    }

    /// **`div_rem_u256` refinement**: matches the division identity
    /// `n = q · d + r ∧ r < d` against a BigUint reference.
    ///
    /// This is the Rust-runtime correspondent of the Lean theorem
    /// `Percolator.U256.divRemU256_correct` (formal_verification/
    /// Percolator/U256.lean). The Lean theorem proves the division
    /// identity over arbitrary Nat; this proptest checks that the
    /// production binary-long-division kernel computes the same result
    /// as the BigUint reference at randomly-sampled u256 inputs.
    #[test]
    fn div_rem_u256_matches_biguint_spec(
        n_lo: u128,
        n_hi: u128,
        d_lo: u128,
        d_hi: u128,
    ) {
        prop_assume!(d_lo != 0 || d_hi != 0);
        let n = U256::new(n_lo, n_hi);
        let d = U256::new(d_lo, d_hi);
        let (q, r) = div_rem_u256(n, d);

        let n_bi = u256_to_biguint(n);
        let d_bi = u256_to_biguint(d);
        let expected_q = &n_bi / &d_bi;
        let expected_r = &n_bi % &d_bi;

        prop_assert_eq!(u256_to_biguint(q), expected_q.clone(),
            "div_rem_u256 quotient drift");
        prop_assert_eq!(u256_to_biguint(r), expected_r.clone(),
            "div_rem_u256 remainder drift");
        // Division identity: n = q · d + r
        prop_assert_eq!(expected_q * &d_bi + &expected_r, n_bi);
        // Remainder bound
        prop_assert!(expected_r < d_bi);
    }

    /// **`I256::checked_neg` refinement**: matches BigInt negation,
    /// fails iff input is I256::MIN.
    ///
    /// Rust-runtime correspondent of the Lean theorem
    /// `Percolator.I256.checkedNeg_correct` (formal_verification/
    /// Percolator/I256.lean). The Lean theorem proves the two's-complement
    /// `~x + 1` matches Int negation on the toInt semantics.
    ///
    /// Input domain note: i128 generation covers values in
    /// `[I256::MIN/2^128, I256::MAX/2^128]` after sign-extension via
    /// `from_i128`. This exercises the carry-propagation paths in the
    /// limb-level negation while keeping the bridge convertible.
    #[test]
    fn i256_checked_neg_matches_bigint_spec(v: i128) {
        let x = I256::from_i128(v);
        let got = x.checked_neg();

        let x_bi = i256_to_bigint(x);
        let neg_bi = -x_bi.clone();
        let i256_min_bi: BigInt = -(BigInt::from(1u8) << 255u32);

        // Spec: fails iff input is exactly I256::MIN
        let expected_some = x_bi != i256_min_bi;

        match (got, expected_some) {
            (Some(g), true) => {
                prop_assert_eq!(
                    i256_to_bigint(g),
                    neg_bi,
                    "checked_neg returned a value but it disagrees with -x"
                );
            }
            (None, false) => {}
            (Some(_), false) => {
                prop_assert!(
                    false,
                    "checked_neg(MIN) returned Some, but -MIN doesn't fit"
                );
            }
            (None, true) => {
                prop_assert!(
                    false,
                    "checked_neg returned None for non-MIN input v={}",
                    v
                );
            }
        }
    }

    /// **`I256::abs_u256` refinement**: matches BigInt absolute value
    /// (returning a U256), panics on I256::MIN.
    ///
    /// Rust-runtime correspondent of the Lean theorem
    /// `Percolator.I256.absU256_correct` (formal_verification/
    /// Percolator/I256.lean). MIN-input panic is verified separately
    /// because proptest can't catch panics in the closure.
    #[test]
    fn i256_abs_u256_matches_bigint_spec(v: i128) {
        let x = I256::from_i128(v);
        // Skip MIN — abs_u256 panics by design (caller contract).
        prop_assume!(x != I256::MIN);

        let got = x.abs_u256();
        let x_bi = i256_to_bigint(x);
        let abs_bi: BigUint = x_bi.magnitude().clone();

        prop_assert_eq!(
            u256_to_biguint(got),
            abs_bi,
            "abs_u256 drift from |x| for v={}",
            v
        );
    }

    /// **`I256::checked_mul_i256` refinement**: matches BigInt multiplication
    /// when the product fits in I256, returns None otherwise.
    ///
    /// Rust-runtime correspondent of the Lean theorem
    /// `Percolator.I256.checkedMulInt_some` / `checkedMulInt_none`
    /// (abstract Int-level spec at formal_verification/Percolator/I256.lean).
    /// The Rust impl decomposes via sign/magnitude + U256.checked_mul,
    /// whose schoolbook correctness rests on `Percolator.U256.checkedMul_correct`.
    #[test]
    fn i256_checked_mul_matches_bigint_spec(a: i128, b: i128) {
        let xa = I256::from_i128(a);
        let xb = I256::from_i128(b);
        let got = xa.checked_mul_i256(xb);

        let prod_bi = i256_to_bigint(xa) * i256_to_bigint(xb);
        let i256_min_bi: BigInt = -(BigInt::from(1u8) << 255u32);
        let i256_max_bi: BigInt = (BigInt::from(1u8) << 255u32) - 1u32;
        let fits = prod_bi >= i256_min_bi && prod_bi <= i256_max_bi;

        match (got, fits) {
            (Some(g), true) => {
                prop_assert_eq!(
                    i256_to_bigint(g),
                    prod_bi,
                    "checked_mul_i256 returned a value but it disagrees with a*b"
                );
            }
            (None, false) => {}
            (Some(g), false) => {
                prop_assert!(
                    false,
                    "checked_mul_i256({}, {}) returned Some({:?}) but spec says overflow ({} bits)",
                    a,
                    b,
                    i256_to_bigint(g),
                    prod_bi.bits()
                );
            }
            (None, true) => {
                prop_assert!(
                    false,
                    "checked_mul_i256({}, {}) returned None but product fits in I256",
                    a,
                    b
                );
            }
        }
    }
}
