/-
  Percolator.U256 — Nat-based model of u256 arithmetic.

  Production `src/wide_math.rs::U256` is a wrapper around `[u64; 4]`
  (BPF target) or `[u128; 2]` (kani target), but for refinement purposes
  the cleanest abstraction is "two u128 limbs interpreted as
  lo + hi * 2^128 in ℕ".

  This file defines the abstract `toNat` interpretation and the
  schoolbook product-expansion identity needed by the `U256::checked_mul`
  refinement (to come in a follow-up).

  The Rust impl stores `(lo, hi)` as a `U256` struct. The Lean model
  represents the *same value* via `U256.toNat lo hi = lo + hi * TWO_128`.
  Refinement theorems show that the Rust operations map cleanly to
  Lean Nat operations on the `toNat` interpretation.
-/

import Percolator.Defs
import Percolator.UInt128
import Percolator.WideMath
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Percolator.Spec

namespace U256

/-- Interpret a U256 represented as (lo, hi) u128 limbs as a `Nat`.
    Mirrors the Rust embedding `U256.lo() | (U256.hi() << 128)`. -/
def toNat (lo hi : Nat) : Nat := lo + hi * TWO_128

/-- **U256 bound**: a valid U256 (both limbs in `[0, TWO_128)`) represents
    a value < TWO_256. Closes the abstraction obligation that the Rust
    `U256` type is a faithful Nat-in-[0, 2^256). -/
theorem toNat_lt (lo hi : Nat) (hlo : lo < TWO_128) (hhi : hi < TWO_128) :
    toNat lo hi < TWO_256 := by
  unfold toNat
  have h256_eq : TWO_128 * TWO_128 = TWO_256 := by unfold TWO_128 TWO_256; ring
  have h_TWO_128_pos : (0 : Nat) < TWO_128 := by unfold TWO_128; norm_num
  -- lo + hi * TWO_128 < TWO_256 = TWO_128 * TWO_128
  -- Worst case: lo = TWO_128 - 1, hi = TWO_128 - 1
  --   ⇒ lo + hi * TWO_128 = (TWO_128 - 1) + (TWO_128 - 1) * TWO_128
  --                       = TWO_128 - 1 + TWO_128² - TWO_128
  --                       = TWO_128² - 1 < TWO_128² = TWO_256
  rw [← h256_eq]
  nlinarith [hlo, hhi, h_TWO_128_pos]

/-- **U256 schoolbook product expansion**: the product of two U256 values
    decomposes into four cross-products by limb.

        toNat sl sh * toNat rl rh =
          sl·rl + (sl·rh + sh·rl) · TWO_128 + sh·rh · TWO_256

    Foundational identity for the `U256::checked_mul` refinement:
    the Rust implementation computes each cross-product separately
    (via `widening_mul_u128`) and assembles them; the theorem says the
    assembly produces the unbounded product. -/
theorem toNat_mul (sl sh rl rh : Nat) :
    toNat sl sh * toNat rl rh
    = sl * rl + (sl * rh + sh * rl) * TWO_128 + sh * rh * TWO_256 := by
  unfold toNat
  have h256_eq : TWO_128 * TWO_128 = TWO_256 := by unfold TWO_128 TWO_256; ring
  rw [← h256_eq]
  ring

/-- **Overflow condition**: if both U256 inputs have nonzero high limbs,
    their product exceeds TWO_256 (so doesn't fit in a U256).

    This is the algebraic justification for the Rust `checked_mul`'s
    first bailout: `if self.hi() != 0 && rhs.hi() != 0 { return None; }`.

    Note: the converse is NOT true — even with one high limb zero, the
    product can still overflow (e.g. `sh = 1, sl = 0, rh = 0,
    rl = TWO_128 - 1`: product = (TWO_128 - 1) · TWO_128 < TWO_256 but
    `sh = 1, sl = 0, rh = 0, rl = TWO_128 ...` wait — limbs are < TWO_128
    by construction, so this case can't overflow). Tighter analysis is
    done case-by-case in the actual `U256::checked_mul` refinement. -/
theorem both_hi_nonzero_overflows
    (sl sh rl rh : Nat) (hsh : 0 < sh) (hrh : 0 < rh)
    (hsl : sl < TWO_128) (hsh' : sh < TWO_128)
    (hrl : rl < TWO_128) (hrh' : rh < TWO_128) :
    TWO_256 ≤ toNat sl sh * toNat rl rh := by
  rw [toNat_mul]
  -- Goal: TWO_256 ≤ sl*rl + (sl*rh + sh*rl)*TWO_128 + sh*rh*TWO_256
  -- Since sh ≥ 1 and rh ≥ 1, sh*rh ≥ 1, so sh*rh*TWO_256 ≥ TWO_256.
  have h_sh_rh : 1 ≤ sh * rh := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h_term : TWO_256 ≤ sh * rh * TWO_256 := by
    calc TWO_256 = 1 * TWO_256 := (one_mul _).symm
      _ ≤ sh * rh * TWO_256 := Nat.mul_le_mul_right TWO_256 h_sh_rh
  omega

/-- **Widening-mul packaged as a U256 representation**: every valid u128
    pair `a, b < TWO_128` produces a U256-representable product. Bridges
    `wideningMulU128_correct` to the U256-typed setting that
    `U256::checked_mul` works in. -/
theorem fromU128Mul_exists (a b : Nat) (ha : a < TWO_128) (hb : b < TWO_128) :
    ∃ lo hi, lo < TWO_128 ∧ hi < TWO_128 ∧ toNat lo hi = a * b := by
  refine ⟨(wideningMulU128 a b).1, (wideningMulU128 a b).2, ?_, ?_, ?_⟩
  · exact wideningMulU128_lo_lt a b
  · exact wideningMulU128_hi_bounded a b ha hb
  · -- toNat lo hi = lo + hi*TWO_128, which equals a*b by wideningMulU128_correct
    unfold toNat
    exact wideningMulU128_correct a b ha hb

-- ============================================================================
-- U256::checked_mul — Lean transcription of `wide_math.rs:309-340`
-- ============================================================================

/-- Lean spec mirror of `wide_math.rs::U256::checked_mul`.

    Inputs: U256 limbs `(sl, sh)` and `(rl, rh)`, all in `[0, TWO_128)`.
    Returns `some (result_lo, result_hi)` when the product fits in U256,
    `none` otherwise.

    Note: the Rust impl skips computing `widening_mul` for cross terms
    when the corresponding hi limb is 0 (perf optimization). The Lean
    spec computes them unconditionally because `wideningMulU128 x 0 = (0, 0)`
    (proved separately) — so the unconditional form is mathematically
    equivalent but proof-friendlier (no match-block reduction issues).

    Bail conditions, in order:
    1. Both highs nonzero ⇒ definitely overflows.
    2. Either cross-product exceeds u128 (hi limb ≠ 0).
    3. Final hi sum exceeds u128. -/
def checkedMul (sl sh rl rh : Nat) : Option (Nat × Nat) :=
  if sh ≠ 0 ∧ rh ≠ 0 then none
  else
    let prod := wideningMulU128 sl rl
    let cross1 := wideningMulU128 sl rh
    let cross2 := wideningMulU128 sh rl
    if cross1.2 ≠ 0 ∨ cross2.2 ≠ 0 then none
    else
      let hi_sum := prod.2 + cross1.1 + cross2.1
      if hi_sum ≥ TWO_128 then none
      else some (prod.1, hi_sum)

/-- **`widening · 0` collapses**: multiplying by zero in widening_mul
    returns `(0, 0)`. Trivial corollary of `wideningMulU128_fits_u128`. -/
theorem wideningMulU128_zero_right (a : Nat) (ha : a < TWO_128) :
    wideningMulU128 a 0 = (0, 0) := by
  have h0 : isU128 0 := by unfold isU128 TWO_128; norm_num
  have hab : a * 0 < TWO_128 := by
    rw [Nat.mul_zero]; unfold TWO_128; norm_num
  have := wideningMulU128_fits_u128 a 0 ha h0 hab
  rw [Nat.mul_zero] at this
  exact this

theorem wideningMulU128_zero_left (b : Nat) (hb : b < TWO_128) :
    wideningMulU128 0 b = (0, 0) := by
  have h0 : isU128 0 := by unfold isU128 TWO_128; norm_num
  have hab : 0 * b < TWO_128 := by
    rw [Nat.zero_mul]; unfold TWO_128; norm_num
  have := wideningMulU128_fits_u128 0 b h0 hb hab
  rw [Nat.zero_mul] at this
  exact this

/-- **`checkedMul` reduces to widening for both-hi-zero inputs**.

    When `sh = rh = 0`, the cross terms collapse to `(0, 0)` and the
    final hi sum equals `(widening sl rl).hi < TWO_128`, so the
    function returns `some (widening sl rl)`. Operationally this is
    `U256::from_u128(x).checked_mul(U256::from_u128(y))`. -/
theorem checkedMul_both_hi_zero
    (sl rl : Nat) (hsl : sl < TWO_128) (hrl : rl < TWO_128) :
    checkedMul sl 0 rl 0 = some (wideningMulU128 sl rl) := by
  have h_prod_hi_lt : (wideningMulU128 sl rl).2 < TWO_128 :=
    wideningMulU128_hi_bounded sl rl hsl hrl
  have h_cross1 : wideningMulU128 sl 0 = (0, 0) := wideningMulU128_zero_right sl hsl
  have h_cross2 : wideningMulU128 0 rl = (0, 0) := wideningMulU128_zero_left rl hrl
  -- Unfold and apply guards in order
  unfold checkedMul
  rw [if_neg (by decide : ¬((0 : Nat) ≠ 0 ∧ (0 : Nat) ≠ 0))]
  rw [h_cross1, h_cross2]
  -- Now cross1.2 = 0 and cross2.2 = 0, so the disjunction is false
  rw [if_neg (by decide : ¬((0 : Nat) ≠ 0 ∨ (0 : Nat) ≠ 0))]
  -- hi_sum = prod.2 + 0 + 0 = prod.2 < TWO_128
  rw [if_neg (show ¬((wideningMulU128 sl rl).2 + 0 + 0 ≥ TWO_128) by linarith)]
  -- Goal: some (prod.1, prod.2 + 0 + 0) = some (wideningMulU128 sl rl)
  -- The +0+0 simplifies, then Prod eta closes via implicit rfl
  rw [show (wideningMulU128 sl rl).2 + 0 + 0 = (wideningMulU128 sl rl).2 from by ring]

/-- **`checkedMul` correctness**: matches the unbounded U256 product or
    signals overflow.

    Soundness: when `checkedMul` returns `some (lo, hi)`, the limbs are
    valid u128 and `toNat lo hi = toNat sl sh · toNat rl rh`.
    Completeness: when it returns `none`, the unbounded product overflows
    U256 (`≥ TWO_256`).

    Generalizes `checkedMul_both_hi_zero` to all valid (sh, rh) regimes:
    both-zero, one-zero, and both-nonzero (in which case the function
    correctly returns `none`).

    Closes the U256 schoolbook-multiplication refinement; downstream
    `mul_div_floor_u256` correctness rests on this. -/
theorem checkedMul_correct
    (sl sh rl rh : Nat)
    (hsl : sl < TWO_128) (hsh : sh < TWO_128)
    (hrl : rl < TWO_128) (hrh : rh < TWO_128) :
    match checkedMul sl sh rl rh with
    | some (lo, hi) =>
        lo < TWO_128 ∧ hi < TWO_128 ∧
        toNat lo hi = toNat sl sh * toNat rl rh
    | none => TWO_256 ≤ toNat sl sh * toNat rl rh := by
  -- Constants
  have h128_pos : (0 : Nat) < TWO_128 := by unfold TWO_128; norm_num
  have h128_sq : TWO_128 * TWO_128 = TWO_256 := by
    unfold TWO_128 TWO_256; ring

  -- Widening correctness on the three partial products
  have hprod_corr : (wideningMulU128 sl rl).1 + (wideningMulU128 sl rl).2 * TWO_128
                  = sl * rl := wideningMulU128_correct sl rl hsl hrl
  have hc1_corr  : (wideningMulU128 sl rh).1 + (wideningMulU128 sl rh).2 * TWO_128
                  = sl * rh := wideningMulU128_correct sl rh hsl hrh
  have hc2_corr  : (wideningMulU128 sh rl).1 + (wideningMulU128 sh rl).2 * TWO_128
                  = sh * rl := wideningMulU128_correct sh rl hsh hrl
  have hprod_lo_lt : (wideningMulU128 sl rl).1 < TWO_128 := wideningMulU128_lo_lt sl rl
  have hprod_hi_lt : (wideningMulU128 sl rl).2 < TWO_128 :=
    wideningMulU128_hi_bounded sl rl hsl hrl

  unfold checkedMul

  -- Case 1: both highs nonzero ⇒ none branch ⇒ overflow theorem applies
  by_cases h1 : sh ≠ 0 ∧ rh ≠ 0
  · rw [if_pos h1]
    obtain ⟨hshne, hrhne⟩ := h1
    exact both_hi_nonzero_overflows sl sh rl rh
      (Nat.pos_of_ne_zero hshne) (Nat.pos_of_ne_zero hrhne) hsl hsh hrl hrh

  rw [if_neg h1]
  -- ¬(sh ≠ 0 ∧ rh ≠ 0) ⇒ sh = 0 ∨ rh = 0 ⇒ sh · rh = 0
  have hshrh_zero : sh * rh = 0 := by
    push_neg at h1
    by_cases hsh0 : sh = 0
    · rw [hsh0]; ring
    · rw [h1 hsh0]; ring

  -- The product target, simplified using sh · rh = 0
  have hmul_simp : toNat sl sh * toNat rl rh
                 = sl * rl + (sl * rh + sh * rl) * TWO_128 := by
    rw [toNat_mul, hshrh_zero]; ring

  -- Case 2: a cross hi limb is nonzero ⇒ none branch ⇒ overflow
  by_cases h2 : (wideningMulU128 sl rh).2 ≠ 0 ∨ (wideningMulU128 sh rl).2 ≠ 0
  · rw [if_pos h2]
    -- Goal: TWO_256 ≤ toNat sl sh * toNat rl rh
    rw [hmul_simp]
    -- Show sl·rh + sh·rl ≥ TWO_128 from the surviving cross
    have hcross_ge : TWO_128 ≤ sl * rh + sh * rl := by
      rcases h2 with hc1 | hc2
      · have hc1p : 0 < (wideningMulU128 sl rh).2 := Nat.pos_of_ne_zero hc1
        have hge : TWO_128 ≤ (wideningMulU128 sl rh).2 * TWO_128 := by
          calc TWO_128 = 1 * TWO_128 := (one_mul _).symm
            _ ≤ (wideningMulU128 sl rh).2 * TWO_128 :=
                Nat.mul_le_mul_right TWO_128 hc1p
        omega
      · have hc2p : 0 < (wideningMulU128 sh rl).2 := Nat.pos_of_ne_zero hc2
        have hge : TWO_128 ≤ (wideningMulU128 sh rl).2 * TWO_128 := by
          calc TWO_128 = 1 * TWO_128 := (one_mul _).symm
            _ ≤ (wideningMulU128 sh rl).2 * TWO_128 :=
                Nat.mul_le_mul_right TWO_128 hc2p
        omega
    -- Then (sl·rh + sh·rl)·TWO_128 ≥ TWO_128² = TWO_256
    have hsq : TWO_128 * TWO_128 ≤ (sl * rh + sh * rl) * TWO_128 :=
      Nat.mul_le_mul_right TWO_128 hcross_ge
    rw [h128_sq] at hsq
    omega

  rw [if_neg h2]
  -- Both cross hi limbs are zero
  push_neg at h2
  obtain ⟨hc1z, hc2z⟩ := h2
  -- ⇒ cross.lo = sl·rh and sh·rl respectively
  have hc1_lo_eq : (wideningMulU128 sl rh).1 = sl * rh := by
    have := hc1_corr; rw [hc1z] at this; linarith
  have hc2_lo_eq : (wideningMulU128 sh rl).1 = sh * rl := by
    have := hc2_corr; rw [hc2z] at this; linarith

  -- Case 3: hi_sum ≥ TWO_128 ⇒ none branch ⇒ overflow
  by_cases h3 : (wideningMulU128 sl rl).2 + (wideningMulU128 sl rh).1
              + (wideningMulU128 sh rl).1 ≥ TWO_128
  · rw [if_pos h3]
    rw [hmul_simp]
    -- product = prod.1 + hi_sum · TWO_128
    have h_eq : sl * rl + (sl * rh + sh * rl) * TWO_128
              = (wideningMulU128 sl rl).1
                + ((wideningMulU128 sl rl).2 + (wideningMulU128 sl rh).1
                    + (wideningMulU128 sh rl).1) * TWO_128 := by
      rw [hc1_lo_eq, hc2_lo_eq, ← hprod_corr]; ring
    rw [h_eq]
    have : TWO_128 * TWO_128
        ≤ ((wideningMulU128 sl rl).2 + (wideningMulU128 sl rh).1
            + (wideningMulU128 sh rl).1) * TWO_128 :=
      Nat.mul_le_mul_right TWO_128 h3
    rw [h128_sq] at this
    linarith

  rw [if_neg h3]
  push_neg at h3
  -- Returns some (prod.1, hi_sum). Three obligations.
  refine ⟨hprod_lo_lt, h3, ?_⟩
  -- toNat prod.1 hi_sum = prod.1 + hi_sum · TWO_128 = toNat sl sh · toNat rl rh
  rw [hmul_simp]
  unfold toNat
  rw [hc1_lo_eq, hc2_lo_eq]
  -- LHS: prod.1 + (prod.2 + sl·rh + sh·rl) · TWO_128
  -- RHS: sl·rl + (sl·rh + sh·rl) · TWO_128
  -- Use hprod_corr: prod.1 + prod.2 · TWO_128 = sl · rl
  have h_expand :
      (wideningMulU128 sl rl).1
        + ((wideningMulU128 sl rl).2 + sl * rh + sh * rl) * TWO_128
      = ((wideningMulU128 sl rl).1 + (wideningMulU128 sl rl).2 * TWO_128)
        + (sl * rh + sh * rl) * TWO_128 := by ring
  rw [h_expand, hprod_corr]

-- ============================================================================
-- div_rem_u256 — Lean spec for `wide_math.rs::div_rem_u256` (binary long division)
-- ============================================================================

/-- Lean spec mirror of `wide_math.rs::div_rem_u256`.

    The production Rust implementation is binary long division on 256-bit
    limbs (see `wide_math.rs:1103-1141`); its observable input/output
    behavior is "given `num`, `den` in `[0, TWO_256)` with `den > 0`,
    return `(num / den, num % den)`". The Lean spec is the latter — the
    Rust↔spec bridge is the proptest in
    `tests/proofs_v16_lean_refinement.rs`.

    Inputs are abstract Nats here; the Rust impl's per-limb arithmetic is
    not modeled at the Lean level (it would only re-prove what
    `Nat.div_add_mod` already gives us). -/
def divRemU256 (num den : Nat) : Nat × Nat := (num / den, num % den)

/-- **Division identity**: for any nonzero denominator,
    `num = quotient · den + remainder` and `remainder < den`.

    Closes the §14 obligation that `U256::checked_div` / `checked_rem`
    satisfy the textbook division relation. The Rust binary-long-division
    implementation is bridged to this spec by
    `div_rem_u256_matches_biguint_spec`. -/
theorem divRemU256_correct (num den : Nat) (hden : 0 < den) :
    let (q, r) := divRemU256 num den
    num = q * den + r ∧ r < den := by
  refine ⟨?_, ?_⟩
  · show num = (num / den) * den + num % den
    have h := Nat.div_add_mod num den
    -- h : den * (num / den) + num % den = num
    linarith [Nat.mul_comm den (num / den)]
  · show num % den < den
    exact Nat.mod_lt _ hden

/-- **Quotient bound**: the quotient never exceeds `num`. Useful for
    showing the quotient fits in U256 whenever `num` does. -/
theorem divRemU256_quotient_le (num den : Nat) :
    (divRemU256 num den).1 ≤ num := by
  show num / den ≤ num
  exact Nat.div_le_self num den

/-- **Remainder bound by num**: the remainder never exceeds `num`. -/
theorem divRemU256_remainder_le (num den : Nat) :
    (divRemU256 num den).2 ≤ num := by
  show num % den ≤ num
  exact Nat.mod_le num den

/-- **Result fits in U256**: when both inputs are valid U256 values
    (< TWO_256), both quotient and remainder fit in U256. Discharges the
    implicit precondition that `div_rem_u256` produces well-formed U256
    outputs. -/
theorem divRemU256_lt_TWO_256
    (num den : Nat) (hnum : num < TWO_256) :
    (divRemU256 num den).1 < TWO_256 ∧ (divRemU256 num den).2 < TWO_256 := by
  refine ⟨?_, ?_⟩
  · exact Nat.lt_of_le_of_lt (divRemU256_quotient_le num den) hnum
  · exact Nat.lt_of_le_of_lt (divRemU256_remainder_le num den) hnum

end U256

end Percolator.Spec
