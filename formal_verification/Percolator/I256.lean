/-
  Percolator.I256 — Two's-complement i256 refinement.

  Production `src/wide_math.rs::I256` is `[u128; 2]` (kani) / `[u64; 4]`
  (BPF) interpreted as two's complement: the sign bit is bit 127 of the
  high u128 limb (`hi ≥ 2^127` ⟺ value is negative). This file lifts
  that to a Nat-limb Lean model and proves the bit-twiddling operations
  match Int-valued semantics.

  Pattern mirrors `Percolator.U256`:
    1. `toInt` maps (lo, hi) ∈ [0, TWO_128)² to an Int ∈ [-2^255, 2^255).
    2. Limb-level operations (`checkedNeg`, `absU256`, `checkedMul`)
       mirror the Rust impl's bit-twiddling.
    3. Correctness theorems show the limb-level computation matches the
       Int-valued spec, e.g. `toInt (checkedNeg lo hi) = -toInt (lo, hi)`.

  The Rust↔Lean bridge for the bit-level u128 ops (`!x`, `overflowing_add`,
  `wrapping_add`) is the proptest in `tests/proofs_v16_lean_refinement.rs`.
-/

import Percolator.Defs
import Percolator.UInt128
import Percolator.WideMath
import Percolator.U256
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Percolator.Spec

namespace I256

-- ============================================================================
-- Width and sentinel constants
-- ============================================================================

/-- 2^127 — the sign-bit threshold for the hi limb. -/
def TWO_127 : Nat := 2^127

/-- 2^255 — magnitude of `I256::MIN`. -/
def TWO_255 : Nat := 2^255

/-- I256::MIN low limb. -/
def MIN_LO : Nat := 0

/-- I256::MIN high limb (2^127 = sign bit set, all other bits zero). -/
def MIN_HI : Nat := TWO_127

-- ============================================================================
-- Width arithmetic facts
-- ============================================================================

theorem TWO_127_pos : 0 < TWO_127 := by unfold TWO_127; norm_num
theorem TWO_128_pos : 0 < TWO_128 := by unfold TWO_128; norm_num
theorem TWO_256_pos : 0 < TWO_256 := by unfold TWO_256; norm_num
theorem TWO_127_lt_TWO_128 : TWO_127 < TWO_128 := by unfold TWO_127 TWO_128; norm_num
theorem TWO_128_sq : TWO_128 * TWO_128 = TWO_256 := by
  unfold TWO_128 TWO_256; ring
theorem TWO_127_mul_TWO_128 : TWO_127 * TWO_128 = TWO_255 := by
  unfold TWO_127 TWO_128 TWO_255; norm_num
theorem TWO_255_double : TWO_255 + TWO_255 = TWO_256 := by
  unfold TWO_255 TWO_256; norm_num

-- ============================================================================
-- Raw u256 interpretation and basic bounds
-- ============================================================================

/-- Raw u256 interpretation of the limb pair (unsigned). -/
def rawNat (lo hi : Nat) : Nat := lo + hi * TWO_128

/-- **Raw fits in u256**: any valid (lo, hi) ∈ [0, TWO_128)² has rawNat
    in `[0, TWO_256)`. -/
theorem rawNat_lt_TWO_256 (lo hi : Nat) (hlo : lo < TWO_128) (hhi : hi < TWO_128) :
    rawNat lo hi < TWO_256 := by
  unfold rawNat
  -- (hi + 1) * TWO_128 ≤ TWO_128 * TWO_128 = TWO_256
  have hbound : hi * TWO_128 + TWO_128 ≤ TWO_128 * TWO_128 := by
    have hstep : (hi + 1) * TWO_128 ≤ TWO_128 * TWO_128 :=
      Nat.mul_le_mul_right TWO_128 (by omega)
    have : (hi + 1) * TWO_128 = hi * TWO_128 + TWO_128 := by ring
    linarith
  rw [← TWO_128_sq]; linarith

/-- **Sign iff raw bound**: for valid limbs (lo, hi < TWO_128),
    `hi ≥ TWO_127` ⟺ `rawNat lo hi ≥ TWO_255`. -/
theorem sign_iff_raw (lo hi : Nat) (hlo : lo < TWO_128) (hhi : hi < TWO_128) :
    TWO_127 ≤ hi ↔ TWO_255 ≤ rawNat lo hi := by
  unfold rawNat
  constructor
  · intro h
    have h1 : TWO_127 * TWO_128 ≤ hi * TWO_128 := Nat.mul_le_mul_right _ h
    rw [TWO_127_mul_TWO_128] at h1
    omega
  · intro h
    by_contra hn
    push_neg at hn  -- hi < TWO_127
    -- lo + hi*TWO_128 < TWO_128 + hi*TWO_128 = (hi + 1) * TWO_128 ≤ TWO_127 * TWO_128 = TWO_255
    have hbound : (hi + 1) * TWO_128 ≤ TWO_127 * TWO_128 :=
      Nat.mul_le_mul_right TWO_128 (by omega)
    have hexp : (hi + 1) * TWO_128 = hi * TWO_128 + TWO_128 := by ring
    rw [TWO_127_mul_TWO_128] at hbound
    linarith

-- ============================================================================
-- Abstract Int semantics
-- ============================================================================

/-- Two's-complement interpretation as an Int.

    `toInt lo hi = raw if hi < 2^127 (positive value),
                   raw - 2^256 if hi ≥ 2^127 (negative value)`. -/
def toInt (lo hi : Nat) : Int :=
  if hi < TWO_127 then (rawNat lo hi : Int)
  else (rawNat lo hi : Int) - (TWO_256 : Int)

-- ============================================================================
-- checked_neg — Lean spec for `wide_math.rs::I256::checked_neg`
-- ============================================================================

/-- Two's-complement limb-level negation: `~x + 1` with carry.

    Shared core of `checkedNeg` and `absU256` (negative branch). Bitwise-not
    of a u128 value `x < TWO_128` equals `TWO_128 - 1 - x`. -/
def negLimbs (lo hi : Nat) : Nat × Nat :=
  let inv_lo := TWO_128 - 1 - lo
  let inv_hi := TWO_128 - 1 - hi
  let neg_lo_raw := inv_lo + 1
  let neg_lo := neg_lo_raw % TWO_128
  let carry : Nat := if neg_lo_raw ≥ TWO_128 then 1 else 0
  let neg_hi := (inv_hi + carry) % TWO_128
  (neg_lo, neg_hi)

/-- Lean spec mirror of `wide_math.rs::I256::checked_neg`.

    Returns none on MIN (whose negation +2^255 doesn't fit in i256);
    otherwise returns the limb-level two's-complement negation. -/
def checkedNeg (lo hi : Nat) : Option (Nat × Nat) :=
  if lo = MIN_LO ∧ hi = MIN_HI then none
  else some (negLimbs lo hi)

/-- **Raw complement** of `negLimbs`: the limb-level `~x + 1` operation
    produces a result `(nl, nh)` such that

      `rawNat nl nh + rawNat lo hi = TWO_256`  (when input ≠ 0)
      `rawNat nl nh = 0`                       (when input = 0)

    Phrased as the two-case disjunction. Both limbs are valid u128. -/
theorem negLimbs_raw
    (lo hi : Nat) (hlo : lo < TWO_128) (hhi : hi < TWO_128) :
    ∃ nl nh, negLimbs lo hi = (nl, nh)
           ∧ nl < TWO_128 ∧ nh < TWO_128
           ∧ ((lo = 0 ∧ hi = 0 ∧ nl = 0 ∧ nh = 0)
              ∨ rawNat nl nh + rawNat lo hi = TWO_256) := by
  have h128_pos : 0 < TWO_128 := TWO_128_pos
  unfold negLimbs
  refine ⟨_, _, rfl, Nat.mod_lt _ h128_pos, Nat.mod_lt _ h128_pos, ?_⟩
  by_cases hlo0 : lo = 0
  · subst hlo0
    -- inv_lo + 1 = TWO_128 ⇒ neg_lo = 0, carry = 1
    have hinv1 : TWO_128 - 1 - 0 + 1 = TWO_128 := by omega
    have hcarry : (TWO_128 - 1 - 0 + 1) ≥ TWO_128 := by omega
    have hneg_lo : (TWO_128 - 1 - 0 + 1) % TWO_128 = 0 := by
      rw [hinv1]; exact Nat.mod_self _
    by_cases hhi0 : hi = 0
    · subst hhi0
      left
      refine ⟨rfl, rfl, ?_, ?_⟩
      · -- (TWO_128 - 1 - 0 + 1) % TWO_128 = 0
        have heq : TWO_128 - 1 - 0 + 1 = TWO_128 := by omega
        rw [heq]; exact Nat.mod_self _
      · -- (TWO_128 - 1 - 0 + carry) % TWO_128 = 0 where carry = 1
        rw [if_pos hcarry]
        -- Goal: (TWO_128 - 1 - 0 + 1) % TWO_128 = 0
        have heq : TWO_128 - 1 - 0 + 1 = TWO_128 := by omega
        rw [heq]; exact Nat.mod_self _
    · right
      have hhip : 0 < hi := Nat.pos_of_ne_zero hhi0
      have hsub_lt : TWO_128 - hi < TWO_128 := by omega
      have hinv_hi_eq : TWO_128 - 1 - hi + 1 = TWO_128 - hi := by omega
      have hneg_hi : (TWO_128 - 1 - hi + 1) % TWO_128 = TWO_128 - hi := by
        rw [hinv_hi_eq]; exact Nat.mod_eq_of_lt hsub_lt
      unfold rawNat
      rw [hneg_lo, if_pos hcarry, hneg_hi]
      -- Goal: 0 + (TWO_128 - hi) * TWO_128 + (0 + hi * TWO_128) = TWO_256
      have hexp : (TWO_128 - hi) * TWO_128 = TWO_128 * TWO_128 - hi * TWO_128 := by
        rw [Nat.sub_mul]
      have hh_le : hi * TWO_128 ≤ TWO_128 * TWO_128 :=
        Nat.mul_le_mul_right _ (by omega)
      rw [← TWO_128_sq]; omega
  · right
    have hlop : 0 < lo := Nat.pos_of_ne_zero hlo0
    -- inv_lo + 1 = TWO_128 - lo < TWO_128 ⇒ neg_lo = TWO_128 - lo, carry = 0
    have hinv_lo_eq : TWO_128 - 1 - lo + 1 = TWO_128 - lo := by omega
    have hsub_lo_lt : TWO_128 - lo < TWO_128 := by omega
    have hneg_lo : (TWO_128 - 1 - lo + 1) % TWO_128 = TWO_128 - lo := by
      rw [hinv_lo_eq]; exact Nat.mod_eq_of_lt hsub_lo_lt
    have hno_carry : ¬(TWO_128 - 1 - lo + 1 ≥ TWO_128) := by omega
    have hsub_hi_lt : TWO_128 - 1 - hi < TWO_128 := by omega
    have hneg_hi : (TWO_128 - 1 - hi + 0) % TWO_128 = TWO_128 - 1 - hi := by
      simp; exact Nat.mod_eq_of_lt hsub_hi_lt
    unfold rawNat
    rw [hneg_lo, if_neg hno_carry, hneg_hi]
    -- Goal: (TWO_128 - lo) + (TWO_128 - 1 - hi) * TWO_128 + (lo + hi * TWO_128) = TWO_256
    -- Use: (TWO_128 - 1 - hi) * TWO_128 + hi * TWO_128 + TWO_128 = TWO_128 * TWO_128
    have hexp : (TWO_128 - 1 - hi) * TWO_128 + (hi + 1) * TWO_128
              = TWO_128 * TWO_128 := by
      have : (TWO_128 - 1 - hi) * TWO_128 + (hi + 1) * TWO_128
           = ((TWO_128 - 1 - hi) + (hi + 1)) * TWO_128 := by ring
      rw [this]
      have hsum : (TWO_128 - 1 - hi) + (hi + 1) = TWO_128 := by omega
      rw [hsum]
    have hexp2 : (hi + 1) * TWO_128 = hi * TWO_128 + TWO_128 := by ring
    rw [← TWO_128_sq]
    have h128_pos : 0 < TWO_128 := TWO_128_pos
    omega

/-- **`checkedNeg` correctness**: matches Int negation on the toInt semantics,
    succeeds iff not MIN.

    For `some (nl, nh)`: limbs are valid u128 and `toInt nl nh = -toInt lo hi`.
    For `none`: input was I256::MIN. -/
theorem checkedNeg_correct
    (lo hi : Nat) (hlo : lo < TWO_128) (hhi : hi < TWO_128) :
    match checkedNeg lo hi with
    | some (nl, nh) =>
        nl < TWO_128 ∧ nh < TWO_128 ∧ toInt nl nh = -(toInt lo hi)
    | none => lo = MIN_LO ∧ hi = MIN_HI := by
  by_cases hmin : lo = MIN_LO ∧ hi = MIN_HI
  · unfold checkedNeg
    rw [if_pos hmin]
    exact hmin
  obtain ⟨nl, nh, hres, hnl_lt, hnh_lt, hraw⟩ := negLimbs_raw lo hi hlo hhi
  unfold checkedNeg
  rw [if_neg hmin, hres]
  refine ⟨hnl_lt, hnh_lt, ?_⟩
  rcases hraw with ⟨hlo0, hhi0, hnl0, hnh0⟩ | hcomp
  · -- Input = 0; result = 0; toInt 0 0 = 0
    subst hlo0 hhi0 hnl0 hnh0
    unfold toInt rawNat
    simp [TWO_127_pos]
  · -- Non-zero input. Show toInt nl nh = -toInt lo hi using the
    -- complementary identity rawNat nl nh + rawNat lo hi = TWO_256.
    have hraw_in_lt : rawNat lo hi < TWO_256 := rawNat_lt_TWO_256 lo hi hlo hhi
    have hraw_in_pos : 0 < rawNat lo hi := by
      by_contra hn
      push_neg at hn
      have heq : rawNat lo hi = 0 := by omega
      unfold rawNat at heq
      have hlo_eq : lo = 0 := by omega
      have hhi_eq : hi = 0 := by
        have : hi * TWO_128 = 0 := by omega
        rcases Nat.mul_eq_zero.mp this with h | h
        · exact h
        · exfalso; have := TWO_128_pos; omega
      subst hlo_eq hhi_eq
      -- Then rawNat nl nh = TWO_256, contradicting nl, nh < TWO_128
      have : rawNat nl nh = TWO_256 := by
        have := hcomp; unfold rawNat at this ⊢; omega
      have hbound : rawNat nl nh < TWO_256 := rawNat_lt_TWO_256 nl nh hnl_lt hnh_lt
      omega
    have hraw_res_lt : rawNat nl nh < TWO_256 := rawNat_lt_TWO_256 nl nh hnl_lt hnh_lt
    -- rawNat nl nh = TWO_256 - rawNat lo hi
    have hres_eq : rawNat nl nh = TWO_256 - rawNat lo hi := by omega
    -- Exclude the MIN input (raw = TWO_255 ⇔ lo = 0, hi = TWO_127)
    have hno_min : rawNat lo hi ≠ TWO_255 := by
      intro heq
      -- rawNat = TWO_255 ⇒ hi = TWO_127 and lo = 0 (MIN)
      have hhi_ge : TWO_127 ≤ hi := by
        rw [sign_iff_raw lo hi hlo hhi]; omega
      have hhi_eq : hi = TWO_127 := by
        by_contra hn
        have hgt : hi > TWO_127 := by omega
        have h1 : TWO_127 * TWO_128 < hi * TWO_128 :=
          (Nat.mul_lt_mul_right TWO_128_pos).mpr hgt
        rw [TWO_127_mul_TWO_128] at h1
        unfold rawNat at heq; omega
      have hlo_eq : lo = 0 := by
        subst hhi_eq
        rw [← TWO_127_mul_TWO_128] at heq
        unfold rawNat at heq
        omega
      exact hmin ⟨hlo_eq, hhi_eq⟩
    unfold toInt
    by_cases hin_sign : hi < TWO_127
    · -- Input positive ⇒ raw_in < TWO_255 ⇒ raw_res > TWO_255 ⇒ result negative
      have hin_lt : rawNat lo hi < TWO_255 := by
        by_contra hn; push_neg at hn
        have := (sign_iff_raw lo hi hlo hhi).mpr hn; omega
      have hres_gt : TWO_255 < rawNat nl nh := by
        have := TWO_255_double; omega
      have hres_ge : TWO_255 ≤ rawNat nl nh := by omega
      have hres_sign : TWO_127 ≤ nh := (sign_iff_raw nl nh hnl_lt hnh_lt).mpr hres_ge
      have hres_not_lt : ¬(nh < TWO_127) := by omega
      rw [if_pos hin_sign, if_neg hres_not_lt]
      -- Goal: (rawNat nl nh : Int) - TWO_256 = -(rawNat lo hi : Int)
      have hsum : (rawNat nl nh : Int) + (rawNat lo hi : Int) = (TWO_256 : Int) := by
        exact_mod_cast hcomp
      linarith
    · push_neg at hin_sign
      have hin_ge : TWO_255 ≤ rawNat lo hi :=
        (sign_iff_raw lo hi hlo hhi).mp hin_sign
      have hin_gt : TWO_255 < rawNat lo hi := by omega
      have hres_lt : rawNat nl nh < TWO_255 := by
        have := TWO_255_double; omega
      have hres_sign : nh < TWO_127 := by
        by_contra hn; push_neg at hn
        have := (sign_iff_raw nl nh hnl_lt hnh_lt).mp hn; omega
      have hin_not_lt : ¬(hi < TWO_127) := by omega
      rw [if_neg hin_not_lt, if_pos hres_sign]
      have hsum : (rawNat nl nh : Int) + (rawNat lo hi : Int) = (TWO_256 : Int) := by
        exact_mod_cast hcomp
      linarith

-- ============================================================================
-- abs_u256 — Lean spec for `wide_math.rs::I256::abs_u256`
-- ============================================================================

/-- Lean spec mirror of `wide_math.rs::I256::abs_u256`.

    For non-negative inputs, returns the raw (lo, hi) interpreted as U256.
    For negative inputs (non-MIN), returns the bit-level negation
    (which equals the magnitude as U256).

    The Rust impl panics on MIN; the Lean spec returns `none` to reflect
    that contract — `|MIN| = 2^255` does fit in U256 but the bit-level
    `~x + 1` of MIN gives MIN back, not its magnitude. -/
def absU256 (lo hi : Nat) : Option (Nat × Nat) :=
  if lo = MIN_LO ∧ hi = MIN_HI then none
  else if hi < TWO_127 then some (lo, hi)
  else some (negLimbs lo hi)

/-- **`absU256` correctness**: returns the absolute value of `toInt lo hi`
    as a U256 raw representation, or `none` on MIN.

    For `some (al, ah)`: the U256 value `al + ah · TWO_128` equals
    `|toInt lo hi|` (as Int).
    For `none`: input was I256::MIN. -/
theorem absU256_correct
    (lo hi : Nat) (hlo : lo < TWO_128) (hhi : hi < TWO_128) :
    match absU256 lo hi with
    | some (al, ah) =>
        al < TWO_128 ∧ ah < TWO_128
        ∧ (rawNat al ah : Int) = (toInt lo hi).natAbs
    | none => lo = MIN_LO ∧ hi = MIN_HI := by
  by_cases hmin : lo = MIN_LO ∧ hi = MIN_HI
  · unfold absU256; rw [if_pos hmin]; exact hmin
  unfold absU256
  rw [if_neg hmin]
  by_cases hsign : hi < TWO_127
  · -- Non-negative ⇒ result is raw, toInt = raw (no subtraction)
    rw [if_pos hsign]
    refine ⟨hlo, hhi, ?_⟩
    unfold toInt
    rw [if_pos hsign]
    -- Goal: (rawNat lo hi : Int) = ((rawNat lo hi : Int)).natAbs
    have hpos : 0 ≤ (rawNat lo hi : Int) := by positivity
    rw [Int.natAbs_of_nonneg hpos]
  · -- Negative branch ⇒ reuse the negLimbs arithmetic identity
    rw [if_neg hsign]
    push_neg at hsign  -- TWO_127 ≤ hi
    obtain ⟨nl, nh, hres, hnl_lt, hnh_lt, hraw⟩ := negLimbs_raw lo hi hlo hhi
    rw [hres]
    refine ⟨hnl_lt, hnh_lt, ?_⟩
    -- Show (rawNat nl nh : Int) = (toInt lo hi).natAbs
    have hraw_lt : rawNat lo hi < TWO_256 := rawNat_lt_TWO_256 lo hi hlo hhi
    have hin_not_lt : ¬(hi < TWO_127) := by omega
    rcases hraw with ⟨_, hhi0, _, _⟩ | hcomp
    · -- Contradiction: hi = 0 contradicts TWO_127 ≤ hi
      have := TWO_127_pos; omega
    unfold toInt
    rw [if_neg hin_not_lt]
    -- Goal: (rawNat nl nh : Int) = ((rawNat lo hi : Int) - (TWO_256 : Int)).natAbs
    have hint_le : ((rawNat lo hi : Int) - (TWO_256 : Int)) ≤ 0 := by
      have hcast : ((rawNat lo hi : Nat) : Int) ≤ ((TWO_256 : Nat) : Int) :=
        Int.ofNat_le.mpr (le_of_lt hraw_lt)
      push_cast at hcast; linarith
    rw [Int.natCast_natAbs, abs_of_nonpos hint_le]
    have hsum : (rawNat nl nh : Int) + (rawNat lo hi : Int) = (TWO_256 : Int) := by
      exact_mod_cast hcomp
    linarith

-- ============================================================================
-- checked_mul — abstract Int-level spec for `wide_math.rs::I256::checked_mul_i256`
-- ============================================================================

/-- The smallest i256 value, as Int (`-2^255`). -/
def MIN_INT : Int := -(TWO_255 : Int)

/-- The largest i256 value, as Int (`2^255 - 1`). -/
def MAX_INT : Int := (TWO_255 : Int) - 1

/-- **Int-level `checkedMul` spec**: returns the product as Int when it
    fits in the i256 representational range `[MIN_INT, MAX_INT]`,
    `none` otherwise.

    This is the *abstract* spec — `wide_math.rs::I256::checked_mul_i256`
    implements it via sign/magnitude decomposition over the U256 schoolbook
    multiplication (`U256::checked_mul`). The Rust↔spec bridge is the
    proptest in `tests/proofs_v16_lean_refinement.rs`; the U256 schoolbook
    correctness underneath is `U256.checkedMul_correct`. -/
def checkedMulInt (x y : Int) : Option Int :=
  let p := x * y
  if MIN_INT ≤ p ∧ p ≤ MAX_INT then some p else none

/-- **`checkedMulInt` soundness**: when it returns `some p`, then `p = x · y`
    and `p` fits in the i256 range. -/
theorem checkedMulInt_some (x y p : Int) (h : checkedMulInt x y = some p) :
    p = x * y ∧ MIN_INT ≤ p ∧ p ≤ MAX_INT := by
  unfold checkedMulInt at h
  by_cases hbound : MIN_INT ≤ x * y ∧ x * y ≤ MAX_INT
  · rw [if_pos hbound] at h
    have hp : p = x * y := (Option.some.inj h).symm
    exact ⟨hp, by rw [hp]; exact hbound.1, by rw [hp]; exact hbound.2⟩
  · rw [if_neg hbound] at h; cases h

/-- **`checkedMulInt` completeness**: when it returns `none`, the product
    does not fit in i256. -/
theorem checkedMulInt_none (x y : Int) (h : checkedMulInt x y = none) :
    ¬(MIN_INT ≤ x * y ∧ x * y ≤ MAX_INT) := by
  unfold checkedMulInt at h
  by_cases hbound : MIN_INT ≤ x * y ∧ x * y ≤ MAX_INT
  · rw [if_pos hbound] at h; cases h
  · exact hbound

/-- **`checkedMulInt` agrees with raw `Int.mul`** for in-range products.
    Trivial unfold but documents the equivalence. -/
theorem checkedMulInt_eq_mul (x y : Int)
    (hin : MIN_INT ≤ x * y ∧ x * y ≤ MAX_INT) :
    checkedMulInt x y = some (x * y) := by
  unfold checkedMulInt; rw [if_pos hin]

end I256

end Percolator.Spec
