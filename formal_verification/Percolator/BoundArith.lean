/-
  Percolator.BoundArith — Bound-scale rounding refinements.

  Mirror of `src/v16.rs::amount_from_bound_num` (line 8339) and
  `bound_num_from_amount` (line 8349). The Rust impl converts between two
  representations of the same quantity:

    - `amount` (coarse units, e.g. tokens)
    - `bound_num` (fine units, equal to `amount · BOUND_SCALE` where BOUND_SCALE = 1e12)

  `amount_from_bound_num` rounds **up**: it returns the smallest amount whose
  bound_num is ≥ the input. This is the fail-safe direction for insurance-credit
  reservations — the engine MUST reserve at least the requested amount, never
  less, even after rounding.

  §14 invariants this file closes:
    - #15 `amount_from_bound_num_up_rounds_up_for_insurance_credit`
-/

import Percolator.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Percolator.Spec

-- ============================================================================
-- Width-of-scale lemmas
-- ============================================================================

theorem BOUND_SCALE_pos : 0 < BOUND_SCALE := by
  unfold BOUND_SCALE; norm_num

theorem POS_SCALE_pos : 0 < POS_SCALE := by
  unfold POS_SCALE; norm_num

-- ============================================================================
-- The ceiling-division function
-- ============================================================================

/-- Lean mirror of `amount_from_bound_num`: ceiling division by `BOUND_SCALE`.

    `bound_num` is the fine-grained representation (scaled by BOUND_SCALE);
    the function returns the coarse `amount` such that `amount · BOUND_SCALE ≥
    bound_num`, rounding up when there's any remainder. Lean's `Nat` is
    unbounded, so unlike Rust we don't model the `checked_add` overflow guard;
    that's a u128-boundary concern verified at the Rust side. -/
def amountFromBoundNum (bn : Nat) : Nat :=
  let whole := bn / BOUND_SCALE
  let rem := bn % BOUND_SCALE
  if rem = 0 then whole else whole + 1

/-- Lean mirror of `bound_num_from_amount`: exact multiplication, no rounding. -/
def boundNumFromAmount (amount : Nat) : Nat := amount * BOUND_SCALE

-- ============================================================================
-- Main theorem (§14 #15)
-- ============================================================================

/-- **Rounds up**: the result, when scaled back to bound_num, is at least the
    original `bn`. Concretely, `amountFromBoundNum bn · BOUND_SCALE ≥ bn`.

    Load-bearing for insurance-credit reservation: any reservation must cover
    the requested bound_num conservatively. Under-rounding would mean an
    insurance lien claims less actual capacity than its declared bound. -/
theorem amountFromBoundNum_rounds_up (bn : Nat) :
    bn ≤ amountFromBoundNum bn * BOUND_SCALE := by
  unfold amountFromBoundNum
  have hdm : BOUND_SCALE * (bn / BOUND_SCALE) + bn % BOUND_SCALE = bn :=
    Nat.div_add_mod bn BOUND_SCALE
  by_cases h : bn % BOUND_SCALE = 0
  · rw [if_pos h]
    -- bn = BOUND_SCALE * (bn / BOUND_SCALE), so bn ≤ (bn / BOUND_SCALE) * BOUND_SCALE
    rw [h] at hdm
    linarith
  · rw [if_neg h]
    -- (bn / BOUND_SCALE + 1) * BOUND_SCALE
    -- = (bn / BOUND_SCALE) * BOUND_SCALE + BOUND_SCALE
    -- ≥ bn since bn = q*s + r with r < s
    have hmod_lt : bn % BOUND_SCALE < BOUND_SCALE :=
      Nat.mod_lt bn BOUND_SCALE_pos
    nlinarith

/-- **Minimal**: the result is the SMALLEST `amount` whose scaled-up value
    covers `bn`. Equivalently, `amountFromBoundNum bn - 1` (when nonzero) is
    insufficient.

    Together with `rounds_up`, this characterizes `amountFromBoundNum` as the
    integer ceiling of `bn / BOUND_SCALE`. -/
theorem amountFromBoundNum_minimal (bn n : Nat)
    (h : n * BOUND_SCALE ≥ bn) :
    amountFromBoundNum bn ≤ n := by
  unfold amountFromBoundNum
  have hdm : BOUND_SCALE * (bn / BOUND_SCALE) + bn % BOUND_SCALE = bn :=
    Nat.div_add_mod bn BOUND_SCALE
  by_cases hr : bn % BOUND_SCALE = 0
  · rw [if_pos hr]
    -- Goal: bn / BOUND_SCALE ≤ n
    -- We have bn ≤ n * BOUND_SCALE and bn = BOUND_SCALE * (bn / BOUND_SCALE)
    rw [hr] at hdm
    -- hdm: BOUND_SCALE * (bn / BOUND_SCALE) + 0 = bn
    -- so BOUND_SCALE * (bn / BOUND_SCALE) ≤ n * BOUND_SCALE
    -- divide both sides by BOUND_SCALE (positive)
    have hpos := BOUND_SCALE_pos
    apply Nat.le_of_mul_le_mul_left
    · -- BOUND_SCALE * (bn / BOUND_SCALE) ≤ BOUND_SCALE * n
      calc BOUND_SCALE * (bn / BOUND_SCALE)
          = bn := by linarith
        _ ≤ n * BOUND_SCALE := h
        _ = BOUND_SCALE * n := by ring
    · exact hpos
  · rw [if_neg hr]
    -- Goal: bn / BOUND_SCALE + 1 ≤ n
    -- i.e. bn / BOUND_SCALE < n
    have hpos := BOUND_SCALE_pos
    have hmod_lt : bn % BOUND_SCALE < BOUND_SCALE :=
      Nat.mod_lt bn hpos
    have hmod_pos : 0 < bn % BOUND_SCALE := Nat.pos_of_ne_zero hr
    -- bn = BOUND_SCALE * (bn/s) + (bn%s)
    -- bn ≤ n * BOUND_SCALE
    -- So BOUND_SCALE * (bn/s) + (bn%s) ≤ n * BOUND_SCALE
    -- Since bn%s > 0, BOUND_SCALE * (bn/s) < n * BOUND_SCALE
    -- Divide by BOUND_SCALE: bn/s < n, i.e. bn/s + 1 ≤ n
    have hlt : BOUND_SCALE * (bn / BOUND_SCALE) < n * BOUND_SCALE := by
      have : BOUND_SCALE * (bn / BOUND_SCALE) + (bn % BOUND_SCALE) ≤ n * BOUND_SCALE := by
        linarith
      linarith
    have : bn / BOUND_SCALE < n := by
      apply Nat.lt_of_mul_lt_mul_left (a := BOUND_SCALE)
      calc BOUND_SCALE * (bn / BOUND_SCALE)
          < n * BOUND_SCALE := hlt
        _ = BOUND_SCALE * n := by ring
    omega

-- ============================================================================
-- Boundary behavior
-- ============================================================================

/-- **Exact when divisible**: if `bn` is a multiple of `BOUND_SCALE`, no rounding
    occurs — the result is exactly `bn / BOUND_SCALE`. This is the equality
    case of `rounds_up`. -/
theorem amountFromBoundNum_exact (bn : Nat) (h : bn % BOUND_SCALE = 0) :
    amountFromBoundNum bn * BOUND_SCALE = bn := by
  unfold amountFromBoundNum
  rw [if_pos h]
  have hdm : BOUND_SCALE * (bn / BOUND_SCALE) + bn % BOUND_SCALE = bn :=
    Nat.div_add_mod bn BOUND_SCALE
  rw [h] at hdm
  linarith

/-- **Zero in, zero out**. -/
theorem amountFromBoundNum_zero : amountFromBoundNum 0 = 0 := by
  unfold amountFromBoundNum
  simp

-- ============================================================================
-- Roundtrip
-- ============================================================================

/-- **`amount → bound_num → amount` is identity.** When we scale up an amount
    to its bound_num representation and then scale back down, no information
    is lost (and no rounding is needed). -/
theorem amount_bound_roundtrip (amount : Nat) :
    amountFromBoundNum (boundNumFromAmount amount) = amount := by
  unfold boundNumFromAmount amountFromBoundNum
  have hpos := BOUND_SCALE_pos
  have hne : BOUND_SCALE ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
  -- (amount * BOUND_SCALE) % BOUND_SCALE = 0
  have hmod : (amount * BOUND_SCALE) % BOUND_SCALE = 0 := by
    exact Nat.mul_mod_left amount BOUND_SCALE
  -- (amount * BOUND_SCALE) / BOUND_SCALE = amount
  have hdiv : (amount * BOUND_SCALE) / BOUND_SCALE = amount := by
    exact Nat.mul_div_cancel amount hpos
  rw [if_pos hmod, hdiv]

-- ============================================================================
-- Monotonicity
-- ============================================================================

/-- **Monotone**: bigger bound_num ⇒ at-least-as-big amount. Used downstream
    when refining bound estimates: a tightened bound never causes a smaller
    reservation. -/
theorem amountFromBoundNum_mono (a b : Nat) (h : a ≤ b) :
    amountFromBoundNum a ≤ amountFromBoundNum b := by
  -- Use the characterization: amountFromBoundNum a is the smallest n with
  -- n * BOUND_SCALE ≥ a. Then amountFromBoundNum b * BOUND_SCALE ≥ b ≥ a,
  -- so by minimality of amountFromBoundNum a, the latter ≤ amountFromBoundNum b.
  apply amountFromBoundNum_minimal
  calc a ≤ b := h
    _ ≤ amountFromBoundNum b * BOUND_SCALE := amountFromBoundNum_rounds_up b

end Percolator.Spec
