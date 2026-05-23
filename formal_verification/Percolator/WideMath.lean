/-
  Percolator.WideMath — Refinement theorems for `src/wide_math.rs`.

  This file mirrors `wide_math.rs` operations as Lean definitions and proves
  each one matches its textbook-arithmetic specification. The pattern is the
  same as falcon512's `Falcon512/Refinement.lean`: production Rust uses
  bit-twiddling tricks (lazy reduction, lazy-t offsets, fused norms for
  falcon; u64-halved schoolbook + wrapping ops for percolator); Lean proves
  the trick computes the textbook value.

  Order of theorems (smallest first):

    1. `wideningMulU128_correct` — u128 × u128 → (lo, hi) decomposition
       satisfies `lo + hi · 2^128 = a · b` in ℕ.

    2. `wideningMulU128_hi_bounded` — corollary: under `a, b < 2^128`, the
       hi limb fits in u128 (`hi < 2^128`). Closes the implicit precondition
       that `U256::checked_mul` relies on.

  Phase 1 follow-ons (closed; see linked files):

    3. `U256.checkedMul_correct` — generalized schoolbook for U256 × U256
       → U256 with explicit overflow. Lives in `Percolator/U256.lean`.

    4. `U256.divRemU256_correct` — `num = quotient · den + remainder
       ∧ remainder < den`. Lives in `Percolator/U256.lean`.

    5. `I256.checkedNeg_correct`, `I256.absU256_correct`,
       `I256.checkedMulInt_*` — two's-complement signed-arithmetic
       refinements. Live in `Percolator/I256.lean`.
-/

import Percolator.Defs
import Percolator.UInt128
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Defs

namespace Percolator.Spec

-- ============================================================================
-- widening_mul_u128 — Lean transcription of `wide_math.rs:1051-1071`
-- ============================================================================

/-- Lean mirror of `wide_math.rs::widening_mul_u128`.

    The Rust code uses `overflowing_add` and raw u128 `+` / `<<` / `>>` with
    Rust's wrapping semantics. We model each operation explicitly:
      - `lh.overflowing_add(hl)` → `mid = (lh + hl) % TWO_128`,
        `mid_carry = (lh + hl ≥ TWO_128)`
      - `ll + (mid << 64)` with overflow → `lo`, `lo_carry`
      - `mid << 64` in u128 = `(mid % TWO_64) * TWO_64` (high 64 bits
        of mid shift out of the u128)
      - `mid >> 64` = `mid / TWO_64`

    The function returns the pair `(lo, hi)` representing a 256-bit value
    `lo + hi · TWO_128`.

    Precondition for correctness: `a, b < TWO_128` (i.e. valid u128). -/
def wideningMulU128 (a b : Nat) : Nat × Nat :=
  let a_lo := u64Lo a
  let a_hi := u64Hi a
  let b_lo := u64Lo b
  let b_hi := u64Hi b

  -- Four 64×64 → 128 partial products. Each is at most (2^64 - 1)² < 2^128.
  let ll := a_lo * b_lo
  let lh := a_lo * b_hi
  let hl := a_hi * b_lo
  let hh := a_hi * b_hi

  -- mid = (lh + hl) mod 2^128; carry bit set if true sum exceeds 2^128.
  let mid := (lh + hl) % TWO_128
  let mid_carry := if lh + hl ≥ TWO_128 then 1 else 0

  -- lo = (ll + (mid mod 2^64) * 2^64) mod 2^128; lo_carry tracks overflow.
  let mid_shifted := (mid % TWO_64) * TWO_64
  let lo_unwrapped := ll + mid_shifted
  let lo := lo_unwrapped % TWO_128
  let lo_carry := if lo_unwrapped ≥ TWO_128 then 1 else 0

  -- hi = hh + (mid div 2^64) + (mid_carry · 2^64) + lo_carry.
  -- Under a, b < 2^128, this stays < 2^128 (proven by wideningMulU128_hi_bounded).
  let hi := hh + (mid / TWO_64) + mid_carry * TWO_64 + lo_carry

  (lo, hi)

-- ============================================================================
-- Theorems
-- ============================================================================

/- **wideningMulU128 correctness sketch** (the actual theorem appears below
   the helper-lemma section): the (lo, hi) decomposition equals the full
   unbounded product `a · b`. Foundational identity for percolator's 256-bit
   arithmetic — every transient product in `wide_math.rs` rests on this.

    Proof structure (drafted; sorry pending follow-up session):
      1. Decompose: `a = (a/TWO_64) · TWO_64 + (a mod TWO_64)` via
         `Nat.div_add_mod`. Same for b.
      2. Bound: under `a < TWO_128 = TWO_64²`, the high chunk
         `a / TWO_64 < TWO_64`, so `u64Hi a = (a / TWO_64) mod TWO_64
         = a / TWO_64` (mod is a no-op).
      3. **Carry identity for `mid`**: by definition,
         `mid = (lh + hl) mod TWO_128` and
         `mid_carry = (lh + hl ≥ TWO_128)`, so
         `mid + mid_carry · TWO_128 = lh + hl` always.
      4. **Shift identity for `mid`**: since `mid < TWO_128`,
         `mid = (mid / TWO_64) · TWO_64 + (mid mod TWO_64)`, so
         `(mid mod TWO_64) · TWO_64 + (mid / TWO_64) · TWO_128 = mid · TWO_64`.
      5. **Carry identity for `lo`**: similarly,
         `lo + lo_carry · TWO_128 = ll + mid_shifted` where
         `mid_shifted = (mid mod TWO_64) · TWO_64`.
      6. Assemble: substitute (3)–(5) into `lo + hi · TWO_128`. After
         expansion and using `TWO_64² = TWO_128`, both sides reduce to
         `ll + (lh + hl) · TWO_64 + hh · TWO_128`. `ring` closes.
      7. Show this equals `a · b` via (1) and (2): expand
         `(a_hi · TWO_64 + a_lo)(b_hi · TWO_64 + b_lo)`. Again `ring`.

    Mirrors the §3c manual walk in
    `~/code/audits/percolator-v16-2026-05/LEARNINGS.md` (T1.5 §3c), which
    informally verified this identity at the corner cases a=b=2^128-1,
    a=2^128-1+b=1, a=2^127+b=2.

    Draft proof (to be uncommented and iterated once Mathlib v4.15.0 has
    finished compiling — `lake build` is running in background):
    ```
    theorem wideningMulU128_correct (a b : Nat) (ha : isU128 a) (hb : isU128 b) :
        (wideningMulU128 a b).1 + (wideningMulU128 a b).2 * TWO_128 = a * b := by
      have h64 : (0 : Nat) < TWO_64 := by unfold TWO_64; norm_num
      have h128_eq : TWO_64 * TWO_64 = TWO_128 := by
        unfold TWO_64 TWO_128
        ring
      -- High chunks fit in u64
      have ha_hi_lt : a / TWO_64 < TWO_64 := by
        apply (Nat.div_lt_iff_lt_mul h64).mpr
        rw [h128_eq]; exact ha
      have hb_hi_lt : b / TWO_64 < TWO_64 := by
        apply (Nat.div_lt_iff_lt_mul h64).mpr
        rw [h128_eq]; exact hb
      -- a = (a/TWO_64) · TWO_64 + (a mod TWO_64)
      have ha_decomp : (a / TWO_64) * TWO_64 + a % TWO_64 = a :=
        Nat.div_add_mod a TWO_64
      have hb_decomp : (b / TWO_64) * TWO_64 + b % TWO_64 = b :=
        Nat.div_add_mod b TWO_64
      -- Unfold the function
      simp only [wideningMulU128, u64Lo, u64Hi]
      -- Rewrite (a/TWO_64) % TWO_64 = a/TWO_64 using ha_hi_lt; same for b
      rw [Nat.mod_eq_of_lt ha_hi_lt, Nat.mod_eq_of_lt hb_hi_lt]
      -- Now the goal is in terms of (a/TWO_64), (a % TWO_64), etc.
      -- The if-branches need case analysis on (lh + hl ≥ TWO_128)
      -- and (lo_unwrapped ≥ TWO_128). After splitting, each case
      -- reduces to a Nat ring identity that `ring` + Nat.div_add_mod close.
      sorry
    ```
-/
-- ============================================================================
-- Helper lemmas
-- ============================================================================

/-- For valid u128 inputs, the high chunk equals the integer division
    (the trailing `% TWO_64` in `u64Hi` is a no-op).

    This is the first cleanly-closed proof in the project, demonstrating
    that the Lake + Mathlib stack works end-to-end for percolator's
    arithmetic verification. -/
theorem u64Hi_eq_div (a : Nat) (ha : isU128 a) : u64Hi a = a / TWO_64 := by
  have h64 : (0 : Nat) < TWO_64 := by unfold TWO_64; norm_num
  have h128_eq : TWO_64 * TWO_64 = TWO_128 := by
    unfold TWO_64 TWO_128; ring
  have hlt : a / TWO_64 < TWO_64 := by
    rw [Nat.div_lt_iff_lt_mul h64, h128_eq]; exact ha
  unfold u64Hi
  exact Nat.mod_eq_of_lt hlt

theorem wideningMulU128_correct (a b : Nat) (ha : isU128 a) (hb : isU128 b) :
    (wideningMulU128 a b).1 + (wideningMulU128 a b).2 * TWO_128 = a * b := by
  -- Basic constants
  have h64 : (0 : Nat) < TWO_64 := by unfold TWO_64; norm_num
  have h128_eq : TWO_64 * TWO_64 = TWO_128 := by unfold TWO_64 TWO_128; ring
  have h128_pos : (0 : Nat) < TWO_128 := by unfold TWO_128; norm_num

  -- Chunk bounds
  have ha_hi_lt : a / TWO_64 < TWO_64 := by
    rw [Nat.div_lt_iff_lt_mul h64, h128_eq]; exact ha
  have hb_hi_lt : b / TWO_64 < TWO_64 := by
    rw [Nat.div_lt_iff_lt_mul h64, h128_eq]; exact hb
  have ha_lo_lt : a % TWO_64 < TWO_64 := Nat.mod_lt _ h64
  have hb_lo_lt : b % TWO_64 < TWO_64 := Nat.mod_lt _ h64
  have ha_hi_eq : (a / TWO_64) % TWO_64 = a / TWO_64 := Nat.mod_eq_of_lt ha_hi_lt
  have hb_hi_eq : (b / TWO_64) % TWO_64 = b / TWO_64 := Nat.mod_eq_of_lt hb_hi_lt

  -- u64 × u64 < TWO_128
  have chunk_mul_lt : ∀ {x y : Nat}, x < TWO_64 → y < TWO_64 → x * y < TWO_128 := by
    intros x y hx hy
    have h1 : x * y < TWO_64 * TWO_64 := by nlinarith
    linarith [h128_eq]

  -- Chunk decompositions
  have ha_decomp : a = a / TWO_64 * TWO_64 + a % TWO_64 := by
    have := Nat.div_add_mod a TWO_64; linarith
  have hb_decomp : b = b / TWO_64 * TWO_64 + b % TWO_64 := by
    have := Nat.div_add_mod b TWO_64; linarith

  -- Unfold function
  unfold wideningMulU128
  simp only [u64Lo, u64Hi, ha_hi_eq, hb_hi_eq]

  -- Names mirroring the let-bindings in wideningMulU128
  set a_lo := a % TWO_64
  set a_hi := a / TWO_64
  set b_lo := b % TWO_64
  set b_hi := b / TWO_64
  set ll := a_lo * b_lo with hll_def
  set lh := a_lo * b_hi with hlh_def
  set hl := a_hi * b_lo with hhl_def
  set hh := a_hi * b_hi with hhh_def

  have hll_lt : ll < TWO_128 := chunk_mul_lt ha_lo_lt hb_lo_lt
  have hlh_lt : lh < TWO_128 := chunk_mul_lt ha_lo_lt hb_hi_lt
  have hhl_lt : hl < TWO_128 := chunk_mul_lt ha_hi_lt hb_lo_lt

  set S_mid := lh + hl with hSmid_def
  set mid := S_mid % TWO_128 with hmid_def
  set mid_carry : Nat := if S_mid ≥ TWO_128 then 1 else 0 with hmidc_def

  have hSmid_lt : S_mid < 2 * TWO_128 := by omega

  -- mid + mid_carry * TWO_128 = S_mid
  have hmid_id : mid + mid_carry * TWO_128 = S_mid := by
    by_cases h : S_mid ≥ TWO_128
    · simp only [hmidc_def, if_pos h]
      have h_div_ge : 1 ≤ S_mid / TWO_128 :=
        (Nat.one_le_div_iff h128_pos).mpr h
      have h_div_lt : S_mid / TWO_128 < 2 :=
        (Nat.div_lt_iff_lt_mul h128_pos).mpr (by linarith [hSmid_lt])
      have hSd : S_mid / TWO_128 = 1 := by omega
      have hda := Nat.div_add_mod S_mid TWO_128
      rw [hSd] at hda
      simp only [hmid_def]; linarith
    · simp only [hmidc_def, if_neg h]
      have hlt : S_mid < TWO_128 := by linarith
      simp only [hmid_def, Nat.mod_eq_of_lt hlt]
      ring

  have hmid_lo_lt : mid % TWO_64 < TWO_64 := Nat.mod_lt _ h64

  set mid_shifted := (mid % TWO_64) * TWO_64 with hms_def
  have hmid_shifted_lt : mid_shifted < TWO_128 := by
    show (mid % TWO_64) * TWO_64 < TWO_128
    have : (mid % TWO_64) * TWO_64 < TWO_64 * TWO_64 := by nlinarith
    linarith [h128_eq]

  set lo_unwrapped := ll + mid_shifted with hlu_def
  have hlu_lt : lo_unwrapped < 2 * TWO_128 := by omega
  set lo := lo_unwrapped % TWO_128 with hlo_def
  set lo_carry : Nat := if lo_unwrapped ≥ TWO_128 then 1 else 0 with hloc_def

  -- lo + lo_carry * TWO_128 = lo_unwrapped
  have hlo_id : lo + lo_carry * TWO_128 = lo_unwrapped := by
    by_cases h : lo_unwrapped ≥ TWO_128
    · simp only [hloc_def, if_pos h]
      have h_div_ge : 1 ≤ lo_unwrapped / TWO_128 :=
        (Nat.one_le_div_iff h128_pos).mpr h
      have h_div_lt : lo_unwrapped / TWO_128 < 2 :=
        (Nat.div_lt_iff_lt_mul h128_pos).mpr (by linarith [hlu_lt])
      have hLd : lo_unwrapped / TWO_128 = 1 := by omega
      have hda := Nat.div_add_mod lo_unwrapped TWO_128
      rw [hLd] at hda
      simp only [hlo_def]; linarith
    · simp only [hloc_def, if_neg h]
      have hlt : lo_unwrapped < TWO_128 := by linarith
      simp only [hlo_def, Nat.mod_eq_of_lt hlt]
      ring

  -- Chunk decomposition for mid
  have hmid_chunk : TWO_64 * (mid / TWO_64) + mid % TWO_64 = mid :=
    Nat.div_add_mod mid TWO_64

  -- Introduce q = mid/TWO_64, r = mid%TWO_64 so the goal is pure ring algebra
  set q := mid / TWO_64
  set r := mid % TWO_64

  have hmid_qr : q * TWO_64 + r = mid := by
    have := hmid_chunk
    -- hmid_chunk : TWO_64 * (mid / TWO_64) + mid % TWO_64 = mid
    -- q = mid / TWO_64, r = mid % TWO_64
    linarith

  -- Restate hmid_id without `mid` / `S_mid`
  have hmid_id' : q * TWO_64 + r + mid_carry * TWO_128 = lh + hl := by
    have h1 : mid + mid_carry * TWO_128 = S_mid := hmid_id
    have h2 : S_mid = lh + hl := rfl
    omega

  have hlo_id' : lo + lo_carry * TWO_128 = ll + r * TWO_64 := by
    have h1 : lo + lo_carry * TWO_128 = lo_unwrapped := hlo_id
    have h2 : lo_unwrapped = ll + mid_shifted := rfl
    have h3 : mid_shifted = r * TWO_64 := rfl
    omega

  -- The hi value
  -- After simp, the goal has `hh + (mid / TWO_64) + mid_carry * TWO_64 + lo_carry`
  -- For Lean's `show`, name it explicitly:
  show lo + (hh + q + mid_carry * TWO_64 + lo_carry) * TWO_128 = a * b

  -- Step A: LHS reduces to `ll + (lh + hl) * TWO_64 + hh * TWO_128`
  -- The key auxiliary identity, derived by multiplying hmid_id' by TWO_64:
  have key_aux : q * TWO_128 + r * TWO_64 + mid_carry * TWO_64 * TWO_128
               = (lh + hl) * TWO_64 := by
    have hmul : (q * TWO_64 + r + mid_carry * TWO_128) * TWO_64 = (lh + hl) * TWO_64 := by
      rw [hmid_id']
    -- Expand LHS of hmul and substitute h128_eq
    have hexp : (q * TWO_64 + r + mid_carry * TWO_128) * TWO_64
              = q * (TWO_64 * TWO_64) + r * TWO_64 + mid_carry * TWO_64 * TWO_128 := by ring
    rw [hexp, h128_eq] at hmul
    linarith [hmul]

  have lhs_step : lo + (hh + q + mid_carry * TWO_64 + lo_carry) * TWO_128
                = ll + (lh + hl) * TWO_64 + hh * TWO_128 := by
    -- All-explicit rewrite chain to avoid linarith heartbeat overload
    have e1 : lo + (hh + q + mid_carry * TWO_64 + lo_carry) * TWO_128
            = (lo + lo_carry * TWO_128)
              + (q * TWO_128 + mid_carry * TWO_64 * TWO_128)
              + hh * TWO_128 := by ring
    rw [e1, hlo_id']
    -- Goal: (ll + r * TWO_64) + (q * TWO_128 + mid_carry * TWO_64 * TWO_128) + hh * TWO_128
    --     = ll + (lh + hl) * TWO_64 + hh * TWO_128
    have e2 : (ll + r * TWO_64) + (q * TWO_128 + mid_carry * TWO_64 * TWO_128) + hh * TWO_128
            = ll + (q * TWO_128 + r * TWO_64 + mid_carry * TWO_64 * TWO_128) + hh * TWO_128 := by ring
    rw [e2, key_aux]

  rw [lhs_step]

  -- Step B: RHS expands to the same
  -- a * b = (a_hi * TWO_64 + a_lo) * (b_hi * TWO_64 + b_lo)
  --       = a_hi*b_hi*TWO_128 + (a_hi*b_lo + a_lo*b_hi)*TWO_64 + a_lo*b_lo
  --       = hh*TWO_128 + (hl + lh)*TWO_64 + ll
  conv_rhs => rw [show a = a_hi * TWO_64 + a_lo from ha_decomp,
                  show b = b_hi * TWO_64 + b_lo from hb_decomp]
  show ll + (lh + hl) * TWO_64 + hh * TWO_128
     = (a_hi * TWO_64 + a_lo) * (b_hi * TWO_64 + b_lo)
  rw [hll_def, hlh_def, hhl_def, hhh_def, ← h128_eq]
  ring

/-- **hi limb bound**: under valid u128 inputs, the hi limb of the widening
    multiplication fits in a u128. Closes the implicit precondition that
    `U256::checked_mul` (`wide_math.rs:309-340`) relies on when it stores
    the result in `U256::new(prod_lo, prod_hi)`.

    Tight bound: `hi ≤ TWO_128 - 2` (achieved at a = b = 2^128 - 1, where
    a · b = 2^256 - 2^129 + 1 ⇒ hi = 2^128 - 2). -/
theorem wideningMulU128_hi_bounded (a b : Nat) (ha : isU128 a) (hb : isU128 b) :
    (wideningMulU128 a b).2 < TWO_128 := by
  have h128_pos : (0 : Nat) < TWO_128 := by unfold TWO_128; norm_num
  have hcorrect := wideningMulU128_correct a b ha hb
  -- lo + hi * TWO_128 = a * b, with a, b < TWO_128, so a * b < TWO_128²
  have hab_lt : a * b < TWO_128 * TWO_128 := by
    by_cases hb_zero : b = 0
    · rw [hb_zero, Nat.mul_zero]; exact Nat.mul_pos h128_pos h128_pos
    · have hbp : 0 < b := Nat.pos_of_ne_zero hb_zero
      have h1 : a * b < TWO_128 * b := (Nat.mul_lt_mul_right hbp).mpr ha
      have h2 : TWO_128 * b ≤ TWO_128 * TWO_128 :=
        Nat.mul_le_mul_left TWO_128 (Nat.le_of_lt hb)
      linarith
  -- hi * TWO_128 ≤ a * b
  have hhi_mul : (wideningMulU128 a b).2 * TWO_128 ≤ a * b := by
    have h1 := hcorrect
    omega
  -- Combine: hi * TWO_128 < TWO_128 * TWO_128
  have : (wideningMulU128 a b).2 * TWO_128 < TWO_128 * TWO_128 := by linarith
  -- Divide by TWO_128 (positive) to conclude hi < TWO_128
  exact Nat.lt_of_mul_lt_mul_right this

/-- **Trivial bound on lo limb**: the low limb of widening multiplication
    always fits in u128 (it's a `% TWO_128` of an unbounded sum). -/
theorem wideningMulU128_lo_lt (a b : Nat) : (wideningMulU128 a b).1 < TWO_128 := by
  unfold wideningMulU128
  exact Nat.mod_lt _ (by unfold TWO_128; norm_num)

/-- **Fits-in-u128 corollary**: when `a · b` is small enough to fit in a
    single u128, the widening multiplication's hi limb is exactly zero and
    the lo limb equals the product. Useful downstream for proving
    `U256::checked_mul` correctness when one of the inputs has hi=0
    (and similarly for `mul_div_floor_u256` when intermediate products
    don't push past u128).

    Corollary of `wideningMulU128_correct`. -/
theorem wideningMulU128_fits_u128 (a b : Nat) (ha : isU128 a) (hb : isU128 b)
    (hab : a * b < TWO_128) :
    wideningMulU128 a b = (a * b, 0) := by
  have h128_pos : (0 : Nat) < TWO_128 := by unfold TWO_128; norm_num
  have hcorrect := wideningMulU128_correct a b ha hb
  -- From hcorrect: lo + hi * TWO_128 = a * b < TWO_128.
  -- If hi > 0, then hi * TWO_128 ≥ TWO_128, so lo + hi * TWO_128 ≥ TWO_128.
  -- Contradiction ⇒ hi = 0.
  have hi_zero : (wideningMulU128 a b).2 = 0 := by
    by_contra hne
    have hi_pos : 0 < (wideningMulU128 a b).2 := Nat.pos_of_ne_zero hne
    have hmul_ge : TWO_128 ≤ (wideningMulU128 a b).2 * TWO_128 := by
      calc TWO_128 = 1 * TWO_128 := (one_mul _).symm
        _ ≤ (wideningMulU128 a b).2 * TWO_128 :=
            Nat.mul_le_mul_right TWO_128 hi_pos
    -- lo + hi*TWO_128 = a*b < TWO_128, but hi*TWO_128 ≥ TWO_128. Contradiction.
    have := hcorrect
    omega
  -- Now hi = 0 ⇒ lo = a * b
  have lo_eq : (wideningMulU128 a b).1 = a * b := by
    have h1 := hcorrect
    rw [hi_zero] at h1
    linarith
  -- Combine into the pair equality
  apply Prod.ext
  · exact lo_eq
  · exact hi_zero

end Percolator.Spec
