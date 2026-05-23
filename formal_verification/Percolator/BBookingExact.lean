/-
  Percolator.BBookingExact — Phase 5 cluster 6 (part 1):
  B residual booking exact-remainder conservation.

  Mirrors the B-booking arithmetic in `spec.md:1200-1212`:

      delta_B       = floor((engine_chunk * SOCIAL_LOSS_DEN + R) / W)
      new_remainder = (engine_chunk * SOCIAL_LOSS_DEN + R) % W

  The exact conservation invariant is the schoolbook
  `num = (num / W) * W + (num % W)` — Lean has this via
  `Nat.div_add_mod`. We expose it as a named theorem at the spec
  level so downstream invariants can cite it.

  §14 invariants addressed:
    - #75 `B_booking_exact_remainder_conservation`
-/

import Percolator.Defs
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

/-- One step of B residual booking.

    Takes the chosen `engineChunk` of residual atoms, the current
    cross-side social-loss remainder `R`, and the loss-weight sum
    `W` (the side denominator).

    Returns `(deltaB, newRemainder)` per `spec.md:1209-1211`:
      `delta_B = floor((engine_chunk * SOCIAL_LOSS_DEN + R) / W)`
      `new_remainder = (engine_chunk * SOCIAL_LOSS_DEN + R) % W`. -/
def bBookingStep (engineChunk R W : Nat) : Nat × Nat :=
  let num := engineChunk * SOCIAL_LOSS_DEN + R
  (num / W, num % W)

/-- **§14 #75 (exact remainder conservation)**: the booking step
    preserves the exact loss atoms across the chunk.

    Concretely: `delta_B * W + new_remainder = engine_chunk * SOCIAL_LOSS_DEN + R`.
    No loss is silently created or destroyed; everything goes either
    into `delta_B` (the booked floor) or `new_remainder` (carried into
    the next step). -/
theorem bBookingStep_exact_conservation
    (engineChunk R W : Nat) (hW : 0 < W) :
    let (deltaB, newR) := bBookingStep engineChunk R W
    deltaB * W + newR = engineChunk * SOCIAL_LOSS_DEN + R := by
  unfold bBookingStep
  simp
  have := Nat.div_add_mod (engineChunk * SOCIAL_LOSS_DEN + R) W
  linarith

/-- **§14 #75 (remainder bound)**: the carried remainder is strictly
    less than the side denominator `W`. Matches the spec's invariant
    `social_loss_remainder_side_num < SOCIAL_LOSS_DEN` (when `W = SOCIAL_LOSS_DEN`)
    and more generally that the new remainder is `< W`.

    A direct consequence of `Nat.mod_lt`. -/
theorem bBookingStep_remainder_lt_W
    (engineChunk R W : Nat) (hW : 0 < W) :
    (bBookingStep engineChunk R W).2 < W := by
  unfold bBookingStep
  exact Nat.mod_lt _ hW

/-- **§14 #75 (delta_B explicit form)**: the booked floor is the
    division of the scaled chunk-plus-remainder by `W`. -/
theorem bBookingStep_delta_eq
    (engineChunk R W : Nat) :
    (bBookingStep engineChunk R W).1
    = (engineChunk * SOCIAL_LOSS_DEN + R) / W := by
  unfold bBookingStep; rfl

/-- **§14 #75 (new_remainder explicit form)**. -/
theorem bBookingStep_remainder_eq
    (engineChunk R W : Nat) :
    (bBookingStep engineChunk R W).2
    = (engineChunk * SOCIAL_LOSS_DEN + R) % W := by
  unfold bBookingStep; rfl

/-- **§14 #75 (monotone in chunk)**: a larger `engineChunk` produces a
    `delta_B` that is at least as large. -/
theorem bBookingStep_delta_mono_in_chunk
    (engineChunk engineChunk' R W : Nat) (h : engineChunk ≤ engineChunk') :
    (bBookingStep engineChunk R W).1 ≤ (bBookingStep engineChunk' R W).1 := by
  unfold bBookingStep
  simp
  apply Nat.div_le_div_right
  have : engineChunk * SOCIAL_LOSS_DEN ≤ engineChunk' * SOCIAL_LOSS_DEN :=
    Nat.mul_le_mul_right _ h
  omega

/-- **§14 #75 (zero-chunk degenerate)**: a zero-chunk step carries the
    remainder forward unchanged and books zero. -/
theorem bBookingStep_zero_chunk (R W : Nat) (hR : R < W) :
    bBookingStep 0 R W = (0, R) := by
  unfold bBookingStep
  have hdiv : (0 * SOCIAL_LOSS_DEN + R) / W = 0 := by
    rw [Nat.zero_mul, Nat.zero_add]; exact Nat.div_eq_of_lt hR
  have hmod : (0 * SOCIAL_LOSS_DEN + R) % W = R := by
    rw [Nat.zero_mul, Nat.zero_add]; exact Nat.mod_eq_of_lt hR
  show ((0 * SOCIAL_LOSS_DEN + R) / W, (0 * SOCIAL_LOSS_DEN + R) % W) = (0, R)
  rw [hdiv, hmod]

-- ============================================================================
-- Repeated booking — the conservation extends across chunks via simple
-- recursion on a list of chunks (rather than foldl, which makes the
-- accumulator induction awkward).
-- ============================================================================

/-- Repeated B-booking, defined by structural recursion. Starting from
    remainder `R0`, apply each `engineChunk` in order, accumulating
    `delta_B` and carrying the remainder. Returns `(totalDeltaB, finalRemainder)`. -/
def bBookingRec (chunks : List Nat) (R0 W : Nat) : Nat × Nat :=
  match chunks with
  | [] => (0, R0)
  | c :: rest =>
    let (delta, R') := bBookingStep c R0 W
    let (deltaRest, finalR) := bBookingRec rest R' W
    (delta + deltaRest, finalR)

/-- Total chunk atoms in a list, scaled by `SOCIAL_LOSS_DEN`. -/
def totalScaledChunks (chunks : List Nat) : Nat :=
  (chunks.map (· * SOCIAL_LOSS_DEN)).sum

/-- **§14 #75 (multi-chunk conservation)**: the total booked plus the
    final remainder equals the initial remainder plus the sum of
    scaled chunks. No atom is lost across an arbitrary chunk sequence. -/
theorem bBookingRec_conservation
    (chunks : List Nat) (R0 W : Nat) (hW : 0 < W) :
    let (totalDelta, finalR) := bBookingRec chunks R0 W
    totalDelta * W + finalR = R0 + totalScaledChunks chunks := by
  induction chunks generalizing R0 with
  | nil =>
    unfold bBookingRec totalScaledChunks
    simp
  | cons c rest ih =>
    unfold bBookingRec totalScaledChunks
    simp [List.map_cons, List.sum_cons]
    -- After the head step: (delta_c, R_c) with delta_c * W + R_c = c*S + R0
    have hstep := bBookingStep_exact_conservation c R0 W hW
    set delta_c := (bBookingStep c R0 W).1
    set R_c     := (bBookingStep c R0 W).2
    -- Apply ih at the new starting remainder R_c
    have ih' := ih R_c
    set rest_delta := (bBookingRec rest R_c W).1
    set rest_R     := (bBookingRec rest R_c W).2
    show (delta_c + rest_delta) * W + rest_R = R0 + (c * SOCIAL_LOSS_DEN + _)
    -- Algebra: combine hstep and ih'
    have h1 : delta_c * W + R_c = c * SOCIAL_LOSS_DEN + R0 := hstep
    have h2 : rest_delta * W + rest_R = R_c + (rest.map (· * SOCIAL_LOSS_DEN)).sum := ih'
    -- (delta_c + rest_delta) * W + rest_R
    --   = delta_c * W + rest_delta * W + rest_R
    --   = delta_c * W + (R_c + sum_rest)             [by h2]
    --   = (delta_c * W + R_c) + sum_rest
    --   = (c * S + R0) + sum_rest                    [by h1]
    --   = R0 + (c * S + sum_rest)
    have hdist : (delta_c + rest_delta) * W
         = delta_c * W + rest_delta * W := Nat.add_mul _ _ _
    omega

end Percolator.Spec
