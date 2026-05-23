/-
  Percolator.LienLifecycle — Phase 5 cluster 1: lien lifecycle.

  Pure Lean transition relations and conservation theorems for the
  per-source lien lifecycle: Create, Consume, Release, Impair.

  Builds directly on the Phase 2 `Lien` and `SourceCreditLienAggregate`
  types in `Percolator/Lien.lean`. Every transition is typed by
  `BackingSource`, so the §14 #23 invariant (no dual classification)
  remains structural across the lifecycle — the source parameter is
  baked into every step.

  §14 invariants addressed in this file:
    - #32 `lien_creation_increments_correct_aggregate_for_backing_source`
    - #37 `lien_consumption_decrements_bucket_valid_liened_and_source_valid_liened_once`
    - #39 `lien_release_moves_valid_liened_to_fresh_unliened_without_changing_fresh_reserved`
    - #21 `impaired_insurance_lien_remains_reserved_and_unavailable_until_reconciled`
    - #31 `insurance_impaired_lien_remains_encumbered_until_release_or_consume`
    - #19/#30 `insurance_backed_lien_*_conserves_canonical_ledger` (the
      consumption-side conservation; the creation side is by typing).
-/

import Percolator.Lien
import Percolator.Lifecycle
import Percolator.BackingBucket
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Percolator.Spec

namespace Lien

-- ============================================================================
-- Lifecycle transition functions
-- ============================================================================

/-- **Create**: add `face` face-claim and `backing` backing-reserved to a
    lien on a given source. The source is type-fixed, so creating on the
    counterparty side cannot accidentally update the insurance lien
    (and vice versa) — that's §14 #32 by typing.

    Preconditions are unconstrained at the per-lien level — the lien
    aggregate may carry arbitrary amounts. Higher-level transitions
    (where backing actually has to come from somewhere) impose extra
    constraints. -/
def create (l : Lien src) (face backing effective : Nat) : Lien src where
  faceClaimLockedNum              := l.faceClaimLockedNum + face
  backingReservedNum              := l.backingReservedNum + backing
  effectiveCreditReserved         := l.effectiveCreditReserved + effective
  impairedFaceClaimNum            := l.impairedFaceClaimNum
  impairedEffectiveCreditReserved := l.impairedEffectiveCreditReserved

/-- **Consume**: subtract `face` face-claim and `backing` backing-reserved
    from a lien — the backing is *spent* (gone from the system).

    Returns `none` if there isn't enough face or backing to consume.
    On success, exactly one bucket-side amount and one source-side amount
    decrease (this is what §14 #37 asserts).

    `effective` is the effective-credit decrement proportional to the
    face/backing consumption; provided as a parameter so the caller (the
    arithmetic-aware engine) can supply the rounded value. -/
def consume (l : Lien src) (face backing effective : Nat) : Option (Lien src) :=
  if l.faceClaimLockedNum < face then none
  else if l.backingReservedNum < backing then none
  else if l.effectiveCreditReserved < effective then none
  else some {
    faceClaimLockedNum              := l.faceClaimLockedNum - face
    backingReservedNum              := l.backingReservedNum - backing
    effectiveCreditReserved         := l.effectiveCreditReserved - effective
    impairedFaceClaimNum            := l.impairedFaceClaimNum
    impairedEffectiveCreditReserved := l.impairedEffectiveCreditReserved
  }

/-- **Release**: same shape as `consume`, but the backing is returned
    to the fresh pool rather than spent. From the per-lien perspective
    the field updates are identical; the difference is in *what happens
    to the backing on the other side* of the ledger — modeled at the
    aggregate level (see `SourceCreditLienAggregate.releaseAccounting`). -/
def release (l : Lien src) (face backing effective : Nat) : Option (Lien src) :=
  consume l face backing effective

/-- **Impair**: move `face` face-claim and `effective` effective-credit
    from the valid bucket to the impaired bucket. `backingReservedNum`
    is NOT changed — the lien is still encumbered, just now bad. -/
def impair (l : Lien src) (face effective : Nat) : Option (Lien src) :=
  if l.faceClaimLockedNum < face then none
  else if l.effectiveCreditReserved < effective then none
  else some {
    faceClaimLockedNum              := l.faceClaimLockedNum - face
    backingReservedNum              := l.backingReservedNum
    effectiveCreditReserved         := l.effectiveCreditReserved - effective
    impairedFaceClaimNum            := l.impairedFaceClaimNum + face
    impairedEffectiveCreditReserved := l.impairedEffectiveCreditReserved + effective
  }

-- ============================================================================
-- §14 #32: lien creation increments correct aggregate
-- ============================================================================

/-- **§14 #32 (per-side)**: `create` strictly adds to the named source's
    fields, never to the other source's fields.

    Statement: for any aggregate `a` and source `src`, applying `create`
    to the `src` lien leaves the *other* lien fields unchanged.

    The version below is the type-level witness — there is no expression
    that updates the wrong source. The aggregate-level lemma is just a
    rewriting witness for downstream proofs. -/
theorem create_targets_named_source_only
    (a : SourceCreditLienAggregate) (face backing effective : Nat) :
    let a' : SourceCreditLienAggregate :=
      { a with counterparty := a.counterparty.create face backing effective }
    a'.insurance = a.insurance := by
  rfl

/-- Symmetric statement for insurance-side creation. -/
theorem create_insurance_leaves_counterparty
    (a : SourceCreditLienAggregate) (face backing effective : Nat) :
    let a' : SourceCreditLienAggregate :=
      { a with insurance := a.insurance.create face backing effective }
    a'.counterparty = a.counterparty := by
  rfl

/-- **§14 #32 (arithmetic)**: `create` increments `faceClaimLockedNum`
    by exactly `face`. -/
theorem create_faceClaim_increments
    (l : Lien src) (face backing effective : Nat) :
    (l.create face backing effective).faceClaimLockedNum
    = l.faceClaimLockedNum + face := rfl

/-- **§14 #32 (arithmetic)**: `create` increments `backingReservedNum`
    by exactly `backing`. -/
theorem create_backing_increments
    (l : Lien src) (face backing effective : Nat) :
    (l.create face backing effective).backingReservedNum
    = l.backingReservedNum + backing := rfl

-- ============================================================================
-- §14 #37: consumption decrements once per side
-- ============================================================================

/-- **§14 #37 (face)**: `consume` decrements `faceClaimLockedNum` by
    exactly `face` (when it succeeds — i.e. the precondition holds). -/
theorem consume_faceClaim_decrements
    (l : Lien src) (face backing effective : Nat) (l' : Lien src)
    (h : l.consume face backing effective = some l') :
    l'.faceClaimLockedNum + face = l.faceClaimLockedNum := by
  unfold consume at h
  by_cases h1 : l.faceClaimLockedNum < face
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : l.backingReservedNum < backing
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : l.effectiveCreditReserved < effective
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  have hl' := Option.some.inj h
  subst hl'
  show l.faceClaimLockedNum - face + face = l.faceClaimLockedNum
  omega

/-- **§14 #37 (backing)**: `consume` decrements `backingReservedNum`
    by exactly `backing`. -/
theorem consume_backing_decrements
    (l : Lien src) (face backing effective : Nat) (l' : Lien src)
    (h : l.consume face backing effective = some l') :
    l'.backingReservedNum + backing = l.backingReservedNum := by
  unfold consume at h
  by_cases h1 : l.faceClaimLockedNum < face
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : l.backingReservedNum < backing
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : l.effectiveCreditReserved < effective
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  have hl' := Option.some.inj h
  subst hl'
  show l.backingReservedNum - backing + backing = l.backingReservedNum
  omega

/-- **§14 #37 (other source untouched)**: consuming on the counterparty
    side leaves the insurance fields unchanged. -/
theorem consume_counterparty_leaves_insurance
    (a : SourceCreditLienAggregate) (face backing effective : Nat) (cp' : Lien .Counterparty)
    (h : a.counterparty.consume face backing effective = some cp') :
    ({ a with counterparty := cp' } : SourceCreditLienAggregate).insurance
    = a.insurance := by
  rfl

-- ============================================================================
-- §14 #39: release moves to fresh without changing total reserves
-- ============================================================================

/-- **§14 #39 (per-lien)**: at the per-lien level, `release` is the same
    operation as `consume` — the difference is what the aggregate does
    with the released backing (returned vs spent). The conservation
    statement below witnesses the per-lien field-level equivalence; the
    aggregate-level "back to fresh" booking lives in
    `SourceCreditLienAggregate.releaseAccounting`. -/
theorem release_eq_consume
    (l : Lien src) (face backing effective : Nat) :
    l.release face backing effective = l.consume face backing effective := rfl

/-- **§14 #39 (impaired untouched)**: `release` does not move face into
    the impaired bucket; the impaired-amount fields are unchanged. -/
theorem release_does_not_impair
    (l : Lien src) (face backing effective : Nat) (l' : Lien src)
    (h : l.release face backing effective = some l') :
    l'.impairedFaceClaimNum = l.impairedFaceClaimNum := by
  unfold release consume at h
  by_cases h1 : l.faceClaimLockedNum < face
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : l.backingReservedNum < backing
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : l.effectiveCreditReserved < effective
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  have hl' := Option.some.inj h
  subst hl'
  rfl

-- ============================================================================
-- §14 #19/#30: lifecycle conservation
-- ============================================================================

/-- **Total face**: total face claim either currently locked or impaired.
    The conservation theorems below assert this quantity is preserved
    by `impair` (moves between the two buckets) and reduced by `consume`
    or `release` (face leaves the lien). -/
def totalFace (l : Lien src) : Nat :=
  l.faceClaimLockedNum + l.impairedFaceClaimNum

/-- **§14 #19/#30 (impair conserves total face)**: impair moves face
    between the valid and impaired buckets without losing or creating
    any. Encodes "impair conserves the canonical ledger." -/
theorem impair_conserves_totalFace
    (l : Lien src) (face effective : Nat) (l' : Lien src)
    (h : l.impair face effective = some l') :
    l'.totalFace = l.totalFace := by
  unfold impair at h
  by_cases h1 : l.faceClaimLockedNum < face
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : l.effectiveCreditReserved < effective
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  have hl' := Option.some.inj h
  subst hl'
  unfold totalFace
  show (l.faceClaimLockedNum - face) + (l.impairedFaceClaimNum + face)
     = l.faceClaimLockedNum + l.impairedFaceClaimNum
  omega

/-- **§14 #19/#30 (consume reduces total face by face)**: consumption
    removes `face` from the lien — the total face decreases by exactly
    that amount. -/
theorem consume_totalFace_decrement
    (l : Lien src) (face backing effective : Nat) (l' : Lien src)
    (h : l.consume face backing effective = some l') :
    l'.totalFace + face = l.totalFace := by
  have hf := consume_faceClaim_decrements l face backing effective l' h
  -- Impaired bucket is untouched by consume; show this.
  have himp : l'.impairedFaceClaimNum = l.impairedFaceClaimNum := by
    unfold consume at h
    by_cases h1 : l.faceClaimLockedNum < face
    · rw [if_pos h1] at h; cases h
    rw [if_neg h1] at h
    by_cases h2 : l.backingReservedNum < backing
    · rw [if_pos h2] at h; cases h
    rw [if_neg h2] at h
    by_cases h3 : l.effectiveCreditReserved < effective
    · rw [if_pos h3] at h; cases h
    rw [if_neg h3] at h
    have hl' := Option.some.inj h
    subst hl'
    rfl
  unfold totalFace
  omega

-- ============================================================================
-- §14 #21/#31: impaired stays encumbered until reconciled
-- ============================================================================

/-- After `impair`, the impaired-face bucket strictly grows (unless face=0). -/
theorem impair_grows_impaired
    (l : Lien src) (face effective : Nat) (l' : Lien src)
    (h : l.impair face effective = some l') :
    l'.impairedFaceClaimNum = l.impairedFaceClaimNum + face := by
  unfold impair at h
  by_cases h1 : l.faceClaimLockedNum < face
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : l.effectiveCreditReserved < effective
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  have hl' := Option.some.inj h
  subst hl'
  rfl

/-- After `impair`, the `backingReservedNum` is *unchanged* — the
    impaired lien is still encumbered against the backing pool.
    Encodes the §14 #21 / #31 "remains reserved" half. -/
theorem impair_preserves_backing
    (l : Lien src) (face effective : Nat) (l' : Lien src)
    (h : l.impair face effective = some l') :
    l'.backingReservedNum = l.backingReservedNum := by
  unfold impair at h
  by_cases h1 : l.faceClaimLockedNum < face
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : l.effectiveCreditReserved < effective
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  have hl' := Option.some.inj h
  subst hl'
  rfl

end Lien

-- ============================================================================
-- §14 #38: joint fresh_reserved + claim_bound drop on lien consumption
-- ============================================================================

/-- **§14 #38 (joint statement)**: a lien consumption that targets
    both the bucket-level `validLiened` partition and the lien-level
    `faceClaimLockedNum` simultaneously decrements both by exactly
    the consumed amount.

    The prior closure proved only the bucket side
    (`consumeLien_removes_from_validLiened`). This strengthens by
    pairing it with the lien-side decrement
    (`Lien.consume_faceClaim_decrements` from cluster 1). -/
theorem lien_consumption_removes_fresh_reserved_and_claim_bound
    {src : BackingSource}
    (b b' : BackingBucket) (l l' : Lien src)
    (amount face : Nat) (effective : Nat)
    (hbucket : b.consumeLien amount = some b')
    (hlien   : l.consume face amount effective = some l') :
    b'.validLiened + amount = b.validLiened
    ∧ l'.faceClaimLockedNum + face = l.faceClaimLockedNum
    ∧ l'.backingReservedNum + amount = l.backingReservedNum := by
  refine ⟨?_, ?_, ?_⟩
  · exact (BackingBucket.consumeLien_removes_from_validLiened
            b b' amount hbucket).1
  · exact Lien.consume_faceClaim_decrements l face amount effective l' hlien
  · exact Lien.consume_backing_decrements l face amount effective l' hlien

/-- **§14 #38 (combined fresh-reserved sum drop)**: the bucket's
    `freshUnliened + validLiened` (the spec's "fresh_reserved_backing_num"
    for that bucket) decreases by `amount` when a consume fires —
    `freshUnliened` is untouched and `validLiened` drops by `amount`. -/
theorem BackingBucket.consumeLien_decreases_fresh_reserved_total
    (b b' : BackingBucket) (amount : Nat)
    (h : b.consumeLien amount = some b') :
    b'.freshUnliened + b'.validLiened + amount
    = b.freshUnliened + b.validLiened := by
  unfold consumeLien at h
  by_cases hlt : b.validLiened < amount
  · simp [hlt] at h
  · push_neg at hlt
    simp [hlt] at h
    have hb' := h.symm
    rw [hb']
    change b.freshUnliened + (b.validLiened - amount) + amount
         = b.freshUnliened + b.validLiened
    omega

end Percolator.Spec
