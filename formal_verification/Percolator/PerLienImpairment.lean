/-
  Percolator.PerLienImpairment — per-lien view of bucket expiry.

  Strengthens the §14 #41 closure in `LiveBacking.lean`. The original
  `BackingBucket.expireAndImpairAll` operates on the aggregate
  `validLiened` / `impairedLiened` Nat fields and proves the
  bucket-level conservation. The audit noted that "per-lien status
  updates not modeled" — the engine actually visits each lien in
  the bucket and flips its status, not just the aggregate.

  This file adds the missing per-lien layer:

    - `BucketLien` is a single lien with `id`, `amount`, and a
      `status : Validity` tag.
    - `expireLiens` is the per-lien transition: every Valid lien
      becomes Impaired; Impaired liens are left alone.
    - `expireLiens_all_impaired` is the per-lien witness — after
      the transition, no Valid lien remains.
    - `expireLiens_valid_sum_zero` and `expireLiens_impaired_sum_eq`
      bridge the per-lien transition to the aggregate counts that
      `LiveBacking.expireAndImpairAll` operates on. The per-lien
      Valid sum drops to 0; the Impaired sum gains exactly the
      prior Valid sum.

  §14 invariants strengthened in this file:
    - #41 `expired_liened_bucket_marks_liens_impaired_in_bounded_work`
          (audit: bucket-aggregate impairment correct; per-lien
           status updates not modeled. This file adds the
           per-lien layer.)
-/

import Percolator.LiveBacking
import Percolator.Lien
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #41 (strengthened): per-lien BucketLien with explicit status flip
-- ============================================================================

/-- A single lien within a backing bucket, with its own validity
    status. The engine tracks one of these per active lien;
    impairment flips the `status` field. -/
structure BucketLien where
  id     : Nat
  amount : Nat
  status : Validity
  deriving Repr, DecidableEq

namespace BucketLien

/-- Mark this lien Impaired (idempotent if already Impaired). -/
def impair (l : BucketLien) : BucketLien :=
  { l with status := .Impaired }

/-- Predicate: this lien is currently in Valid status. -/
def isValid (l : BucketLien) : Bool :=
  match l.status with
  | .Valid    => true
  | .Impaired => false

/-- Predicate: this lien is currently in Impaired status. -/
def isImpaired (l : BucketLien) : Bool :=
  match l.status with
  | .Valid    => false
  | .Impaired => true

theorem impair_status (l : BucketLien) : l.impair.status = .Impaired := rfl

theorem impair_preserves_amount (l : BucketLien) : l.impair.amount = l.amount := rfl

theorem impair_preserves_id (l : BucketLien) : l.impair.id = l.id := rfl

theorem impair_isImpaired (l : BucketLien) : l.impair.isImpaired = true := by
  unfold isImpaired impair; simp

theorem impair_not_isValid (l : BucketLien) : l.impair.isValid = false := by
  unfold isValid impair; simp

end BucketLien

/-- The per-lien expire transition over a list of liens. Every Valid
    lien becomes Impaired; Impaired liens pass through unchanged. -/
def expireLiens (liens : List BucketLien) : List BucketLien :=
  liens.map (fun l => if l.isValid then l.impair else l)

-- ============================================================================
-- Per-lien aggregate sums (bridge to LiveBacking aggregate fields)
-- ============================================================================

/-- Sum of amounts of Valid liens in the list — the per-lien analog of
    `BackingBucket.validLiened`. -/
def validSum (liens : List BucketLien) : Nat :=
  (liens.filter (·.isValid)).map (·.amount) |>.sum

/-- Sum of amounts of Impaired liens in the list — the per-lien
    analog of `BackingBucket.impairedLiened`. -/
def impairedSum (liens : List BucketLien) : Nat :=
  (liens.filter (·.isImpaired)).map (·.amount) |>.sum

/-- Sum of amounts of *all* liens — the conservation quantity. -/
def totalAmount (liens : List BucketLien) : Nat :=
  (liens.map (·.amount)).sum

/-- **Per-lien conservation**: a lien is either Valid or Impaired
    (closed-world from `Validity`), so summing both buckets gives the
    full total. -/
theorem validSum_plus_impairedSum_eq_total (liens : List BucketLien) :
    validSum liens + impairedSum liens = totalAmount liens := by
  induction liens with
  | nil => rfl
  | cons l rest ih =>
    unfold validSum impairedSum totalAmount at ih ⊢
    cases hs : l.status with
    | Valid =>
      have hv : l.isValid = true := by unfold BucketLien.isValid; rw [hs]
      have hi : l.isImpaired = false := by unfold BucketLien.isImpaired; rw [hs]
      simp [List.filter_cons, hv, hi, List.map_cons, List.sum_cons]
      omega
    | Impaired =>
      have hv : l.isValid = false := by unfold BucketLien.isValid; rw [hs]
      have hi : l.isImpaired = true := by unfold BucketLien.isImpaired; rw [hs]
      simp [List.filter_cons, hv, hi, List.map_cons, List.sum_cons]
      omega

-- ============================================================================
-- §14 #41 (strengthened): per-lien witness — no Valid lien survives
-- ============================================================================

/-- **§14 #41 (per-lien witness)**: after `expireLiens`, every lien in
    the result list is in Impaired status. The bucket-aggregate
    transition in `LiveBacking` only proves `validLiened = 0` post-
    state; this proves the same fact at the per-lien resolution
    the engine actually operates at. -/
theorem expireLiens_all_impaired (liens : List BucketLien) :
    ∀ l ∈ expireLiens liens, l.status = .Impaired := by
  intro l hl
  unfold expireLiens at hl
  rw [List.mem_map] at hl
  obtain ⟨orig, _, heq⟩ := hl
  rw [← heq]
  cases hs : orig.status with
  | Valid =>
    have hv : orig.isValid = true := by unfold BucketLien.isValid; rw [hs]
    simp [hv]
    rfl
  | Impaired =>
    have hv : orig.isValid = false := by unfold BucketLien.isValid; rw [hs]
    simp [hv]
    exact hs

/-- **§14 #41 (per-lien witness, contrapositive)**: no lien in the
    post-state list is Valid. -/
theorem expireLiens_no_valid (liens : List BucketLien) :
    ∀ l ∈ expireLiens liens, l.isValid = false := by
  intro l hl
  have := expireLiens_all_impaired liens l hl
  unfold BucketLien.isValid
  rw [this]

/-- **§14 #41 (id-preservation)**: `expireLiens` doesn't drop, add,
    or re-order liens — every input id is present in the output. -/
theorem expireLiens_preserves_length (liens : List BucketLien) :
    (expireLiens liens).length = liens.length := by
  unfold expireLiens
  exact List.length_map _ _

-- ============================================================================
-- §14 #41 (strengthened): aggregate-bridge theorems
-- ============================================================================

/-- **§14 #41 (post-state Valid sum is zero)**: the per-lien Valid
    sum after expiry is 0 — every Valid lien is gone. This bridges
    to `BackingBucket.expireAndImpairAll_clears_validLiened` (which
    proves `validLiened = 0`). -/
theorem expireLiens_valid_sum_zero (liens : List BucketLien) :
    validSum (expireLiens liens) = 0 := by
  unfold validSum
  have hnone : (expireLiens liens).filter (·.isValid) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro l hl
    have := expireLiens_no_valid liens l hl
    simp [this]
  rw [hnone]
  simp

/-- Amount-preservation: the if-then-else mapper inside `expireLiens`
    leaves the `amount` field unchanged. -/
theorem expireLiens_mapper_preserves_amount (l : BucketLien) :
    (if l.isValid then l.impair else l).amount = l.amount := by
  by_cases hv : l.isValid
  · simp [hv, BucketLien.impair]
  · simp [hv]

/-- Amount-preservation, lifted to the list-level: mapping `(·.amount)`
    over `expireLiens liens` gives the same list as over `liens`. -/
theorem expireLiens_map_amount_eq (liens : List BucketLien) :
    (expireLiens liens).map (·.amount) = liens.map (·.amount) := by
  unfold expireLiens
  rw [List.map_map]
  apply List.map_congr_left
  intro l _
  exact expireLiens_mapper_preserves_amount l

/-- Total amount is preserved by `expireLiens`. -/
theorem expireLiens_totalAmount_eq (liens : List BucketLien) :
    totalAmount (expireLiens liens) = totalAmount liens := by
  unfold totalAmount
  rw [expireLiens_map_amount_eq]

/-- **§14 #41 (post-state Impaired sum is prior Valid + Impaired)**:
    the per-lien Impaired sum after expiry equals the sum of both
    partitions before. This bridges to
    `BackingBucket.expireAndImpairAll_grows_impaired` (which proves
    `impairedLiened' = impairedLiened + validLiened`). -/
theorem expireLiens_impaired_sum_eq (liens : List BucketLien) :
    impairedSum (expireLiens liens) = impairedSum liens + validSum liens := by
  have htotal : validSum (expireLiens liens) + impairedSum (expireLiens liens)
              = totalAmount (expireLiens liens) :=
    validSum_plus_impairedSum_eq_total (expireLiens liens)
  have hvalid : validSum (expireLiens liens) = 0 :=
    expireLiens_valid_sum_zero liens
  have htotal' : totalAmount (expireLiens liens) = totalAmount liens :=
    expireLiens_totalAmount_eq liens
  have horig : validSum liens + impairedSum liens = totalAmount liens :=
    validSum_plus_impairedSum_eq_total liens
  omega

-- ============================================================================
-- §14 #41 (strengthened): bucket-level transition with per-lien backing
-- ============================================================================

/-- A bucket paired with its per-lien list. The two aggregate Nat
    fields on the bucket should match the per-lien `validSum` and
    `impairedSum`; the predicate `consistent` witnesses this. -/
structure BucketWithLiens where
  bucket : BackingBucket
  liens  : List BucketLien
  deriving Repr

namespace BucketWithLiens

/-- The aggregate-counts-match-per-lien invariant. -/
def consistent (bwl : BucketWithLiens) : Prop :=
  validSum bwl.liens = bwl.bucket.validLiened
  ∧ impairedSum bwl.liens = bwl.bucket.impairedLiened

/-- The per-lien-aware expire transition: applies `expireLiens` to
    the lien list and runs `expireAndImpairAll` on the aggregate
    bucket. -/
def expireWithLiens (bwl : BucketWithLiens) : Option BucketWithLiens :=
  match bwl.bucket.expireAndImpairAll with
  | none    => none
  | some b' => some { bucket := b', liens := expireLiens bwl.liens }

/-- **§14 #41 (per-lien transition preserves consistency)**: if the
    input bucket is consistent with its per-lien list, the
    post-transition state is also consistent. The per-lien Valid
    sum drops to 0 (matching post-state `validLiened = 0`); the
    per-lien Impaired sum gains the prior Valid sum (matching
    post-state `impairedLiened' = impairedLiened + validLiened`). -/
theorem expireWithLiens_preserves_consistency
    (bwl bwl' : BucketWithLiens)
    (hcons : bwl.consistent) (h : bwl.expireWithLiens = some bwl') :
    bwl'.consistent := by
  unfold expireWithLiens at h
  cases hb : bwl.bucket.expireAndImpairAll with
  | none => rw [hb] at h; cases h
  | some b' =>
    rw [hb] at h
    injection h with heq
    subst heq
    unfold consistent
    obtain ⟨hvcons, hicons⟩ := hcons
    refine ⟨?_, ?_⟩
    · -- validSum (expireLiens bwl.liens) = b'.validLiened
      rw [expireLiens_valid_sum_zero bwl.liens]
      exact (BackingBucket.expireAndImpairAll_clears_validLiened
              bwl.bucket b' hb).symm
    · -- impairedSum (expireLiens bwl.liens) = b'.impairedLiened
      rw [expireLiens_impaired_sum_eq bwl.liens, hicons, hvcons]
      exact (BackingBucket.expireAndImpairAll_grows_impaired
              bwl.bucket b' hb).symm

/-- **§14 #41 (per-lien transition: every post-lien is Impaired)**: a
    successful `expireWithLiens` has the stronger property that
    every individual lien in the output is now Impaired — the
    per-lien content the audit asked for, lifted to the paired
    state. -/
theorem expireWithLiens_all_liens_impaired
    (bwl bwl' : BucketWithLiens) (h : bwl.expireWithLiens = some bwl') :
    ∀ l ∈ bwl'.liens, l.status = .Impaired := by
  unfold expireWithLiens at h
  cases hb : bwl.bucket.expireAndImpairAll with
  | none => rw [hb] at h; cases h
  | some b' =>
    rw [hb] at h
    injection h with heq
    subst heq
    exact expireLiens_all_impaired bwl.liens

/-- **§14 #41 (post-state bucket is Impaired status, lifted)**. -/
theorem expireWithLiens_bucket_status_impaired
    (bwl bwl' : BucketWithLiens) (h : bwl.expireWithLiens = some bwl') :
    bwl'.bucket.status = .Impaired := by
  unfold expireWithLiens at h
  cases hb : bwl.bucket.expireAndImpairAll with
  | none => rw [hb] at h; cases h
  | some b' =>
    rw [hb] at h
    injection h with heq
    subst heq
    exact (BackingBucket.expireAndImpairAll_status_impaired
            bwl.bucket b' hb).2

end BucketWithLiens

end Percolator.Spec
