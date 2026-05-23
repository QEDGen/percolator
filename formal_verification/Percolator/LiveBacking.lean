/-
  Percolator.LiveBacking — backing-bucket freshness exclusion and
  expiry-driven impairment.

  Strengthens `BackingBucket` with a "live" view: only `Fresh` buckets
  contribute to source-credit available backing. Expired, Empty, and
  Impaired buckets are excluded by construction, matching the spec's
  `fresh_reserved_backing_num // sum over Fresh buckets` aggregation
  (`spec.md:251`).

  Also exposes `expireAndImpairAll`, the single transition that
  expires a bucket and moves all of its valid-liened backing into the
  impaired partition — the §14 #41 "bounded work" claim.

  §14 invariants addressed:
    - #7  `source_credit_rate_zero_when_backing_stale_or_exhausted`
    - #41 `expired_liened_bucket_marks_liens_impaired_in_bounded_work`
-/

import Percolator.BackingBucket
import Percolator.CreditRate
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

namespace BackingBucket

-- ============================================================================
-- §14 #7: live backing — only Fresh contributes
-- ============================================================================

/-- The bucket's *live* contribution to source-credit available
    backing: equals `freshUnliened` only when the bucket is `Fresh`.

    Empty, Expired, and Impaired buckets contribute 0. This matches the
    spec's "sum over Fresh buckets of fresh_unliened" definition
    (`spec.md:251`). -/
def liveAvailable (b : BackingBucket) : Nat :=
  if b.status = .Fresh then b.freshUnliened else 0

/-- **§14 #7 (per-bucket)**: a non-Fresh bucket contributes zero live
    backing. Direct from the definition. -/
theorem liveAvailable_zero_of_nonfresh (b : BackingBucket)
    (h : b.status ≠ .Fresh) : liveAvailable b = 0 := by
  unfold liveAvailable
  simp [h]

theorem liveAvailable_eq_freshUnliened_of_fresh (b : BackingBucket)
    (h : b.status = .Fresh) : liveAvailable b = b.freshUnliened := by
  unfold liveAvailable
  simp [h]

/-- An empty bucket contributes zero live. -/
theorem liveAvailable_empty (m : Nat) : liveAvailable (emptyForMarket m) = 0 := by
  unfold liveAvailable emptyForMarket
  simp

/-- Aggregate `liveAvailable` across a list of buckets — the actual
    `fresh_reserved_backing_num` quantity that feeds source-credit
    rate computation. -/
def sumLiveAvailable (buckets : List BackingBucket) : Nat :=
  (buckets.map liveAvailable).sum

theorem sumLiveAvailable_nil : sumLiveAvailable [] = 0 := by
  unfold sumLiveAvailable; simp

theorem sumLiveAvailable_cons (b : BackingBucket) (rest : List BackingBucket) :
    sumLiveAvailable (b :: rest) = liveAvailable b + sumLiveAvailable rest := by
  unfold sumLiveAvailable; simp

/-- **§14 #7 (aggregate exhaustion)**: if every bucket is non-Fresh,
    the live aggregate is zero — capturing both "stale" (Expired,
    Impaired) and "exhausted" (Empty) regimes. -/
theorem sumLiveAvailable_zero_when_all_nonfresh
    (buckets : List BackingBucket) (h : ∀ b ∈ buckets, b.status ≠ .Fresh) :
    sumLiveAvailable buckets = 0 := by
  induction buckets with
  | nil => exact sumLiveAvailable_nil
  | cons b rest ih =>
    rw [sumLiveAvailable_cons]
    have hb : b.status ≠ .Fresh := h b (List.mem_cons_self b rest)
    rw [liveAvailable_zero_of_nonfresh b hb]
    have hrest : ∀ x ∈ rest, x.status ≠ .Fresh := fun x hx =>
      h x (List.mem_cons_of_mem b hx)
    rw [ih hrest]

/-- **§14 #7 (rate corollary)**: `creditRateNum` with zero live
    backing returns zero (for any positive claim). Combines
    `sumLiveAvailable_zero_when_all_nonfresh` with Phase 1's
    `creditRateNum_zero_backing`.

    Concretely: if a source domain's only backing buckets are
    Expired/Empty/Impaired, the rate it can quote is zero whenever
    there is a non-zero claim. -/
theorem creditRate_zero_when_no_fresh
    (buckets : List BackingBucket) (claim : Nat) (hclaim : 0 < claim)
    (h : ∀ b ∈ buckets, b.status ≠ .Fresh) :
    creditRateNum (sumLiveAvailable buckets) claim = 0 := by
  rw [sumLiveAvailable_zero_when_all_nonfresh buckets h]
  exact creditRateNum_zero_backing claim hclaim

/-- **§14 #7 (single-bucket stale → zero)**: convenience corollary
    for the one-bucket case. -/
theorem creditRate_zero_when_single_stale
    (b : BackingBucket) (claim : Nat) (hclaim : 0 < claim)
    (h : b.status ≠ .Fresh) :
    creditRateNum (liveAvailable b) claim = 0 := by
  rw [liveAvailable_zero_of_nonfresh b h]
  exact creditRateNum_zero_backing claim hclaim

-- ============================================================================
-- §14 #41: expired-liened bucket marks liens impaired (bounded work)
-- ============================================================================

/-- **The atomic expire-and-impair transition**: move the bucket to
    `Impaired` status and shift all `validLiened` backing into
    `impairedLiened` in a single step.

    The Rust counterpart is the per-bucket pass that expires fresh
    buckets and impairs their liens (mirrored in `v16.rs`). The
    "bounded work" claim of §14 #41 is structural here: this is a
    single function call, not a loop. -/
def expireAndImpairAll (b : BackingBucket) : Option BackingBucket :=
  if b.status ≠ .Fresh then none
  else some {
    b with
    status        := .Impaired
    validLiened   := 0
    impairedLiened := b.impairedLiened + b.validLiened
  }

/-- **§14 #41 (validLiened drained)**: after `expireAndImpairAll`,
    no valid-liened backing remains in the bucket. -/
theorem expireAndImpairAll_clears_validLiened
    (b b' : BackingBucket) (h : b.expireAndImpairAll = some b') :
    b'.validLiened = 0 := by
  unfold expireAndImpairAll at h
  by_cases hs : b.status ≠ .Fresh
  · simp [hs] at h
  · push_neg at hs
    simp [hs] at h
    have := h.symm
    rw [this]

/-- **§14 #41 (impairedLiened captures the full valid amount)**: the
    bucket's `impairedLiened` strictly grows by the prior `validLiened`. -/
theorem expireAndImpairAll_grows_impaired
    (b b' : BackingBucket) (h : b.expireAndImpairAll = some b') :
    b'.impairedLiened = b.impairedLiened + b.validLiened := by
  unfold expireAndImpairAll at h
  by_cases hs : b.status ≠ .Fresh
  · simp [hs] at h
  · push_neg at hs
    simp [hs] at h
    have := h.symm
    rw [this]

/-- **§14 #41 (total backing conserved)**: the transition does not
    change the bucket's total backing — backing moves between
    partitions but never leaves the bucket. -/
theorem expireAndImpairAll_preserves_totalBacking
    (b b' : BackingBucket) (h : b.expireAndImpairAll = some b') :
    b'.totalBacking = b.totalBacking := by
  unfold expireAndImpairAll at h
  by_cases hs : b.status ≠ .Fresh
  · simp [hs] at h
  · push_neg at hs
    simp [hs] at h
    have := h.symm
    rw [this]
    unfold totalBacking
    show b.freshUnliened + 0 + b.consumedLiened + (b.impairedLiened + b.validLiened)
       = b.freshUnliened + b.validLiened + b.consumedLiened + b.impairedLiened
    omega

/-- **§14 #41 (bucket is now Impaired)**: status flips from Fresh to
    Impaired. -/
theorem expireAndImpairAll_status_impaired
    (b b' : BackingBucket) (h : b.expireAndImpairAll = some b') :
    b.status = .Fresh ∧ b'.status = .Impaired := by
  unfold expireAndImpairAll at h
  by_cases hs : b.status ≠ .Fresh
  · simp [hs] at h
  · push_neg at hs
    simp [hs] at h
    have := h.symm
    refine ⟨hs, ?_⟩
    rw [this]

/-- **§14 #41 (post-transition exclusion from live)**: an
    `expireAndImpairAll`'d bucket contributes zero live backing
    (because its status is now Impaired, not Fresh). This is the
    bridge to §14 #7: an expired-and-impaired bucket no longer
    counts in the credit-rate computation. -/
theorem expireAndImpairAll_excluded_from_live
    (b b' : BackingBucket) (h : b.expireAndImpairAll = some b') :
    liveAvailable b' = 0 := by
  have := (expireAndImpairAll_status_impaired b b' h).2
  exact liveAvailable_zero_of_nonfresh b' (by rw [this]; intro; contradiction)

end BackingBucket

end Percolator.Spec
