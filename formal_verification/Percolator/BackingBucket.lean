/-
  Percolator.BackingBucket — Phase 5 cluster 3: backing bucket lifecycle.

  Models a single per-domain backing bucket (Rust counterpart at
  `v16.rs::BackingBucketV16`, line 875). Each bucket holds counterparty
  backing in four partitions (`freshUnliened`, `validLiened`,
  `consumedLiened`, `impairedLiened`) plus an expiry slot and a status
  tag (`Empty | Fresh | Expired | Impaired`).

  This file defines the per-bucket transition functions and the
  aggregation lemma that bridges per-bucket state to source-level
  state.

  §14 invariants addressed:
    - #34 `backing_bucket_expiry_does_not_underflow_available_backing`
    - #35 `backing_bucket_expiry_does_not_increase_available_backing_or_credit_rate`
    - #36 `backing_bucket_expiry_after_partial_lien_consumption_does_not_inflate_available`
    - #40 `source_available_backing_recomputes_from_bucket_sums`
-/

import Percolator.Lifecycle
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- BackingBucket — single per-domain bucket
-- ============================================================================

/-- Lean mirror of `v16.rs::BackingBucketV16` (line 875).

    A bucket is the unit of backing freshness/expiry. The four amount
    partitions cover the bucket's backing across its lifecycle states. -/
structure BackingBucket where
  marketId           : Nat
  freshUnliened      : Nat
  validLiened        : Nat
  consumedLiened     : Nat
  impairedLiened     : Nat
  expirySlot         : Nat
  status             : BackingBucketStatus
  deriving Repr

namespace BackingBucket

/-- An empty bucket for a market. -/
def emptyForMarket (marketId : Nat) : BackingBucket where
  marketId       := marketId
  freshUnliened  := 0
  validLiened    := 0
  consumedLiened := 0
  impairedLiened := 0
  expirySlot     := 0
  status         := .Empty

/-- Total backing held in this bucket across all four partitions. -/
def totalBacking (b : BackingBucket) : Nat :=
  b.freshUnliened + b.validLiened + b.consumedLiened + b.impairedLiened

/-- Available (un-liened, un-consumed, un-impaired) backing — what can
    be drawn against. Equals `freshUnliened`. -/
def available (b : BackingBucket) : Nat := b.freshUnliened

-- ============================================================================
-- Lifecycle transitions
-- ============================================================================

/-- **Open**: Empty bucket → Fresh, with `amount` freshly-deposited
    backing and an expiry slot. (Renamed from `open` since that's a
    Lean keyword.) -/
def openFresh (b : BackingBucket) (amount expirySlot : Nat) : Option BackingBucket :=
  if b.status ≠ .Empty then none
  else some {
    b with
    freshUnliened := amount
    expirySlot := expirySlot
    status := .Fresh
  }

/-- **Expire**: Fresh bucket → Expired. Only the status tag changes; no
    amount field is touched.

    This is the §14 #34/#35 transition: expiry must not underflow or
    inflate available backing. By construction here it changes only
    `status`, so all amounts are preserved. -/
def expire (b : BackingBucket) : Option BackingBucket :=
  if b.status ≠ .Fresh then none
  else some { b with status := .Expired }

/-- **Impair**: Fresh or Expired → Impaired. Status change only; the
    actual partition updates that move freshUnliened to impairedLiened
    are explicit operations (`partitionImpair`). -/
def markImpaired (b : BackingBucket) : Option BackingBucket :=
  if b.status = .Empty then none
  else some { b with status := .Impaired }

/-- **Lien against the bucket**: move `amount` from freshUnliened to
    validLiened. The bucket loses available backing equal to `amount`. -/
def lienAgainst (b : BackingBucket) (amount : Nat) : Option BackingBucket :=
  if b.freshUnliened < amount then none
  else some {
    b with
    freshUnliened := b.freshUnliened - amount
    validLiened := b.validLiened + amount
  }

/-- **Consume a lien**: move `amount` from validLiened to
    consumedLiened. The backing is gone (spent). -/
def consumeLien (b : BackingBucket) (amount : Nat) : Option BackingBucket :=
  if b.validLiened < amount then none
  else some {
    b with
    validLiened := b.validLiened - amount
    consumedLiened := b.consumedLiened + amount
  }

/-- **Release a lien**: move `amount` from validLiened back to
    freshUnliened. The backing returns to available. -/
def releaseLien (b : BackingBucket) (amount : Nat) : Option BackingBucket :=
  if b.validLiened < amount then none
  else some {
    b with
    validLiened := b.validLiened - amount
    freshUnliened := b.freshUnliened + amount
  }

/-- **Mark a lien impaired**: move `amount` from validLiened to
    impairedLiened. Backing stays in the bucket but is now bad. -/
def impairLien (b : BackingBucket) (amount : Nat) : Option BackingBucket :=
  if b.validLiened < amount then none
  else some {
    b with
    validLiened := b.validLiened - amount
    impairedLiened := b.impairedLiened + amount
  }

-- ============================================================================
-- §14 #34, #35: expire is status-only
-- ============================================================================

/-- **§14 #34**: expire does not underflow `available` — it does not
    decrement `freshUnliened`.

    Direct from the definition: only `status` is updated. -/
theorem expire_preserves_available (b b' : BackingBucket)
    (h : b.expire = some b') : b'.available = b.available := by
  unfold expire at h
  by_cases hs : b.status ≠ .Fresh
  · rw [if_pos hs] at h; cases h
  rw [if_neg hs] at h
  have := Option.some.inj h
  subst this
  rfl

/-- **§14 #35**: expire does not *increase* `available`. The stronger
    form: expire preserves `available` exactly. -/
theorem expire_does_not_increase_available (b b' : BackingBucket)
    (h : b.expire = some b') : b'.available ≤ b.available := by
  rw [expire_preserves_available b b' h]

/-- **§14 #34/#35 (corollary)**: expire is exactly the identity on every
    backing partition. -/
theorem expire_preserves_amounts (b b' : BackingBucket)
    (h : b.expire = some b') :
    b'.freshUnliened = b.freshUnliened
    ∧ b'.validLiened = b.validLiened
    ∧ b'.consumedLiened = b.consumedLiened
    ∧ b'.impairedLiened = b.impairedLiened
    ∧ b'.totalBacking = b.totalBacking := by
  unfold expire at h
  by_cases hs : b.status ≠ .Fresh
  · rw [if_pos hs] at h; cases h
  rw [if_neg hs] at h
  have := Option.some.inj h
  subst this
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  unfold totalBacking
  rfl

/-- **§14 #34/#35 (status change)**: expire transitions the status from
    Fresh to Expired. -/
theorem expire_status (b b' : BackingBucket) (h : b.expire = some b') :
    b.status = .Fresh ∧ b'.status = .Expired := by
  unfold expire at h
  by_cases hs : b.status ≠ .Fresh
  · rw [if_pos hs] at h; cases h
  rw [if_neg hs] at h
  push_neg at hs
  have := Option.some.inj h
  subst this
  exact ⟨hs, rfl⟩

-- ============================================================================
-- §14 #36: expiry after partial consumption doesn't inflate available
-- ============================================================================

/-- **`consumeLien` reduces `available` — no, wait**: actually
    `consumeLien` operates on `validLiened`, not `freshUnliened`, so
    `available = freshUnliened` is preserved.

    What §14 #36 really cares about: after `lienAgainst` partially
    consumes the fresh pool (via creating a lien), the available
    backing has gone down. Subsequent `expire` does not restore it. -/
theorem available_after_lien_then_expire
    (b b' b'' : BackingBucket) (amount : Nat)
    (h1 : b.lienAgainst amount = some b')
    (h2 : b'.expire = some b'') :
    b''.available ≤ b.available := by
  -- After lienAgainst: b'.available = b.available - amount
  -- After expire: b''.available = b'.available
  -- So b''.available = b.available - amount ≤ b.available
  have hsub : b'.available = b.available - amount := by
    unfold lienAgainst at h1
    by_cases hlt : b.freshUnliened < amount
    · rw [if_pos hlt] at h1; cases h1
    rw [if_neg hlt] at h1
    have := Option.some.inj h1
    subst this
    rfl
  rw [expire_preserves_available _ _ h2, hsub]
  exact Nat.sub_le _ _

-- ============================================================================
-- §14 #40: source-level available = sum of per-bucket available
-- ============================================================================

/-- Aggregate `available` across a list of buckets — the per-source
    realizable backing. -/
def sumAvailable (buckets : List BackingBucket) : Nat :=
  (buckets.map BackingBucket.available).sum

/-- Aggregate `freshUnliened` across buckets. Same as `sumAvailable`. -/
def sumFreshUnliened (buckets : List BackingBucket) : Nat :=
  (buckets.map BackingBucket.freshUnliened).sum

/-- Aggregate `validLiened` across buckets. -/
def sumValidLiened (buckets : List BackingBucket) : Nat :=
  (buckets.map BackingBucket.validLiened).sum

/-- Aggregate `impairedLiened` across buckets. -/
def sumImpairedLiened (buckets : List BackingBucket) : Nat :=
  (buckets.map BackingBucket.impairedLiened).sum

/-- **§14 #40**: source-level `available` (= `freshUnliened` total) is
    the sum of per-bucket available. Trivially true by definition;
    documents the aggregation principle. -/
theorem sumAvailable_eq_sumFreshUnliened (buckets : List BackingBucket) :
    sumAvailable buckets = sumFreshUnliened buckets := by
  unfold sumAvailable sumFreshUnliened available
  rfl

/-- **§14 #40 (additivity)**: cons-ing a bucket onto the list adds its
    `available` to the sum. -/
theorem sumAvailable_cons (b : BackingBucket) (rest : List BackingBucket) :
    sumAvailable (b :: rest) = b.available + sumAvailable rest := by
  unfold sumAvailable
  simp

-- ============================================================================
-- Source-level invariants of bucket transitions
-- ============================================================================

/-- **Aggregate consequence of `expire`**: replacing one bucket in a
    list with its expired form preserves the sum of `available`. -/
theorem expire_preserves_sumAvailable
    (b b' : BackingBucket) (rest : List BackingBucket)
    (h : b.expire = some b') :
    sumAvailable (b' :: rest) = sumAvailable (b :: rest) := by
  rw [sumAvailable_cons, sumAvailable_cons, expire_preserves_available _ _ h]

/-- **Aggregate consequence of `lienAgainst`**: replacing one bucket
    with its lien-against form *reduces* the sum of `available` by
    exactly the lien amount. -/
theorem lienAgainst_decreases_sumAvailable
    (b b' : BackingBucket) (rest : List BackingBucket) (amount : Nat)
    (h : b.lienAgainst amount = some b') :
    sumAvailable (b' :: rest) + amount = sumAvailable (b :: rest) := by
  have hsub : b'.available = b.available - amount := by
    unfold lienAgainst at h
    by_cases hlt : b.freshUnliened < amount
    · rw [if_pos hlt] at h; cases h
    rw [if_neg hlt] at h
    have := Option.some.inj h
    subst this
    rfl
  have hge : amount ≤ b.available := by
    unfold lienAgainst at h
    by_cases hlt : b.freshUnliened < amount
    · rw [if_pos hlt] at h; cases h
    push_neg at hlt
    exact hlt
  rw [sumAvailable_cons, sumAvailable_cons, hsub]
  omega

/-- **§14 #38 (consumeLien decrements validLiened, credits consumedLiened)**:
    a successful `BackingBucket.consumeLien` strictly decreases the
    `validLiened` partition by `amount` and moves it into
    `consumedLiened`. Combined with `lienAgainst` reducing
    `freshUnliened` at lien creation, the net effect is that the
    spent backing is removed from the bucket's `freshUnliened +
    validLiened` total — the "fresh-reserved" pool from the spec. -/
theorem consumeLien_removes_from_validLiened
    (b b' : BackingBucket) (amount : Nat)
    (h : b.consumeLien amount = some b') :
    b'.validLiened + amount = b.validLiened
    ∧ b'.consumedLiened = b.consumedLiened + amount := by
  unfold consumeLien at h
  by_cases hlt : b.validLiened < amount
  · simp [hlt] at h
  · push_neg at hlt
    simp [hlt] at h
    have hb' := h.symm
    refine ⟨?_, ?_⟩
    · rw [hb']
      change b.validLiened - amount + amount = b.validLiened
      omega
    · rw [hb']

end BackingBucket

end Percolator.Spec
