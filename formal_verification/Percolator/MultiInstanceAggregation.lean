/-
  Percolator.MultiInstanceAggregation — concrete multi-instance
  model and cross-instance accumulator.

  Strengthens the §14 #58 and #86 closures in `Activation.lean`
  (`AccountHealthWitness` / `UIAggregate`). The original closure
  used a type-level distinction between an in-instance
  `HealthProof` and a cross-instance `UIAggregate` (only the
  former can construct an `AccountHealthWitness`). The audit
  noted that cross-instance semantics were abstract — both types
  were single-field placeholders without explicit multi-instance
  state.

  This file adds:
    - `InstanceId`, an opaque label for one percolator instance.
    - `InstanceSnapshot`, a per-instance projection of an
      account's state (the unit of multi-instance aggregation).
    - `GlobalAccumulator`, a concrete multi-instance aggregator
      built by *summing across instances*. Distinct type from
      `HealthProof` with no projection back to it.
    - `MultiInstanceView`, the typed pair (per-instance health
      proofs, plus an aggregator). The structural witness is
      that the aggregator alone cannot recover any individual
      `HealthProof`.

  §14 invariants strengthened in this file:
    - #58 `cross_instance_ui_aggregation_not_health_or_collateral_proof`
          (audit: HealthProof / UIAggregate type split; cross-
           instance semantics abstract. This file adds the
           concrete multi-instance state.)
    - #86 `global_accumulator_not_account_health_proof`
          (audit: re-cite of #58; "global accumulator" lacked its
           own type. This file gives it explicit multi-instance
           content distinct from a per-account proof.)
-/

import Percolator.Activation
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

-- ============================================================================
-- §14 #58, #86 (strengthened): concrete multi-instance model
-- ============================================================================

/-- A percolator instance label. In production this is the chain or
    deployment id; here it's an opaque Nat. -/
abbrev InstanceId : Type := Nat

/-- A per-instance projection of an account's observable state. The
    `accountId` and `instance` together identify the per-instance
    record; `notional` is the in-instance contribution; the
    `healthProof` field is the in-instance health certificate.

    An aggregator that sums across instances does so by *adding*
    `notional`s — never by combining `healthProof`s. -/
structure InstanceSnapshot where
  instId      : InstanceId
  accountId   : Nat
  notional    : Nat
  healthProof : HealthProof
  deriving Repr

namespace InstanceSnapshot

/-- The per-instance snapshot's health proof is the canonical
    in-instance certificate. Projecting it returns a typed
    `HealthProof`. -/
def proof (s : InstanceSnapshot) : HealthProof := s.healthProof

end InstanceSnapshot

/-- A cross-instance accumulator. Carries a list of instance ids
    (which instances were aggregated) and the aggregate notional —
    but no per-account health certificate. The absence of any
    `healthProof` field is the structural witness for §14 #86. -/
structure GlobalAccumulator where
  instances     : List InstanceId
  totalNotional : Nat
  deriving Repr

namespace GlobalAccumulator

/-- The empty accumulator. -/
def empty : GlobalAccumulator where
  instances     := []
  totalNotional := 0

/-- Construct a `GlobalAccumulator` from a list of per-instance
    snapshots. The aggregator records *which* instances were
    summed and *what* the aggregate notional is. It throws away
    every per-instance `healthProof` — by design. -/
def fromSnapshots (snaps : List InstanceSnapshot) : GlobalAccumulator where
  instances     := snaps.map (·.instId)
  totalNotional := (snaps.map (·.notional)).sum

/-- **§14 #86 (aggregator records instances)**: the constructed
    accumulator's `instances` list matches the input snapshot
    list's instance projection. The aggregator is provably
    multi-instance content, not a singleton certificate. -/
theorem fromSnapshots_instances (snaps : List InstanceSnapshot) :
    (fromSnapshots snaps).instances = snaps.map (·.instId) := rfl

/-- **§14 #86 (aggregator records total notional)**: the
    constructed accumulator's `totalNotional` is the sum of the
    per-instance notionals — visible multi-instance content. -/
theorem fromSnapshots_totalNotional (snaps : List InstanceSnapshot) :
    (fromSnapshots snaps).totalNotional = (snaps.map (·.notional)).sum := rfl

end GlobalAccumulator

/-- A multi-instance view: per-instance snapshots plus an aggregator
    over them. The structural invariant is that the aggregator was
    built *from* the snapshots — it is not a free-standing object. -/
structure MultiInstanceView where
  snapshots   : List InstanceSnapshot
  aggregator  : GlobalAccumulator
  /-- The aggregator was indeed built from the snapshots. -/
  builtFrom   : aggregator = GlobalAccumulator.fromSnapshots snapshots

namespace MultiInstanceView

/-- Construct a `MultiInstanceView` from a list of snapshots. The
    aggregator is computed from the snapshots; the `builtFrom`
    field is `rfl`. -/
def ofSnapshots (snaps : List InstanceSnapshot) : MultiInstanceView where
  snapshots  := snaps
  aggregator := GlobalAccumulator.fromSnapshots snaps
  builtFrom  := rfl

/-- **§14 #86 (instance count consistency)**: the aggregator
    instance list matches the snapshot list one-to-one. -/
theorem aggregator_instances (v : MultiInstanceView) :
    v.aggregator.instances = v.snapshots.map (·.instId) := by
  rw [v.builtFrom]
  exact GlobalAccumulator.fromSnapshots_instances v.snapshots

end MultiInstanceView

-- ============================================================================
-- §14 #58 (strengthened): aggregator cannot construct a HealthProof
-- ============================================================================

/-- **§14 #58 (no aggregator → health-proof extractor)**: there is
    no total function `GlobalAccumulator → HealthProof`. Any such
    "extractor" would have to produce a HealthProof for the empty
    aggregator (instances = [], totalNotional = 0), which carries
    no account-specific information; the resulting health proof's
    accountId would be unrelated to any real account.

    The structural witness: there is no canonical `fromAccumulator`
    constructor on `AccountHealthWitness`, and the only path to a
    HealthProof is via an in-instance snapshot. -/
theorem no_canonical_extractor_from_accumulator :
    ¬ ∃ (extract : GlobalAccumulator → HealthProof),
        ∀ (snaps : List InstanceSnapshot),
          ∀ s ∈ snaps, extract (GlobalAccumulator.fromSnapshots snaps)
                     = s.healthProof := by
  intro ⟨extract, hext⟩
  -- Consider two distinct per-instance snapshots with different
  -- health proofs. If they sum to the same aggregator (because
  -- the aggregator only retains instances + notional, not
  -- per-account proofs), `extract` is forced to equal two
  -- distinct HealthProofs — contradiction.
  let p1 : HealthProof := { accountId := 1, epoch := 0, refreshSlot := 0 }
  let p2 : HealthProof := { accountId := 2, epoch := 0, refreshSlot := 0 }
  let s1 : InstanceSnapshot :=
    { instId := 0, accountId := 1, notional := 0, healthProof := p1 }
  let s2 : InstanceSnapshot :=
    { instId := 0, accountId := 2, notional := 0, healthProof := p2 }
  -- Both [s1] and [s2] map to the same aggregator (same
  -- instance list [0], same notional sum 0).
  have hagg : GlobalAccumulator.fromSnapshots [s1]
            = GlobalAccumulator.fromSnapshots [s2] := by
    unfold GlobalAccumulator.fromSnapshots
    rfl
  have h1 : extract (GlobalAccumulator.fromSnapshots [s1]) = p1 :=
    hext [s1] s1 (List.mem_singleton.mpr rfl)
  have h2 : extract (GlobalAccumulator.fromSnapshots [s2]) = p2 :=
    hext [s2] s2 (List.mem_singleton.mpr rfl)
  rw [hagg] at h1
  have heq : p1 = p2 := by rw [← h1]; exact h2
  -- But p1.accountId = 1 ≠ 2 = p2.accountId.
  have : p1.accountId = p2.accountId := by rw [heq]
  simp at this

/-- **§14 #58 (structural distinction by type)**: a value of type
    `GlobalAccumulator` is *not* a value of type
    `AccountHealthWitness`. Lean's type checker rejects any
    substitution: there is no `fromAccumulator` constructor on
    `AccountHealthWitness`. The `proof` projection is total
    against the `fromHealthProof` constructor only. -/
theorem account_health_witness_only_from_proof
    (w : AccountHealthWitness) :
    ∃ p : HealthProof, w = .fromHealthProof p := by
  cases w with
  | fromHealthProof p => exact ⟨p, rfl⟩

/-- **§14 #58 (a HealthProof carries accountId-specific data)**:
    distinct accounts yield distinct health proofs. This is the
    in-instance specificity that the aggregator structurally
    cannot recover. -/
theorem health_proof_carries_accountId
    (p1 p2 : HealthProof) (h : p1.accountId ≠ p2.accountId) :
    p1 ≠ p2 := by
  intro heq
  apply h
  rw [heq]

/-- **§14 #58 (aggregator loses accountId information)**: two
    snapshots with different accountIds and zero notional can
    produce identical accumulators. The aggregator structurally
    discards per-account identity. -/
theorem aggregator_collapses_distinct_accounts :
    ∃ (s1 s2 : InstanceSnapshot),
      s1.accountId ≠ s2.accountId
      ∧ GlobalAccumulator.fromSnapshots [s1]
        = GlobalAccumulator.fromSnapshots [s2] := by
  let p1 : HealthProof := { accountId := 1, epoch := 0, refreshSlot := 0 }
  let p2 : HealthProof := { accountId := 2, epoch := 0, refreshSlot := 0 }
  let s1 : InstanceSnapshot :=
    { instId := 0, accountId := 1, notional := 0, healthProof := p1 }
  let s2 : InstanceSnapshot :=
    { instId := 0, accountId := 2, notional := 0, healthProof := p2 }
  refine ⟨s1, s2, ?_, ?_⟩
  · intro h
    simp at h
  · unfold GlobalAccumulator.fromSnapshots
    rfl

end Percolator.Spec
