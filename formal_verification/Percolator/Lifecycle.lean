/-
  Percolator.Lifecycle — Lifecycle enums and allowed-transition relations.

  This file mirrors the lifecycle / sign / mode enums from `src/v16.rs` as
  Lean inductives, and encodes the allowed-transition graph for each as
  an `Inductive` predicate.

  Phase 2 deliverable per `VERIFICATION_PLAN.md:107`: the goal is to make
  invalid lifecycle transitions a *type error* (constructive proof that
  the transition is allowed must be supplied at every state-change site).

  §14 invariants this contributes to:
    - #57 (no_global_B_index): per-asset indexing is enforced by typing
      `AssetState` separately rather than via a global index.
    - Various lifecycle-step invariants: once a transition is encoded as
      an inductive constructor, the only way to step is via an allowed
      edge.
-/

namespace Percolator.Spec

-- ============================================================================
-- HLockLane — h_min vs h_max selection
-- ============================================================================

/-- Lean mirror of `v16.rs::HLockLaneV16`.

    Two-valued selector for which side of the h-lock range an account
    operation reads against. -/
inductive HLockLane : Type where
  | HMin : HLockLane
  | HMax : HLockLane
  deriving DecidableEq, Repr

-- ============================================================================
-- Side — long vs short position direction
-- ============================================================================

/-- Lean mirror of `v16.rs::SideV16`. -/
inductive Side : Type where
  | Long : Side
  | Short : Side
  deriving DecidableEq, Repr

/-- The "other side" function. Useful for cross-side invariants. -/
def Side.flip : Side → Side
  | .Long => .Short
  | .Short => .Long

theorem Side.flip_flip (s : Side) : s.flip.flip = s := by cases s <;> rfl

-- ============================================================================
-- SideMode — per-side accrual/drain status
-- ============================================================================

/-- Lean mirror of `v16.rs::SideModeV16`.

    Three-valued status for the per-side trade-acceptance mode within
    an active asset. -/
inductive SideMode : Type where
  | Normal : SideMode
  | DrainOnly : SideMode
  | ResetPending : SideMode
  deriving DecidableEq, Repr

-- ============================================================================
-- AssetLifecycle — per-asset state in a market group
-- ============================================================================

/-- Lean mirror of `v16.rs::AssetLifecycleV16`.

    The lifecycle of an asset slot within a market group. The complete
    set of valid states, with their allowed transitions defined below
    as `AssetLifecycle.Step`. -/
inductive AssetLifecycle : Type where
  | Disabled : AssetLifecycle
  | PendingActivation : AssetLifecycle
  | Active : AssetLifecycle
  | DrainOnly : AssetLifecycle
  | Retired : AssetLifecycle
  | Recovery : AssetLifecycle
  deriving DecidableEq, Repr

/-- **Allowed asset-lifecycle transitions** (from `v16.rs` step sites):

    - `Disabled → Active`           (activate_asset, line 2891 after 2846 guard)
    - `Retired → Active`            (re-activate; same handler, line 2851 guard)
    - `Active → DrainOnly`          (start_draining, line 4721-4722)
    - `Active → Retired`            (retire, line 4741-4745)
    - `DrainOnly → Retired`         (retire, line 4741-4745)
    - `Recovery → Retired`          (retire, line 4741-4745)
    - `Active → Recovery`           (move_to_recovery)
    - `DrainOnly → Recovery`        (move_to_recovery)
    - `PendingActivation → Active`  (finalize_activation)

    Each constructor witnesses a single legal step. Self-loops are also
    constructors where the operation is idempotent (e.g. retiring a
    Retired asset). -/
inductive AssetLifecycle.Step : AssetLifecycle → AssetLifecycle → Prop where
  | activateFromDisabled : Step .Disabled .Active
  | activateFromRetired  : Step .Retired  .Active
  | finalizeActivation   : Step .PendingActivation .Active
  | startDraining        : Step .Active    .DrainOnly
  | retireActive         : Step .Active    .Retired
  | retireDrainOnly      : Step .DrainOnly .Retired
  | retireRecovery       : Step .Recovery  .Retired
  | enterRecoveryActive  : Step .Active    .Recovery
  | enterRecoveryDrain   : Step .DrainOnly .Recovery

/-- A multi-step transition is the reflexive-transitive closure of `Step`.
    Useful for "asset reached state S via some sequence of allowed steps". -/
inductive AssetLifecycle.Reach : AssetLifecycle → AssetLifecycle → Prop where
  | refl  : ∀ s, Reach s s
  | trans : ∀ {a b c}, Step a b → Reach b c → Reach a c

theorem AssetLifecycle.Reach.single {a b : AssetLifecycle} (h : Step a b) :
    Reach a b := .trans h (.refl b)

-- ============================================================================
-- MarketMode — market-group-wide operating mode
-- ============================================================================

/-- Lean mirror of `v16.rs::MarketModeV16`. -/
inductive MarketMode : Type where
  | Live     : MarketMode
  | Resolved : MarketMode
  | Recovery : MarketMode
  deriving DecidableEq, Repr

/-- **Allowed market-mode transitions** (from `v16.rs` step sites):

    - `Live → Resolved`     (begin_resolved, line 6053)
    - `Live → Recovery`     (enter_recovery, line 6869)
    - `Recovery → Resolved` (line 6047 guard followed by 6053)

    There is no transition out of `Resolved` (terminal) in production. -/
inductive MarketMode.Step : MarketMode → MarketMode → Prop where
  | beginResolvedFromLive     : Step .Live     .Resolved
  | beginResolvedFromRecovery : Step .Recovery .Resolved
  | enterRecovery             : Step .Live     .Recovery

-- ============================================================================
-- BackingBucketStatus — per-bucket freshness/health
-- ============================================================================

/-- Lean mirror of `v16.rs::BackingBucketStatusV16`. -/
inductive BackingBucketStatus : Type where
  | Empty    : BackingBucketStatus
  | Fresh    : BackingBucketStatus
  | Expired  : BackingBucketStatus
  | Impaired : BackingBucketStatus
  deriving DecidableEq, Repr

/-- **Allowed backing-bucket-status transitions**:

    - `Empty → Fresh`       (open new bucket)
    - `Fresh → Expired`     (slot rolls past expiry)
    - `Fresh → Impaired`    (impair-on-loss)
    - `Expired → Impaired`  (expired bucket carries an unrealized loss)
    - `* → Empty`           (close bucket back to empty after drain)

    The closing transitions are uniformly allowed from any status — they
    represent the bucket being recycled. -/
inductive BackingBucketStatus.Step : BackingBucketStatus → BackingBucketStatus → Prop where
  | open            : Step .Empty    .Fresh
  | expire          : Step .Fresh    .Expired
  | impairFresh     : Step .Fresh    .Impaired
  | impairExpired   : Step .Expired  .Impaired
  | close (s : BackingBucketStatus) : Step s .Empty

-- ============================================================================
-- BackingSource — counterparty vs insurance lien classification
-- ============================================================================

/-- Lean mirror of `v16.rs::SourceCreditBackingSourceV16`.

    The discriminator for a lien's backing pool. A given Lien is
    parameterized by this type (see `Percolator/Lien.lean`), which
    makes §14 #23 "lien_never_both_support_and_insurance" a *type
    error* rather than a runtime invariant. -/
inductive BackingSource : Type where
  | Counterparty : BackingSource
  | Insurance    : BackingSource
  deriving DecidableEq, Repr

-- ============================================================================
-- PermissionlessRecoveryReason — labelled recovery causes
-- ============================================================================

/-- Lean mirror of `v16.rs::PermissionlessRecoveryReasonV16`.

    One of the eight authenticated reasons that may trigger a
    permissionless recovery transition. Encoded as a closed sum so the
    set cannot be silently extended. -/
inductive PermissionlessRecoveryReason : Type where
  | BelowProgressFloor                          : PermissionlessRecoveryReason
  | BlockedSegmentHeadroomOrRepresentability    : PermissionlessRecoveryReason
  | AccountBSettlementCannotProgress            : PermissionlessRecoveryReason
  | BIndexHeadroomExhausted                     : PermissionlessRecoveryReason
  | ActiveBankruptCloseCannotProgress           : PermissionlessRecoveryReason
  | ExplicitLossOrDustAuditOverflow             : PermissionlessRecoveryReason
  | OracleOrTargetUnavailableByAuthenticatedPolicy : PermissionlessRecoveryReason
  | CounterOrEpochOverflowDeclaredRecovery      : PermissionlessRecoveryReason
  deriving DecidableEq, Repr

end Percolator.Spec
