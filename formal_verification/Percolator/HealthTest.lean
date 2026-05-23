/-
  Percolator.HealthTest — health-test formula with single-counted
  pending-obligation exposure.

  The spec asserts (around §6 and §10) that the account health test
  combines positive components (capital, source-credit, certified
  health) against negative components (loss exposure, locked face
  claim, pending obligation exposure). The pending-obligation
  exposure MUST appear exactly once on the negative side — no
  per-leg multiplication, no aggregate double-count.

  The §14 #89 invariant is closed by writing the health test as a
  single explicit formula in `Nat × Int` arithmetic and proving by
  inspection that the pending-obligation term occurs exactly once.
  The single-count property is captured by the structural shape:
  any function consuming `HealthInputs` reads
  `pendingObligationExposure` at most once.

  §14 invariants addressed:
    - #89 `pending_obligation_exposure_counted_exactly_once_in_health_test`
-/

import Percolator.Defs
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

/-- The bundled inputs to the per-account health test.

    Positive components contribute to equity (`capital`,
    `sourceCreditNum`, `certifiedHealthBonus`).

    Negative components subtract from equity (`lossExposure`,
    `lockedFaceClaim`, `pendingObligationExposure`,
    `maintenanceRequirement`).

    `pendingObligationExposure` is the named term that §14 #89
    constrains to single-counting. -/
structure HealthInputs where
  capital                   : Nat
  sourceCreditNum           : Nat
  certifiedHealthBonus      : Nat
  lossExposure              : Nat
  lockedFaceClaim           : Nat
  pendingObligationExposure : Nat
  maintenanceRequirement    : Nat
  deriving Repr

namespace HealthInputs

/-- Positive equity component — sum of the three positive inputs. -/
def positiveEquity (h : HealthInputs) : Nat :=
  h.capital + h.sourceCreditNum + h.certifiedHealthBonus

/-- Negative equity component — sum of the four negative inputs,
    with `pendingObligationExposure` appearing exactly once. -/
def negativeEquity (h : HealthInputs) : Nat :=
  h.lossExposure + h.lockedFaceClaim + h.pendingObligationExposure
  + h.maintenanceRequirement

/-- The health test result: an `Int` to allow under-collateralized
    states. -/
def equity (h : HealthInputs) : Int :=
  (h.positiveEquity : Int) - (h.negativeEquity : Int)

/-- An account is healthy iff equity is non-negative. -/
def isHealthy (h : HealthInputs) : Prop :=
  0 ≤ h.equity

instance (h : HealthInputs) : Decidable h.isHealthy := by
  unfold isHealthy; infer_instance

-- ============================================================================
-- §14 #89: pending-obligation exposure counted exactly once
-- ============================================================================

/-- **§14 #89 (additivity)**: the negative-equity formula
    distributes over `pendingObligationExposure` linearly with
    coefficient one. Increasing the exposure by `d` increases the
    negative side by exactly `d`. -/
theorem negativeEquity_increment_in_pending
    (h : HealthInputs) (d : Nat) :
    ({ h with pendingObligationExposure := h.pendingObligationExposure + d }
      : HealthInputs).negativeEquity
    = h.negativeEquity + d := by
  unfold negativeEquity
  show h.lossExposure + h.lockedFaceClaim + (h.pendingObligationExposure + d)
       + h.maintenanceRequirement
     = h.lossExposure + h.lockedFaceClaim + h.pendingObligationExposure
       + h.maintenanceRequirement + d
  omega

/-- **§14 #89 (no other appearance)**: `positiveEquity` does NOT read
    `pendingObligationExposure` at all. The negative side is the
    only place this term appears. -/
theorem positiveEquity_independent_of_pending
    (h : HealthInputs) (d : Nat) :
    ({ h with pendingObligationExposure := d } : HealthInputs).positiveEquity
    = h.positiveEquity := by
  unfold positiveEquity
  rfl

/-- **§14 #89 (equity decrement matches exposure increment)**: when
    pending-obligation exposure rises by `d`, equity drops by
    exactly `d`. No double-count would produce a `2*d` drop; no
    miscount would produce a smaller drop. -/
theorem equity_decreases_by_pending_increment
    (h : HealthInputs) (d : Nat) :
    ({ h with pendingObligationExposure := h.pendingObligationExposure + d }
      : HealthInputs).equity
    = h.equity - d := by
  unfold equity
  rw [positiveEquity_independent_of_pending,
      negativeEquity_increment_in_pending]
  push_cast
  linarith

/-- **§14 #89 (zero-exposure baseline)**: when `pendingObligationExposure = 0`,
    equity reduces to the standard `positive − rest-of-negative`
    formula. -/
theorem equity_at_zero_pending (h : HealthInputs)
    (hzero : h.pendingObligationExposure = 0) :
    h.equity
    = (h.positiveEquity : Int)
      - (h.lossExposure + h.lockedFaceClaim + h.maintenanceRequirement : Int) := by
  unfold equity negativeEquity
  rw [hzero]
  push_cast
  linarith

/-- **§14 #89 (no per-leg double-count)**: if one tries to count
    pending exposure twice in the negative equity, the resulting
    formula is `negativeEquity + pendingObligationExposure` —
    strictly greater than the spec formula whenever there is exposure.
    Modeled here as the explicit difference. -/
theorem double_counted_negativeEquity_exceeds_spec
    (h : HealthInputs) :
    h.negativeEquity + h.pendingObligationExposure
    ≥ h.negativeEquity := Nat.le_add_right _ _

theorem double_counted_strict_increase
    (h : HealthInputs) (hpos : 0 < h.pendingObligationExposure) :
    h.negativeEquity < h.negativeEquity + h.pendingObligationExposure :=
  Nat.lt_add_of_pos_right hpos

end HealthInputs

-- ============================================================================
-- §14 #90: PenaltySource enum with category tags (equity vs requirement)
-- ============================================================================

/-- The classification of a penalty: does it deduct from equity or
    add to the maintenance requirement? Per spec these are disjoint
    sides of the health test. -/
inductive PenaltyCategory : Type where
  | equity      : PenaltyCategory
  | requirement : PenaltyCategory
  deriving DecidableEq, Repr

/-- A specific penalty source. Each source maps to exactly one
    `PenaltyCategory` and one `HealthInputs` field — the disjointness
    is established by definition. -/
inductive PenaltySource : Type where
  | lossExposure              : PenaltySource
  | lockedFaceClaim           : PenaltySource
  | pendingObligationExposure : PenaltySource
  | maintenanceRequirement    : PenaltySource
  deriving DecidableEq, Repr

namespace PenaltySource

/-- The category each source belongs to. -/
def category : PenaltySource → PenaltyCategory
  | .lossExposure              => .equity
  | .lockedFaceClaim           => .equity
  | .pendingObligationExposure => .equity
  | .maintenanceRequirement    => .requirement

/-- The contribution of each source to the health inputs. -/
def contributionOf (h : HealthInputs) : PenaltySource → Nat
  | .lossExposure              => h.lossExposure
  | .lockedFaceClaim           => h.lockedFaceClaim
  | .pendingObligationExposure => h.pendingObligationExposure
  | .maintenanceRequirement    => h.maintenanceRequirement

end PenaltySource

/-- The sum of contributions across a list of sources. -/
def HealthInputs.sumContributions
    (h : HealthInputs) (sources : List PenaltySource) : Nat :=
  (sources.map (PenaltySource.contributionOf h)).sum

/-- **§14 #90 (each source has exactly one category)**: the category
    function is total and deterministic — no source spans both equity
    and requirement sides. -/
theorem PenaltySource.category_total (s : PenaltySource) :
    s.category = .equity ∨ s.category = .requirement := by
  cases s
  all_goals (first | exact .inl rfl | exact .inr rfl)

/-- **§14 #90 (no source has both categories)**: the category function
    is a function (not a relation), so no source can simultaneously
    be equity and requirement. -/
theorem PenaltySource.category_unique
    (s : PenaltySource) (c1 c2 : PenaltyCategory)
    (h1 : s.category = c1) (h2 : s.category = c2) :
    c1 = c2 := by
  rw [← h1, ← h2]

/-- **§14 #90 (sum decomposition by category)**: the negative-equity
    formula equals the sum over the three equity-category sources
    plus the maintenance-requirement source. Each source contributes
    via `contributionOf` exactly once. -/
theorem HealthInputs.negativeEquity_eq_sum_by_category (h : HealthInputs) :
    h.negativeEquity
    = h.sumContributions [.lossExposure, .lockedFaceClaim, .pendingObligationExposure]
      + h.sumContributions [.maintenanceRequirement] := by
  unfold negativeEquity sumContributions
  simp [PenaltySource.contributionOf]
  omega

/-- **§14 #90 (equity-side sources have equity category)**: the three
    sources in the equity decomposition all map to `.equity`. -/
theorem PenaltySource.equity_sources_have_equity_category :
    PenaltySource.lossExposure.category = .equity
    ∧ PenaltySource.lockedFaceClaim.category = .equity
    ∧ PenaltySource.pendingObligationExposure.category = .equity := by
  refine ⟨rfl, rfl, rfl⟩

/-- **§14 #90 (requirement-side source has requirement category)**: the
    sole requirement-side source maps to `.requirement`. -/
theorem PenaltySource.requirement_source_has_requirement_category :
    PenaltySource.maintenanceRequirement.category = .requirement := rfl

/-- **§14 #90 (disjointness via category mismatch)**: an equity-side
    source's category is provably not equal to a requirement-side
    source's category. -/
theorem PenaltySource.equity_distinct_from_requirement
    (s : PenaltySource) (h : s.category = .equity) :
    s.category ≠ .requirement := by
  rw [h]
  intro contra
  cases contra

end Percolator.Spec
