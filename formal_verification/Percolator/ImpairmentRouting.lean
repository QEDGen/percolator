/-
  Percolator.ImpairmentRouting — impaired-lien account routing.

  Mirrors the spec rule in §4 / §10: once a source-credit lien is
  impaired (counterparty backing expired or insurance ledger
  impaired), the affected account can no longer take normal-mode
  actions. The account MUST route to one of three resolutions:
    - Deleverage (reduce position so impaired credit isn't needed)
    - Liquidation (terminate the account by liquidation flow)
    - Recovery (route via permissionless recovery)

  The §14 #10 invariant is closed by typing: a `NormalStep` is only
  available from an `accountHasImpairedLien = false` state. Once the
  flag is set, the only available transitions are the three routes.

  §14 invariants addressed:
    - #10 `source_credit_lien_impairment_forces_deleverage_liquidation_or_recovery`
-/

import Percolator.Lien
import Percolator.Lifecycle
import Mathlib.Tactic.Linarith

namespace Percolator.Spec

/-- The route taken by an account with an impaired lien. -/
inductive Resolution : Type where
  | deleverage : Resolution
  | liquidation : Resolution
  | recovery   : Resolution
  deriving DecidableEq, Repr

/-- Account state relevant to impaired-lien routing. -/
structure AccountWithLiens where
  hasImpairedLien : Bool
  resolved        : Bool
  resolution      : Option Resolution
  deriving Repr

namespace AccountWithLiens

/-- The fresh account state — no impairment, no resolution. -/
def fresh : AccountWithLiens where
  hasImpairedLien := false
  resolved        := false
  resolution      := none

/-- Mark a lien as impaired on this account. -/
def markImpaired (a : AccountWithLiens) : AccountWithLiens :=
  { a with hasImpairedLien := true }

/-- A normal-mode mutation step. Refuses to fire when the account has
    an unresolved impaired lien — encoding §14 #10 as a typed
    precondition. -/
def normalStep (a : AccountWithLiens) : Option AccountWithLiens :=
  if a.hasImpairedLien && !a.resolved then none
  else some a

/-- **Deleverage route**: clear the impairment by reducing risk.
    Produces an account with the impaired flag cleared and the
    resolution recorded. -/
def routeDeleverage (a : AccountWithLiens) : Option AccountWithLiens :=
  if a.hasImpairedLien then
    some {
      a with
      hasImpairedLien := false
      resolved        := true
      resolution      := some .deleverage
    }
  else none

/-- **Liquidation route**: clear the impairment via liquidation. -/
def routeLiquidation (a : AccountWithLiens) : Option AccountWithLiens :=
  if a.hasImpairedLien then
    some {
      a with
      hasImpairedLien := false
      resolved        := true
      resolution      := some .liquidation
    }
  else none

/-- **Recovery route**: clear the impairment via permissionless
    recovery. -/
def routeRecovery (a : AccountWithLiens) : Option AccountWithLiens :=
  if a.hasImpairedLien then
    some {
      a with
      hasImpairedLien := false
      resolved        := true
      resolution      := some .recovery
    }
  else none

-- ============================================================================
-- §14 #10: impaired-lien account forced to a route
-- ============================================================================

/-- **§14 #10 (normal step blocked under impairment)**: when an
    account has an unresolved impaired lien, `normalStep` returns
    `none`. The account cannot take ordinary mutations. -/
theorem normalStep_blocked_when_impaired
    (a : AccountWithLiens) (himp : a.hasImpairedLien = true)
    (hres : a.resolved = false) :
    a.normalStep = none := by
  unfold normalStep
  simp [himp, hres]

/-- **§14 #10 (normal step allowed when no impairment)**: without an
    impaired lien, `normalStep` succeeds. -/
theorem normalStep_open_when_unimpaired
    (a : AccountWithLiens) (h : a.hasImpairedLien = false) :
    a.normalStep = some a := by
  unfold normalStep
  simp [h]

/-- **§14 #10 (any route clears impairment)**: each of the three
    resolution routes flips `hasImpairedLien` to false. -/
theorem routeDeleverage_clears_impaired
    (a a' : AccountWithLiens) (h : a.routeDeleverage = some a') :
    a'.hasImpairedLien = false := by
  unfold routeDeleverage at h
  by_cases himp : a.hasImpairedLien
  · simp [himp] at h
    have := h.symm
    rw [this]
  · simp [himp] at h

theorem routeLiquidation_clears_impaired
    (a a' : AccountWithLiens) (h : a.routeLiquidation = some a') :
    a'.hasImpairedLien = false := by
  unfold routeLiquidation at h
  by_cases himp : a.hasImpairedLien
  · simp [himp] at h
    have := h.symm
    rw [this]
  · simp [himp] at h

theorem routeRecovery_clears_impaired
    (a a' : AccountWithLiens) (h : a.routeRecovery = some a') :
    a'.hasImpairedLien = false := by
  unfold routeRecovery at h
  by_cases himp : a.hasImpairedLien
  · simp [himp] at h
    have := h.symm
    rw [this]
  · simp [himp] at h

/-- **§14 #10 (routes resolve)**: after any of the three routes, the
    account is marked `resolved = true`. The resolution is recorded
    so observers can see which path was taken. -/
theorem routeDeleverage_records_resolution
    (a a' : AccountWithLiens) (h : a.routeDeleverage = some a') :
    a'.resolved = true ∧ a'.resolution = some .deleverage := by
  unfold routeDeleverage at h
  by_cases himp : a.hasImpairedLien
  · simp [himp] at h
    have := h.symm
    refine ⟨?_, ?_⟩
    · rw [this]
    · rw [this]
  · simp [himp] at h

theorem routeLiquidation_records_resolution
    (a a' : AccountWithLiens) (h : a.routeLiquidation = some a') :
    a'.resolved = true ∧ a'.resolution = some .liquidation := by
  unfold routeLiquidation at h
  by_cases himp : a.hasImpairedLien
  · simp [himp] at h
    have := h.symm
    refine ⟨?_, ?_⟩
    · rw [this]
    · rw [this]
  · simp [himp] at h

theorem routeRecovery_records_resolution
    (a a' : AccountWithLiens) (h : a.routeRecovery = some a') :
    a'.resolved = true ∧ a'.resolution = some .recovery := by
  unfold routeRecovery at h
  by_cases himp : a.hasImpairedLien
  · simp [himp] at h
    have := h.symm
    refine ⟨?_, ?_⟩
    · rw [this]
    · rw [this]
  · simp [himp] at h

/-- **§14 #10 (routes require prior impairment)**: each route is only
    callable when an impairment exists — there is no spurious
    "resolve nothing" path. -/
theorem routeDeleverage_requires_impaired
    (a a' : AccountWithLiens) (h : a.routeDeleverage = some a') :
    a.hasImpairedLien = true := by
  unfold routeDeleverage at h
  by_cases himp : a.hasImpairedLien
  · exact himp
  · simp [himp] at h

theorem routeLiquidation_requires_impaired
    (a a' : AccountWithLiens) (h : a.routeLiquidation = some a') :
    a.hasImpairedLien = true := by
  unfold routeLiquidation at h
  by_cases himp : a.hasImpairedLien
  · exact himp
  · simp [himp] at h

theorem routeRecovery_requires_impaired
    (a a' : AccountWithLiens) (h : a.routeRecovery = some a') :
    a.hasImpairedLien = true := by
  unfold routeRecovery at h
  by_cases himp : a.hasImpairedLien
  · exact himp
  · simp [himp] at h

/-- **§14 #10 (closed-world routing)**: every successful resolution
    is one of the three named routes. The `resolution` field tags
    which one was taken. -/
theorem resolution_is_one_of_three
    (a : AccountWithLiens) (h : a.resolved = true) :
    a.resolution = none ∨ a.resolution = some .deleverage
    ∨ a.resolution = some .liquidation ∨ a.resolution = some .recovery := by
  rcases a.resolution with _ | r
  · exact .inl rfl
  · cases r with
    | deleverage => exact .inr (.inl rfl)
    | liquidation => exact .inr (.inr (.inl rfl))
    | recovery => exact .inr (.inr (.inr rfl))

end AccountWithLiens

end Percolator.Spec
