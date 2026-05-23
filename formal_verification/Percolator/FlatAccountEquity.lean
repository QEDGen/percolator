/-
  Percolator.FlatAccountEquity — Phase 3 port of `account_equity` /
  `flat_account_equity`.

  Computes the equity of a portfolio account that holds no leveraged
  positions ("flat" — i.e. before reading any leg PnL): just capital +
  realized PnL minus accumulated fee debt.

  Mirror of `v16.rs::account_equity` (line 9683). The Rust function
  validates `fee_credits ≤ 0` then computes `capital + pnl − |fee_credits|`.
  The Lean port keeps that exact shape but lifts to `Int` so the
  no-overflow precondition stays explicit.

  Pure-function port — no state, no side effects. Builds on the
  `PortfolioAccount` model in `Percolator/State.lean`.
-/

import Percolator.State
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Percolator.Spec

namespace PortfolioAccount

-- ============================================================================
-- fee_debt — the magnitude of (non-positive) fee_credits
-- ============================================================================

/-- Lean spec mirror of `v16.rs::validate_fee_credits` (line 10011) —
    fee credits must be non-positive. Captured as a Lean predicate. -/
def validFeeCredits (a : PortfolioAccount) : Prop := a.feeCredits ≤ 0

/-- Lean spec mirror of `v16.rs::fee_debt_u128` (line 10019).

    Given the precondition `validFeeCredits`, the fee debt equals
    `−fee_credits` (a non-negative `Int`). The Rust version returns a
    `u128` via `.unsigned_abs()`; here we keep the `Int` form so the
    sign relationship to `feeCredits` is transparent. -/
def feeDebt (a : PortfolioAccount) : Int := -a.feeCredits

/-- **`feeDebt` is non-negative** under the validity precondition. -/
theorem feeDebt_nonneg (a : PortfolioAccount) (h : validFeeCredits a) :
    0 ≤ a.feeDebt := by
  unfold feeDebt validFeeCredits at *; linarith

-- ============================================================================
-- account_equity — capital + pnl − fee_debt
-- ============================================================================

/-- Lean spec mirror of `v16.rs::account_equity` (line 9683).

    The flat (leg-free) equity of an account: capital plus realized PnL
    minus accumulated fee debt. -/
def accountEquity (a : PortfolioAccount) : Int :=
  (a.capital : Int) + a.pnl - a.feeDebt

-- ============================================================================
-- Closed-form rewrite
-- ============================================================================

/-- **Closed form**: with `feeDebt = −feeCredits`, the equity reduces to
    `capital + pnl + feeCredits`. -/
theorem accountEquity_eq_capital_plus_pnl_plus_feeCredits
    (a : PortfolioAccount) :
    a.accountEquity = (a.capital : Int) + a.pnl + a.feeCredits := by
  unfold accountEquity feeDebt; linarith

-- ============================================================================
-- Monotonicity / sign properties
-- ============================================================================

/-- **Monotonic in capital**: adding capital strictly increases equity. -/
theorem accountEquity_mono_capital
    (a : PortfolioAccount) (delta : Nat) (hdelta : 0 < delta) :
    a.accountEquity < ({ a with capital := a.capital + delta } : PortfolioAccount).accountEquity := by
  unfold accountEquity feeDebt
  push_cast
  linarith

/-- **Monotonic in pnl**: more PnL ⇒ more equity (weak monotonicity). -/
theorem accountEquity_mono_pnl
    (a : PortfolioAccount) (newPnl : Int) (hle : a.pnl ≤ newPnl) :
    a.accountEquity ≤ ({ a with pnl := newPnl } : PortfolioAccount).accountEquity := by
  unfold accountEquity feeDebt
  linarith

/-- **Monotonic in feeCredits**: less-negative fee credits (smaller fee
    debt) ⇒ more equity. Specifically, if `feeCredits` increases (toward
    zero), equity increases. -/
theorem accountEquity_mono_feeCredits
    (a : PortfolioAccount) (newFee : Int) (hle : a.feeCredits ≤ newFee) :
    a.accountEquity ≤ ({ a with feeCredits := newFee } : PortfolioAccount).accountEquity := by
  unfold accountEquity feeDebt
  linarith

/-- **Sign relationship**: under the validity precondition, equity is
    bounded above by `capital + pnl`. -/
theorem accountEquity_le_capital_plus_pnl
    (a : PortfolioAccount) (h : validFeeCredits a) :
    a.accountEquity ≤ (a.capital : Int) + a.pnl := by
  unfold accountEquity
  have := a.feeDebt_nonneg h
  linarith

/-- **Lower bound at zero fee debt**: when fee credits are exactly zero,
    equity equals `capital + pnl`. -/
theorem accountEquity_no_fee_debt
    (a : PortfolioAccount) (h : a.feeCredits = 0) :
    a.accountEquity = (a.capital : Int) + a.pnl := by
  rw [accountEquity_eq_capital_plus_pnl_plus_feeCredits, h]
  ring

end PortfolioAccount

end Percolator.Spec
