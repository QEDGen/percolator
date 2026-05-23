#![allow(dead_code)] // reference port mirrors every Lean def; not all are exercised by proptests yet

//! State-machine refinement: `Percolator/ValueFlow.lean` +
//! `Percolator/ValueFlowSoundness.lean` ↔ Rust.
//!
//! Tier 2 of the verification stack, seventh cluster bridge.
//!
//! Covers token-value flow shapes: TokenValueClass enumeration,
//! TokenValueRow (one debit / one credit / one amount), and
//! TokenValueFlow (a balanced list of rows + external quote
//! tracking + vault snapshots). Plus the named flow constructors
//! lien_create / internal_transfer / insurance_to_close_spent /
//! recovery_insurance_payout.
//!
//! Theorems verified at runtime:
//!
//!   - §14 #2 (`total_debit_eq_total_credit`): every flow is
//!     balanced — total debit equals total credit by construction.
//!   - §14 #4 (`lienCreateFlow_no_value`): lien creation produces
//!     a structurally-empty flow with no rows and no value.
//!   - §14 #25 (`internalTransferFlow_balanced`): internal
//!     transfers are balanced and have no external quote movement
//!     and no vault delta.
//!   - §14 #26 (`creditFor_own_class` / `creditFor_other_class`):
//!     a row contributes `amount` to its own credit class and 0
//!     to every other class.
//!   - §14 #27 (`recoveryInsurancePayoutFlow_*`): the payout
//!     decrements the vault by exactly the payout amount; debits
//!     InsuranceCapital, credits ExternalQuote.
//!
//! See `formal_verification/Percolator/ValueFlow.lean` and
//! `Percolator/ValueFlowSoundness.lean`.

use proptest::prelude::*;

// ============================================================================
// Reference port
// ============================================================================

/// Token-value class. Lean `TokenValueClass`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TokenValueClass {
    TokenVault,
    SeniorCapital,
    InsuranceCapital,
    AccountCapital,
    CloseSupportConsumed,
    CloseInsuranceSpent,
    CloseCounterpartyCreditConsumed,
    BResidualBooked,
    PendingObligationEscrow,
    PendingObligationCredit,
    ExplicitBackedLoss,
    SettlementRoundingResidue,
    CancelDepositEscrow,
    ResolvedPayoutPaid,
    ProtocolFeePaid,
    ExternalQuote,
    UnallocatedProtocolSurplus,
}

/// One row of a token-value flow. Lean `TokenValueRow`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TokenValueRow {
    debit_class: TokenValueClass,
    credit_class: TokenValueClass,
    amount: u128,
}

impl TokenValueRow {
    /// Lean `debitFor`.
    fn debit_for(&self, cls: TokenValueClass) -> u128 {
        if self.debit_class == cls { self.amount } else { 0 }
    }

    /// Lean `creditFor`.
    fn credit_for(&self, cls: TokenValueClass) -> u128 {
        if self.credit_class == cls { self.amount } else { 0 }
    }
}

/// A balanced token-value flow. Lean `TokenValueFlow`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct TokenValueFlow {
    rows: Vec<TokenValueRow>,
    external_quote_in: u128,
    external_quote_out: u128,
    vault_before: u128,
    vault_after: u128,
}

impl TokenValueFlow {
    /// Lean `empty`.
    fn empty(vault_before: u128, vault_after: u128) -> Self {
        Self {
            rows: Vec::new(),
            external_quote_in: 0,
            external_quote_out: 0,
            vault_before,
            vault_after,
        }
    }

    /// Total debit volume — sum of every row's amount. Lean
    /// `totalDebit`.
    fn total_debit(&self) -> u128 {
        self.rows.iter().map(|r| r.amount).sum()
    }

    /// Total credit volume — defined identically to total_debit.
    /// Lean `totalCredit`.
    fn total_credit(&self) -> u128 {
        self.rows.iter().map(|r| r.amount).sum()
    }

    /// Per-class debit total. Lean `debitByClass`.
    fn debit_by_class(&self, cls: TokenValueClass) -> u128 {
        self.rows.iter().map(|r| r.debit_for(cls)).sum()
    }

    /// Per-class credit total. Lean `creditByClass`.
    fn credit_by_class(&self, cls: TokenValueClass) -> u128 {
        self.rows.iter().map(|r| r.credit_for(cls)).sum()
    }

    /// Append a (debit, credit, amount) row. Lean `addRow`.
    fn add_row(
        mut self,
        debit: TokenValueClass,
        credit: TokenValueClass,
        amount: u128,
    ) -> Self {
        self.rows.push(TokenValueRow {
            debit_class: debit,
            credit_class: credit,
            amount,
        });
        self
    }
}

// ============================================================================
// Named flow constructors (mirror Lean ValueFlowSoundness.lean)
// ============================================================================

/// Lien creation: empty flow, no value moved. Lean `lienCreateFlow`.
fn lien_create_flow(vault: u128) -> TokenValueFlow {
    TokenValueFlow::empty(vault, vault)
}

/// Internal transfer: one row debit_class → credit_class, no
/// external quote movement, no vault change. Lean
/// `internalTransferFlow`.
fn internal_transfer_flow(
    debit_cls: TokenValueClass,
    credit_cls: TokenValueClass,
    amount: u128,
    vault: u128,
) -> TokenValueFlow {
    TokenValueFlow::empty(vault, vault).add_row(debit_cls, credit_cls, amount)
}

/// Insurance → CloseInsuranceSpent transfer. Lean
/// `insuranceToCloseSpentFlow`.
fn insurance_to_close_spent_flow(amount: u128, vault: u128) -> TokenValueFlow {
    internal_transfer_flow(
        TokenValueClass::InsuranceCapital,
        TokenValueClass::CloseInsuranceSpent,
        amount,
        vault,
    )
}

/// Recovery insurance payout: debit InsuranceCapital, credit
/// ExternalQuote. Vault decreases by amount. Lean
/// `recoveryInsurancePayoutFlow`. Returns None if amount exceeds
/// vault (the Lean precondition).
fn recovery_insurance_payout_flow(amount: u128, vault_before: u128) -> Option<TokenValueFlow> {
    if amount > vault_before {
        return None;
    }
    Some(TokenValueFlow {
        rows: vec![TokenValueRow {
            debit_class: TokenValueClass::InsuranceCapital,
            credit_class: TokenValueClass::ExternalQuote,
            amount,
        }],
        external_quote_in: 0,
        external_quote_out: amount,
        vault_before,
        vault_after: vault_before - amount,
    })
}

// ============================================================================
// Generators
// ============================================================================

fn arb_token_value_class() -> impl Strategy<Value = TokenValueClass> {
    prop_oneof![
        Just(TokenValueClass::TokenVault),
        Just(TokenValueClass::SeniorCapital),
        Just(TokenValueClass::InsuranceCapital),
        Just(TokenValueClass::AccountCapital),
        Just(TokenValueClass::CloseSupportConsumed),
        Just(TokenValueClass::CloseInsuranceSpent),
        Just(TokenValueClass::CloseCounterpartyCreditConsumed),
        Just(TokenValueClass::BResidualBooked),
        Just(TokenValueClass::PendingObligationEscrow),
        Just(TokenValueClass::PendingObligationCredit),
        Just(TokenValueClass::ExplicitBackedLoss),
        Just(TokenValueClass::SettlementRoundingResidue),
        Just(TokenValueClass::CancelDepositEscrow),
        Just(TokenValueClass::ResolvedPayoutPaid),
        Just(TokenValueClass::ProtocolFeePaid),
        Just(TokenValueClass::ExternalQuote),
        Just(TokenValueClass::UnallocatedProtocolSurplus),
    ]
}

fn arb_row() -> impl Strategy<Value = TokenValueRow> {
    (arb_token_value_class(), arb_token_value_class(), 0u128..=1_000_000u128).prop_map(
        |(d, c, a)| TokenValueRow {
            debit_class: d,
            credit_class: c,
            amount: a,
        },
    )
}

fn arb_flow() -> impl Strategy<Value = TokenValueFlow> {
    (
        prop::collection::vec(arb_row(), 0..=10),
        0u128..=1_000u128,
        0u128..=1_000u128,
        0u128..=1_000_000u128,
        0u128..=1_000_000u128,
    )
        .prop_map(|(rows, eqi, eqo, vb, va)| TokenValueFlow {
            rows,
            external_quote_in: eqi,
            external_quote_out: eqo,
            vault_before: vb,
            vault_after: va,
        })
}

// ============================================================================
// Proptests
// ============================================================================

proptest! {
    /// **§14 #2 `total_debit_eq_total_credit`**: every flow is
    /// balanced by construction — total_debit equals total_credit.
    #[test]
    fn flow_balanced(f in arb_flow()) {
        prop_assert_eq!(f.total_debit(), f.total_credit());
    }

    /// **§14 #4 `lienCreateFlow_no_value`**: lien creation produces
    /// an empty flow with no rows.
    #[test]
    fn lien_create_flow_no_value(vault in 0u128..=1_000_000u128) {
        let f = lien_create_flow(vault);
        prop_assert_eq!(f.total_debit(), 0);
        prop_assert_eq!(f.total_credit(), 0);
        prop_assert!(f.rows.is_empty());
    }

    /// **§14 #4 (corollary)**: lien creation does not change vault.
    #[test]
    fn lien_create_flow_vault_unchanged(vault in 0u128..=1_000_000u128) {
        let f = lien_create_flow(vault);
        prop_assert_eq!(f.vault_before, f.vault_after);
    }

    /// **§14 #25 `internalTransferFlow_balanced`**: internal
    /// transfers are balanced and have no external quote movement
    /// and no vault delta.
    #[test]
    fn internal_transfer_flow_balanced(
        d in arb_token_value_class(),
        c in arb_token_value_class(),
        amount in 0u128..=1_000_000u128,
        vault in 0u128..=1_000_000u128,
    ) {
        let f = internal_transfer_flow(d, c, amount, vault);
        prop_assert_eq!(f.total_debit(), f.total_credit());
        prop_assert_eq!(f.external_quote_in, 0);
        prop_assert_eq!(f.external_quote_out, 0);
        prop_assert_eq!(f.vault_before, f.vault_after);
    }

    /// **§14 #25 (specialized)**: insurance-to-close-spent.
    #[test]
    fn insurance_to_close_spent_balanced(
        amount in 0u128..=1_000_000u128,
        vault in 0u128..=1_000_000u128,
    ) {
        let f = insurance_to_close_spent_flow(amount, vault);
        prop_assert_eq!(f.total_debit(), f.total_credit());
        prop_assert_eq!(f.external_quote_in, 0);
        prop_assert_eq!(f.external_quote_out, 0);
        prop_assert_eq!(f.vault_before, f.vault_after);
    }

    /// **§14 #26 `creditFor_own_class`**: a row contributes `amount`
    /// to its own credit class.
    #[test]
    fn row_credit_for_own_class(r in arb_row()) {
        prop_assert_eq!(r.credit_for(r.credit_class), r.amount);
    }

    /// **§14 #26 `creditFor_other_class`**: a row contributes 0 to
    /// every class other than its credit class.
    #[test]
    fn row_credit_for_other_class(r in arb_row(), other in arb_token_value_class()) {
        if other != r.credit_class {
            prop_assert_eq!(r.credit_for(other), 0);
        }
    }

    /// **§14 #26 `debitFor_own_class`**.
    #[test]
    fn row_debit_for_own_class(r in arb_row()) {
        prop_assert_eq!(r.debit_for(r.debit_class), r.amount);
    }

    /// **§14 #26 `debitFor_other_class`**.
    #[test]
    fn row_debit_for_other_class(r in arb_row(), other in arb_token_value_class()) {
        if other != r.debit_class {
            prop_assert_eq!(r.debit_for(other), 0);
        }
    }

    /// **§14 #27 `recoveryInsurancePayoutFlow_vault_decrements`**:
    /// the payout decrements the vault by exactly the payout
    /// amount; external_quote_out equals that amount.
    #[test]
    fn recovery_payout_vault_decrements(
        amount in 0u128..=1_000_000u128,
        vault_before in 0u128..=2_000_000u128,
    ) {
        if let Some(f) = recovery_insurance_payout_flow(amount, vault_before) {
            prop_assert_eq!(f.vault_before, vault_before);
            prop_assert_eq!(f.vault_after, vault_before - amount);
            prop_assert_eq!(f.vault_before - f.vault_after, amount);
            prop_assert_eq!(f.external_quote_out, amount);
            prop_assert_eq!(f.external_quote_in, 0);
        }
    }

    /// **§14 #27 `recoveryInsurancePayoutFlow_shape`**: the payout
    /// has a single row debiting InsuranceCapital and crediting
    /// ExternalQuote.
    #[test]
    fn recovery_payout_shape(
        amount in 0u128..=1_000_000u128,
        vault_before in 0u128..=2_000_000u128,
    ) {
        if let Some(f) = recovery_insurance_payout_flow(amount, vault_before) {
            prop_assert_eq!(f.debit_by_class(TokenValueClass::InsuranceCapital), amount);
            prop_assert_eq!(f.credit_by_class(TokenValueClass::ExternalQuote), amount);
            prop_assert_eq!(f.debit_by_class(TokenValueClass::ExternalQuote), 0);
            prop_assert_eq!(f.credit_by_class(TokenValueClass::InsuranceCapital), 0);
        }
    }

    /// **§14 #27 `recoveryInsurancePayoutFlow_balanced`**: payout
    /// flow's total_debit equals total_credit.
    #[test]
    fn recovery_payout_balanced(
        amount in 0u128..=1_000_000u128,
        vault_before in 0u128..=2_000_000u128,
    ) {
        if let Some(f) = recovery_insurance_payout_flow(amount, vault_before) {
            prop_assert_eq!(f.total_debit(), f.total_credit());
        }
    }

    /// **`addRow_balanced`** (Lean): appending a row to a flow
    /// preserves the total_debit = total_credit invariant. The
    /// stronger statement is that this is true for any flow, but
    /// we verify it explicitly under arbitrary additions.
    #[test]
    fn add_row_balanced(
        f in arb_flow(),
        d in arb_token_value_class(),
        c in arb_token_value_class(),
        amount in 0u128..=1_000u128,
    ) {
        let f_post = f.add_row(d, c, amount);
        prop_assert_eq!(f_post.total_debit(), f_post.total_credit());
    }
}
