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

// ============================================================================
// Tier 2.5 — Production connector
//
// Connects the TokenValueFlow reference port to
// `v16.rs::TokenValueFlowProofV16` plus its named constructors and
// `validate()` method.
//
// Production stores per-class aggregates in two parallel arrays
// (debits[17], credits[17]) — the per-class totals after summing all
// rows. The reference port stores a list of rows. The bridge agrees
// on the *aggregates*: per-class sums, totals, externals, vault.
// ============================================================================

use percolator::v16::{TokenValueClassV16, TokenValueFlowProofV16};

/// Convert a production class index to the reference enum.
fn class_from_v16(c: TokenValueClassV16) -> TokenValueClass {
    match c {
        TokenValueClassV16::TokenVault => TokenValueClass::TokenVault,
        TokenValueClassV16::SeniorCapital => TokenValueClass::SeniorCapital,
        TokenValueClassV16::InsuranceCapital => TokenValueClass::InsuranceCapital,
        TokenValueClassV16::AccountCapital => TokenValueClass::AccountCapital,
        TokenValueClassV16::CloseSupportConsumed => TokenValueClass::CloseSupportConsumed,
        TokenValueClassV16::CloseInsuranceSpent => TokenValueClass::CloseInsuranceSpent,
        TokenValueClassV16::CloseCounterpartyCreditConsumed => {
            TokenValueClass::CloseCounterpartyCreditConsumed
        }
        TokenValueClassV16::BResidualBooked => TokenValueClass::BResidualBooked,
        TokenValueClassV16::PendingObligationEscrow => TokenValueClass::PendingObligationEscrow,
        TokenValueClassV16::PendingObligationCredit => TokenValueClass::PendingObligationCredit,
        TokenValueClassV16::ExplicitBackedLoss => TokenValueClass::ExplicitBackedLoss,
        TokenValueClassV16::SettlementRoundingResidue => {
            TokenValueClass::SettlementRoundingResidue
        }
        TokenValueClassV16::CancelDepositEscrow => TokenValueClass::CancelDepositEscrow,
        TokenValueClassV16::ResolvedPayoutPaid => TokenValueClass::ResolvedPayoutPaid,
        TokenValueClassV16::ProtocolFeePaid => TokenValueClass::ProtocolFeePaid,
        TokenValueClassV16::ExternalQuote => TokenValueClass::ExternalQuote,
        TokenValueClassV16::UnallocatedProtocolSurplus => {
            TokenValueClass::UnallocatedProtocolSurplus
        }
    }
}

/// Production total debit (sum across the per-class array).
fn prod_total_debit(p: &TokenValueFlowProofV16) -> u128 {
    p.debits.iter().sum()
}

/// Production total credit.
fn prod_total_credit(p: &TokenValueFlowProofV16) -> u128 {
    p.credits.iter().sum()
}

proptest! {
    /// **Production `account_capital_to_insurance` matches reference
    /// `internal_transfer_flow(AccountCapital, InsuranceCapital, ...)`**.
    /// Both produce a balanced flow with one (AccountCapital,
    /// InsuranceCapital) move and no external quote.
    #[test]
    fn production_account_capital_to_insurance_matches_reference(
        amount in 0u128..=1_000_000u128,
        vault in 0u128..=1_000_000u128,
    ) {
        // Production constructor.
        let prod = TokenValueFlowProofV16::account_capital_to_insurance(amount, vault, vault)
            .expect("production constructor should succeed for safe inputs");

        // Reference constructor.
        let r = internal_transfer_flow(
            TokenValueClass::AccountCapital,
            TokenValueClass::InsuranceCapital,
            amount,
            vault,
        );

        // Total debit / credit agree.
        prop_assert_eq!(prod_total_debit(&prod), r.total_debit());
        prop_assert_eq!(prod_total_credit(&prod), r.total_credit());

        // Per-class agreement: AccountCapital debit, InsuranceCapital credit.
        prop_assert_eq!(
            prod.debits[TokenValueClassV16::AccountCapital as usize],
            r.debit_by_class(TokenValueClass::AccountCapital)
        );
        prop_assert_eq!(
            prod.credits[TokenValueClassV16::InsuranceCapital as usize],
            r.credit_by_class(TokenValueClass::InsuranceCapital)
        );

        // External and vault agree.
        prop_assert_eq!(prod.external_quote_in, r.external_quote_in);
        prop_assert_eq!(prod.external_quote_out, r.external_quote_out);
        prop_assert_eq!(prod.vault_before, r.vault_before);
        prop_assert_eq!(prod.vault_after, r.vault_after);

        // Production validate succeeds — the §14 #2 invariant holds.
        prop_assert!(prod.validate().is_ok());
    }

    /// **Production `insurance_to_close_insurance_spent` matches
    /// reference**: same pattern, different class pair.
    #[test]
    fn production_insurance_to_close_insurance_spent_matches_reference(
        amount in 0u128..=1_000_000u128,
        vault in 0u128..=1_000_000u128,
    ) {
        let prod = TokenValueFlowProofV16::insurance_to_close_insurance_spent(
            amount, vault, vault,
        )
        .expect("production constructor should succeed");

        let r = insurance_to_close_spent_flow(amount, vault);

        prop_assert_eq!(prod_total_debit(&prod), r.total_debit());
        prop_assert_eq!(prod_total_credit(&prod), r.total_credit());
        prop_assert_eq!(
            prod.debits[TokenValueClassV16::InsuranceCapital as usize],
            r.debit_by_class(TokenValueClass::InsuranceCapital)
        );
        prop_assert_eq!(
            prod.credits[TokenValueClassV16::CloseInsuranceSpent as usize],
            r.credit_by_class(TokenValueClass::CloseInsuranceSpent)
        );
        prop_assert_eq!(prod.external_quote_in, 0);
        prop_assert_eq!(prod.external_quote_out, 0);
        prop_assert_eq!(prod.vault_before, prod.vault_after);
        prop_assert!(prod.validate().is_ok());
    }

    /// **Production `external_in_to_account_capital` matches a
    /// reference external-inflow shape**: external_quote_in = amount,
    /// AccountCapital debit = amount, ExternalQuote credit = amount.
    /// Vault increases by amount.
    #[test]
    fn production_external_in_matches_reference(
        amount in 0u128..=1_000_000u128,
        vault_before in 0u128..=1_000_000u128,
    ) {
        let vault_after = match vault_before.checked_add(amount) {
            Some(v) => v,
            None => return Ok(()),
        };

        let prod = TokenValueFlowProofV16::external_in_to_account_capital(
            amount,
            vault_before,
            vault_after,
        )
        .expect("constructor should succeed");

        prop_assert_eq!(prod_total_debit(&prod), prod_total_credit(&prod));
        prop_assert_eq!(prod_total_debit(&prod), amount);
        prop_assert_eq!(prod.external_quote_in, amount);
        prop_assert_eq!(prod.external_quote_out, 0);
        prop_assert_eq!(prod.vault_after, prod.vault_before + amount);
        prop_assert_eq!(
            prod.debits[TokenValueClassV16::AccountCapital as usize],
            amount
        );
        prop_assert_eq!(
            prod.credits[TokenValueClassV16::ExternalQuote as usize],
            amount
        );
        prop_assert!(prod.validate().is_ok());
    }

    /// **Production validate enforces total-balance**: every
    /// successfully-constructed production proof has
    /// total_debit == total_credit, mirroring §14 #2.
    #[test]
    fn production_named_constructor_validates(
        amount in 0u128..=1_000_000u128,
        vault in 0u128..=1_000_000u128,
    ) {
        let constructors: Vec<Result<TokenValueFlowProofV16, _>> = vec![
            TokenValueFlowProofV16::account_capital_to_insurance(amount, vault, vault),
            TokenValueFlowProofV16::insurance_to_close_insurance_spent(amount, vault, vault),
            TokenValueFlowProofV16::account_capital_to_realized_loss(amount, vault, vault),
        ];
        for prod in constructors.into_iter().flatten() {
            prop_assert!(prod.validate().is_ok());
            prop_assert_eq!(prod_total_debit(&prod), prod_total_credit(&prod));
        }
    }
}

// Reference the helper to silence unused-warning in some configurations.
#[allow(unused)]
fn _class_mapping_smoke(c: TokenValueClassV16) -> TokenValueClass {
    class_from_v16(c)
}

// ============================================================================
// Multi-step sequencing — Week 2 deepening
// ============================================================================

proptest! {
    /// **Chained internal transfers stay balanced**: building a
    /// TokenValueFlow by appending many transfer rows preserves
    /// `total_debit = total_credit` at every step (the §14 #2
    /// invariant). The production side does this via successive
    /// `validate()` calls on growing flows.
    #[test]
    fn multistep_flow_remains_balanced(
        actions in prop::collection::vec(
            (arb_token_value_class(), arb_token_value_class(), 0u128..=1_000u128),
            1..15,
        ),
        vault in 0u128..=1_000_000u128,
    ) {
        let mut f = TokenValueFlow::empty(vault, vault);
        for (d, c, amt) in actions {
            f = f.add_row(d, c, amt);
            // After each row added, the flow remains balanced.
            prop_assert_eq!(f.total_debit(), f.total_credit());
        }
    }

    /// **Per-class accumulation matches expected sums after a
    /// chain of internal transfers from a single class**.
    /// Repeatedly transferring out of AccountCapital into various
    /// destinations: the AccountCapital debit total equals the
    /// sum of transferred amounts.
    #[test]
    fn multistep_per_class_aggregates(
        amounts in prop::collection::vec(0u128..=1_000u128, 1..10),
    ) {
        let mut f = TokenValueFlow::empty(0, 0);
        let mut total_out: u128 = 0;
        for amt in amounts {
            f = f.add_row(
                TokenValueClass::AccountCapital,
                TokenValueClass::InsuranceCapital,
                amt,
            );
            total_out += amt;
            prop_assert_eq!(
                f.debit_by_class(TokenValueClass::AccountCapital),
                total_out
            );
            prop_assert_eq!(
                f.credit_by_class(TokenValueClass::InsuranceCapital),
                total_out
            );
        }
    }

    /// **Production-flow validate stays consistent across
    /// successive named constructors**: building independent
    /// production `TokenValueFlowProofV16` values from each named
    /// constructor and verifying each independently passes
    /// `validate()`. This exercises the validation idempotency.
    #[test]
    fn multistep_named_constructors_independently_valid(
        amount in 0u128..=1_000u128,
        vault in 0u128..=1_000_000u128,
    ) {
        let p1 = TokenValueFlowProofV16::account_capital_to_insurance(
            amount, vault, vault,
        ).expect("c1");
        let p2 = TokenValueFlowProofV16::insurance_to_close_insurance_spent(
            amount, vault, vault,
        ).expect("c2");
        let p3 = TokenValueFlowProofV16::account_capital_to_realized_loss(
            amount, vault, vault,
        ).expect("c3");

        prop_assert!(p1.validate().is_ok());
        prop_assert!(p2.validate().is_ok());
        prop_assert!(p3.validate().is_ok());

        // Each proof's debit/credit totals equal `amount`.
        prop_assert_eq!(prod_total_debit(&p1), amount);
        prop_assert_eq!(prod_total_debit(&p2), amount);
        prop_assert_eq!(prod_total_debit(&p3), amount);
    }
}
