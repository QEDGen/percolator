//! State-machine refinement: `Percolator/InsuranceLedger.lean` ↔ Rust.
//!
//! Tier 2 of the verification stack. The pattern mirrors
//! `proofs_v16_lean_refinement.rs` but at the state-machine level:
//!
//!   - The Lean spec (`InsuranceLedger` + `reserve` / `release` /
//!     `consume` + `applyWrite`) defines the abstract behavior with
//!     a carried conservation invariant.
//!   - The Rust *reference port* below is a line-for-line port of
//!     the Lean definitions. It is **owned by the verification**
//!     (not used by production); it exists so the Lean spec is
//!     runnable in Rust.
//!   - The proptests verify the Lean theorems hold at runtime for
//!     the reference port. They do not yet bridge to v16.rs
//!     production state — that is a follow-up step that requires a
//!     `MarketGroupV16` fixture and an abstraction function
//!     projecting the production `InsuranceCreditReservationV16` to
//!     the abstract `InsuranceLedger`.
//!
//! The theorems verified at runtime:
//!
//!   - `consume_atomic_decrement_and_spend`: a successful consume
//!     decrements `sourceCreditReservedNum` and increments
//!     `domainSpent` by the same amount.
//!   - `applyWrite_preserves_initialDeposited`: no writer mutates
//!     the deposit anchor.
//!   - `conservation`: every reachable state satisfies the
//!     `reserved + staged + protocolStaged + spent ≤ deposited`
//!     invariant. Carried as a struct field on the Lean side; a
//!     runtime check on the Rust side.
//!
//! See `formal_verification/Percolator/InsuranceLedger.lean` for
//! the Lean statements and
//! `formal_verification/Percolator/SingleWriterInsurance.lean` for
//! the closed-sum `applyWrite` typed entry point.

use proptest::prelude::*;

// ============================================================================
// Reference port — Rust copy of `Percolator/InsuranceLedger.lean`
// ============================================================================

/// Insurance ledger, single-domain projection. Mirrors the Lean
/// `InsuranceLedger` structure.
///
/// The Lean structure carries the conservation invariant as a proof
/// field; in Rust we represent it as a runtime check (see
/// `is_conserved`). Construction is via `new` and the three
/// transitions; the conservation property is preserved by
/// construction (verified by the proptests below).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct InsuranceLedger {
    initial_deposited: u128,
    source_credit_reserved_num: u128,
    domain_spent: u128,
    staged_domain_debit: u128,
    global_protocol_staged: u128,
}

impl InsuranceLedger {
    /// The empty ledger — Lean's `InsuranceLedger.empty`.
    const EMPTY: Self = Self {
        initial_deposited: 0,
        source_credit_reserved_num: 0,
        domain_spent: 0,
        staged_domain_debit: 0,
        global_protocol_staged: 0,
    };

    /// Initialize a ledger with `deposit` units of capital. Mirrors
    /// `Percolator/InsuranceLedger.lean::InsuranceLedger.initial`.
    fn initial(deposit: u128) -> Self {
        Self {
            initial_deposited: deposit,
            ..Self::EMPTY
        }
    }

    /// The conservation invariant. Carried as a struct field
    /// (`conservation : ... ≤ initialDeposited`) in Lean; verified
    /// at construction time here.
    fn is_conserved(&self) -> bool {
        self.source_credit_reserved_num
            .checked_add(self.staged_domain_debit)
            .and_then(|x| x.checked_add(self.global_protocol_staged))
            .and_then(|x| x.checked_add(self.domain_spent))
            .map(|sum| sum <= self.initial_deposited)
            .unwrap_or(false)
    }

    /// **Reserve**: add `amount` to source-credit reservation.
    /// Returns `None` if the post-state would violate conservation.
    ///
    /// Mirrors Lean `InsuranceLedger.reserve`.
    fn reserve(&self, amount: u128) -> Option<Self> {
        let new_reserved = self.source_credit_reserved_num.checked_add(amount)?;
        let sum = new_reserved
            .checked_add(self.staged_domain_debit)?
            .checked_add(self.global_protocol_staged)?
            .checked_add(self.domain_spent)?;
        if sum <= self.initial_deposited {
            Some(Self {
                source_credit_reserved_num: new_reserved,
                ..*self
            })
        } else {
            None
        }
    }

    /// **Release**: remove `amount` from source-credit reservation
    /// without spending. Returns `None` if `amount` exceeds the
    /// current reservation.
    ///
    /// Mirrors Lean `InsuranceLedger.release`.
    fn release(&self, amount: u128) -> Option<Self> {
        if self.source_credit_reserved_num < amount {
            None
        } else {
            Some(Self {
                source_credit_reserved_num: self.source_credit_reserved_num - amount,
                ..*self
            })
        }
    }

    /// **Consume**: spend `amount`. Decrements
    /// `source_credit_reserved_num` and increments `domain_spent`
    /// atomically.
    ///
    /// Mirrors Lean `InsuranceLedger.consume`.
    fn consume(&self, amount: u128) -> Option<Self> {
        if self.source_credit_reserved_num < amount {
            return None;
        }
        Some(Self {
            source_credit_reserved_num: self.source_credit_reserved_num - amount,
            domain_spent: self.domain_spent.checked_add(amount)?,
            ..*self
        })
    }
}

/// Closed sum of canonical writers. Mirrors Lean
/// `SingleWriterInsurance.lean::InsuranceWrite`. By exhaustiveness,
/// there is no fourth constructor — every `InsuranceWrite` value
/// is provably one of these three.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InsuranceWrite {
    Reserve(u128),
    Release(u128),
    Consume(u128),
}

impl InsuranceLedger {
    /// The single typed entry point. Routes by `InsuranceWrite`
    /// constructor to the corresponding named transition.
    ///
    /// Mirrors Lean `InsuranceLedger.applyWrite`.
    fn apply_write(&self, w: InsuranceWrite) -> Option<Self> {
        match w {
            InsuranceWrite::Reserve(a) => self.reserve(a),
            InsuranceWrite::Release(a) => self.release(a),
            InsuranceWrite::Consume(a) => self.consume(a),
        }
    }
}

// ============================================================================
// Generators
// ============================================================================

/// Generate a well-conserved random ledger. We start from a deposit
/// and apply a random reservation; this guarantees the post-state
/// satisfies the conservation invariant. Other fields stay zero
/// for simplicity in the first cut.
fn arb_ledger() -> impl Strategy<Value = InsuranceLedger> {
    (1u128..=1_000_000u128, 0u128..=1_000_000u128).prop_filter_map(
        "reservation must not exceed deposit",
        |(deposit, reserved)| {
            if reserved <= deposit {
                Some(InsuranceLedger {
                    initial_deposited: deposit,
                    source_credit_reserved_num: reserved,
                    domain_spent: 0,
                    staged_domain_debit: 0,
                    global_protocol_staged: 0,
                })
            } else {
                None
            }
        },
    )
}

/// Generate a random `InsuranceWrite` action.
fn arb_write() -> impl Strategy<Value = InsuranceWrite> {
    prop_oneof![
        (1u128..=1_000_000u128).prop_map(InsuranceWrite::Reserve),
        (0u128..=1_000_000u128).prop_map(InsuranceWrite::Release),
        (0u128..=1_000_000u128).prop_map(InsuranceWrite::Consume),
    ]
}

// ============================================================================
// Proptests — runtime verification of the Lean theorems
// ============================================================================

proptest! {
    /// **Lean `InsuranceLedger.empty_isReconciledZero` analog**: the
    /// empty ledger satisfies conservation. Sanity check on the
    /// constructor — not a proptest in the random-input sense, but
    /// included for completeness.
    #[test]
    fn empty_is_conserved(_x: u32) {
        prop_assert!(InsuranceLedger::EMPTY.is_conserved());
    }

    /// **Lean `InsuranceLedger.initial` is conserved**: a freshly-
    /// constructed ledger is always conserved.
    #[test]
    fn initial_is_conserved(deposit in 0u128..=u128::MAX) {
        prop_assert!(InsuranceLedger::initial(deposit).is_conserved());
    }

    /// **Conservation under reserve** (Lean
    /// `reserve_preserves_conservation`): every successful reserve
    /// produces a conserved post-state. The Lean theorem is by the
    /// `conservation` proof field; here it's a runtime check.
    #[test]
    fn reserve_preserves_conservation(l in arb_ledger(), amount in 0u128..=2_000_000u128) {
        if let Some(l_post) = l.reserve(amount) {
            prop_assert!(l_post.is_conserved());
        }
    }

    /// **Conservation under release** (Lean
    /// `release_preserves_conservation`). -/
    #[test]
    fn release_preserves_conservation(l in arb_ledger(), amount in 0u128..=2_000_000u128) {
        if let Some(l_post) = l.release(amount) {
            prop_assert!(l_post.is_conserved());
        }
    }

    /// **Conservation under consume** (Lean
    /// `consume_preserves_conservation`).
    #[test]
    fn consume_preserves_conservation(l in arb_ledger(), amount in 0u128..=2_000_000u128) {
        if let Some(l_post) = l.consume(amount) {
            prop_assert!(l_post.is_conserved());
        }
    }

    /// **Atomic decrement-and-spend** (Lean
    /// `consume_atomic_decrement_and_spend`): a successful consume
    /// decrements `source_credit_reserved_num` and increments
    /// `domain_spent` by exactly `amount` in the same step. The
    /// same atom cannot be both reserved and spent.
    #[test]
    fn consume_atomic_decrement_and_spend(l in arb_ledger(), amount in 0u128..=2_000_000u128) {
        if let Some(l_post) = l.consume(amount) {
            prop_assert_eq!(
                l_post.source_credit_reserved_num + amount,
                l.source_credit_reserved_num
            );
            prop_assert_eq!(l_post.domain_spent, l.domain_spent + amount);
        }
    }

    /// **Consume preserves deposit and staged** (Lean
    /// `consume_preserves_deposit_and_staged`): the consume
    /// transition reclassifies reserved → spent against the same
    /// `initial_deposited`; nothing else moves.
    #[test]
    fn consume_preserves_deposit_and_staged(l in arb_ledger(), amount in 0u128..=2_000_000u128) {
        if let Some(l_post) = l.consume(amount) {
            prop_assert_eq!(l_post.initial_deposited, l.initial_deposited);
            prop_assert_eq!(l_post.staged_domain_debit, l.staged_domain_debit);
            prop_assert_eq!(l_post.global_protocol_staged, l.global_protocol_staged);
        }
    }

    /// **Release preserves domain_spent** (Lean
    /// `release_preserves_domainSpent`): release returns reserved
    /// capacity to available without ever moving spend.
    #[test]
    fn release_preserves_domain_spent(l in arb_ledger(), amount in 0u128..=2_000_000u128) {
        if let Some(l_post) = l.release(amount) {
            prop_assert_eq!(l_post.domain_spent, l.domain_spent);
        }
    }

    /// **apply_write_preserves_initialDeposited** (Lean
    /// `applyWrite_preserves_initialDeposited`): no constructor of
    /// `InsuranceWrite` mutates the deposit anchor. Closed-sum
    /// exhaustiveness on the Lean side; per-constructor checks here.
    #[test]
    fn apply_write_preserves_initial_deposited(
        l in arb_ledger(),
        w in arb_write(),
    ) {
        if let Some(l_post) = l.apply_write(w) {
            prop_assert_eq!(l_post.initial_deposited, l.initial_deposited);
        }
    }

    /// **apply_write_preserves_globalProtocolStaged** (Lean
    /// `applyWrite_preserves_globalProtocolStaged`).
    #[test]
    fn apply_write_preserves_global_protocol_staged(
        l in arb_ledger(),
        w in arb_write(),
    ) {
        if let Some(l_post) = l.apply_write(w) {
            prop_assert_eq!(l_post.global_protocol_staged, l.global_protocol_staged);
        }
    }

    /// **apply_write routing equivalence** (Lean
    /// `applyWrite_Reserve` / `_Release` / `_Consume`):
    /// `apply_write(Reserve(a))` is definitionally `reserve(a)`,
    /// and likewise for the other two constructors.
    #[test]
    fn apply_write_routing_equivalence(
        l in arb_ledger(),
        a in 0u128..=1_000_000u128,
    ) {
        prop_assert_eq!(l.apply_write(InsuranceWrite::Reserve(a)), l.reserve(a));
        prop_assert_eq!(l.apply_write(InsuranceWrite::Release(a)), l.release(a));
        prop_assert_eq!(l.apply_write(InsuranceWrite::Consume(a)), l.consume(a));
    }

    /// **Sequences of writes preserve conservation**: a chain of
    /// arbitrary `InsuranceWrite` actions, each one applied if it
    /// succeeds, never breaks conservation. This is the
    /// integration-level claim — composition of the Lean
    /// transitions stays sound.
    #[test]
    fn sequence_of_writes_preserves_conservation(
        l0 in arb_ledger(),
        actions in prop::collection::vec(arb_write(), 0..20),
    ) {
        let mut l = l0;
        prop_assert!(l.is_conserved());
        for w in actions {
            if let Some(l_next) = l.apply_write(w) {
                l = l_next;
                prop_assert!(l.is_conserved());
            }
        }
    }
}
