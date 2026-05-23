/-
  Percolator.Defs — Constants mirrored from `src/lib.rs`.

  Each definition here matches the literal expression of the corresponding
  `pub const` in `src/lib.rs`. Lean theorems refer to these by name so that
  any drift between Rust constants and Lean definitions surfaces at proof
  time rather than as a stale literal.

  Numeric values are written as `10^k` rather than `1_000_000_000`
  (Lean 4 v4.15.0 doesn't parse `_` separators in numeric literals).
-/

namespace Percolator.Spec

-- ============================================================================
-- Fixed-point denominators (mirror `lib.rs`)
-- ============================================================================

/-- Position-scale denominator. `lib.rs::POS_SCALE = 1e6`. -/
def POS_SCALE : Nat := 10^6

/-- ADL one-unit. `lib.rs::ADL_ONE = 1e15`. -/
def ADL_ONE : Nat := 10^15

/-- Minimum side-A unit. `lib.rs::MIN_A_SIDE = 1e14`. -/
def MIN_A_SIDE : Nat := 10^14

/-- Maximum oracle price (u64). `lib.rs::MAX_ORACLE_PRICE = 1e12`. -/
def MAX_ORACLE_PRICE : Nat := 10^12

/-- Funding denominator. `lib.rs::FUNDING_DEN = 1e9`. -/
def FUNDING_DEN : Nat := 10^9

/-- Stress consumption scale (currently unused in `v16.rs`).
    `lib.rs::STRESS_CONSUMPTION_SCALE = 1e9`. -/
def STRESS_CONSUMPTION_SCALE : Nat := 10^9

/-- Social weight scale = ADL_ONE. `lib.rs::SOCIAL_WEIGHT_SCALE`. -/
def SOCIAL_WEIGHT_SCALE : Nat := ADL_ONE

/-- Social loss denominator. `lib.rs::SOCIAL_LOSS_DEN = 1e21`. -/
def SOCIAL_LOSS_DEN : Nat := 10^21

/-- Support weight scale (currently unreferenced in `v16.rs` despite 5
    references in `spec.md`, including the arithmetic formula at
    `spec.md:1053`). See LEARNINGS for the intent-drift discussion.
    `lib.rs::SUPPORT_WEIGHT_SCALE = 1e6`. -/
def SUPPORT_WEIGHT_SCALE : Nat := 10^6

/-- Full support weight (= 1.0 in `SUPPORT_WEIGHT_SCALE` units).
    `lib.rs::FULL_SUPPORT_WEIGHT = SUPPORT_WEIGHT_SCALE`. -/
def FULL_SUPPORT_WEIGHT : Nat := SUPPORT_WEIGHT_SCALE

/-- Bound scale. `lib.rs::BOUND_SCALE = 1e12`. -/
def BOUND_SCALE : Nat := 10^12

/-- Credit-rate scale. `lib.rs::CREDIT_RATE_SCALE = 1e12`. -/
def CREDIT_RATE_SCALE : Nat := 10^12

-- ============================================================================
-- Magnitude caps
-- ============================================================================

/-- `lib.rs::MAX_VAULT_TVL = 1e16`. -/
def MAX_VAULT_TVL : Nat := 10^16

/-- `lib.rs::MAX_POSITION_ABS_Q = 1e14`. -/
def MAX_POSITION_ABS_Q : Nat := 10^14

/-- `lib.rs::MAX_ACCOUNT_NOTIONAL = 1e20`. -/
def MAX_ACCOUNT_NOTIONAL : Nat := 10^20

/-- `lib.rs::MAX_TRADE_SIZE_Q = MAX_POSITION_ABS_Q`. -/
def MAX_TRADE_SIZE_Q : Nat := MAX_POSITION_ABS_Q

/-- `lib.rs::MAX_OI_SIDE_Q = 1e14`. -/
def MAX_OI_SIDE_Q : Nat := 10^14

-- ============================================================================
-- BPS caps (consumer-program-facing; not referenced inside `v16.rs`)
-- ============================================================================

/-- `lib.rs::MAX_TRADING_FEE_BPS = 10000`. -/
def MAX_TRADING_FEE_BPS : Nat := 10000

/-- `lib.rs::MAX_MARGIN_BPS = 10000`. -/
def MAX_MARGIN_BPS : Nat := 10000

/-- `lib.rs::MAX_LIQUIDATION_FEE_BPS = 10000`. -/
def MAX_LIQUIDATION_FEE_BPS : Nat := 10000

/-- `lib.rs::MAX_RESOLVE_PRICE_DEVIATION_BPS = 10000`. -/
def MAX_RESOLVE_PRICE_DEVIATION_BPS : Nat := 10000

/-- `lib.rs::MAX_RECOVERY_FALLBACK_DEVIATION_BPS = MAX_RESOLVE_PRICE_DEVIATION_BPS`. -/
def MAX_RECOVERY_FALLBACK_DEVIATION_BPS : Nat := MAX_RESOLVE_PRICE_DEVIATION_BPS

/-- `lib.rs::MAX_PROTOCOL_FEE_ABS = 1e36`. -/
def MAX_PROTOCOL_FEE_ABS : Nat := 10^36

/-- `lib.rs::MAX_WARMUP_SLOTS = u64::MAX = 2^64 - 1`. -/
def MAX_WARMUP_SLOTS : Nat := 2^64 - 1

end Percolator.Spec
