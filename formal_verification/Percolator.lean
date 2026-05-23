-- Percolator: Formal verification of percolator-v16 risk engine arithmetic.
--
-- Scope (mirrors the falcon512 / hawk512 verification model):
--
--   Lean covers algebraic identities that Kani's BMC can only check at
--   bounded inputs — widening multiplication, U256 mul/div bounds, two's-
--   complement signed-arithmetic edges, and the fixed-point scaling
--   identities that underpin source-domain credit and A/K/F/B settlement
--   (POS_SCALE / BOUND_SCALE / SUPPORT_WEIGHT_SCALE / ADL_ONE).
--
--   Pipeline-level state-machine correctness — lifecycle transitions,
--   multi-handler invariant preservation, account-topology reasoning,
--   wire-format roundtrip — stays in the existing Kani suite
--   (`tests/proofs_v16*.rs`, 219 proofs at v16 HEAD, 57 in the latest
--   completed full-audit sweep at `kani_audit_final.tsv`).
--
--   The two suites are linked by:
--     1. **Refinement**: each operation in `src/wide_math.rs` is mirrored
--        by a Lean def + correctness theorem in `Percolator/WideMath.lean`.
--        Rust kernel = Lean spec, proven at the math level.
--     2. **Kernel-vs-spec proptests** (planned, not in this commit):
--        Rust `tests/proofs_v16_arithmetic.rs` will add proptests that
--        diff the production kernel against a textbook reference impl
--        whose Lean-extracted form is what Lean theorems prove correct.
--
-- This is the math layer. Operationally correct Rust still needs to track
-- it; proptests + Kani harnesses do that linking work.

import Percolator.Defs
import Percolator.UInt128
import Percolator.WideMath
import Percolator.U256
import Percolator.I256
import Percolator.CreditRate
import Percolator.BoundArith
