/-
Saouter 1998, P0018, unit U-0360, run 20261017T2003Z-30240. Mathlib-free Boolean check that a
ladder block continues the ladder: its primes rise from `a` with gaps at most `B - 4`, and the
block ends at `last`. One small `decide +kernel` per block, in Chk1 to Chk201.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/
import LeanLab.Saouter1998.CertDef

namespace LeanLab.Saouter1998.Core

/-- The chain check from `a` along `l`. -/
def chainC (B a : Nat) : List Nat → Bool
  | [] => true
  | b :: t => (decide (a < b) && decide (b ≤ a + (B - 4))) && chainC B b t

/-- A block continues the ladder from `a` and ends at `last`. -/
def chk (B a last : Nat) (C : List Cert) : Bool :=
  chainC B a (C.map Prod.fst) && ((C.map Prod.fst).getLast? == some last) && decide (a < last)

end LeanLab.Saouter1998.Core
