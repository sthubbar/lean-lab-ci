/-
Saouter 1998, Theorem 2, page 864. Mathlib-free certificate data.
AI wrote this Lean code for CODEX task73. Soundness is in PrefixSound.lean.
-/
import LeanLab.Saouter1998.ChainDef

namespace LeanLab.Saouter1998.PrefixCore

open LeanLab.Saouter1998.Core

/-- The candidate prime represented by its odd cofactor. -/
def candidate (R : Nat) : Nat := 2 ^ 22 * R + 1

/-- Theorem 2 with an integer witness between consecutive squares. -/
def test (R k : Nat) : Bool :=
  let N := candidate R
  let s := R / (2 * 2 ^ 22)
  let r := R % (2 * 2 ^ 22)
  (R % 2 == 1) && decide (N < 2 * (2 ^ 22) ^ 3) &&
    (pm (N.log2 + 1) 5 (R * 2 ^ 21) N == N - 1) &&
    (s == 0 || decide (r * r < 8 * s) ||
      (decide (8 * s + k * k < r * r) && decide (r * r < 8 * s + (k + 1) * (k + 1))))

/-- The candidate primes in a list of certificates. -/
def primes (W : List (Nat × Nat)) : List Nat := W.map (fun x => candidate x.1)

/-- The candidates form a ladder from a to last with gaps at most B minus 4. -/
def check (B a last : Nat) (W : List (Nat × Nat)) : Bool :=
  chainC B a (primes W) && ((primes W).getLast? == some last) && decide (a < last)

end LeanLab.Saouter1998.PrefixCore
