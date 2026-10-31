/-
Saouter 1998, P0018, unit U-0360, run 20261017T2003Z-30240. The Boolean Lucas certificate
checker in plain Lean core, with no Mathlib import, so each ladder block loads in a second and
uses little memory. Lucas.lean proves these definitions agree with the lab's Mathlib versions
and that `certB c = true` makes `c.1` prime.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/

namespace LeanLab.Saouter1998.Core

/-- Binary modular power with fuel, the same recursion as `LeanLab.Verifications.Pratt.pm`. -/
def pm : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 1
  | fuel + 1, a, e, m =>
    if e = 0 then 1 % m else
      let h := pm fuel a (e / 2) m
      if e % 2 = 1 then h * h % m * a % m else h * h % m

/-- Trial division, the same recursion as `LeanLab.noDivFrom`. -/
def noDiv (n : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, d => if n < d * d then true else if n % d = 0 then false else noDiv n fuel (d + 1)

/-- Boolean primality by trial division. -/
def primeB (n : Nat) : Bool := decide (2 ≤ n) && noDiv n n 2

/-- The product of the listed prime powers. -/
def prodPow : List (Nat × Nat) → Nat
  | [] => 1
  | x :: t => x.1 ^ x.2 * prodPow t

/-- A rung certificate: the prime, a Lucas witness, and `p - 1` as a list of prime powers. -/
abbrev Cert := Nat × Nat × List (Nat × Nat)

/-- Boolean Lucas check of one certificate. -/
def certB : Cert → Bool
  | (p, a, L) =>
    decide (2 ≤ p) && decide (p < 2 ^ 64) && (prodPow L == p - 1) &&
      L.all (fun x => primeB x.1) && (pm 64 a (p - 1) p == 1 % p) &&
      L.all (fun x => pm 64 a ((p - 1) / x.1) p % p != 1 % p)

end LeanLab.Saouter1998.Core
