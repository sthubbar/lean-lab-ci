/- AI wrote this Lean code for CODEX task700. Goldbach is open.
A core checker for the finite calculation in Buthe 2014 display 4.6.
The witness data are untrusted. Every square divisor used is checked.
https://arxiv.org/abs/1410.7561v2 -/
import Lean
namespace LeanLab.BS2022GRH.Witness700

/-- Recognize a checked square divisor. -/
def excludes (n d : Nat) : Bool := decide (2 ≤ d ∧ n % (d*d) = 0)

/-- The existing rational upper squarefree budget. -/
def good (m q : Nat) : Bool :=
  decide (10000*q ≤ 6079*m) || decide ((10000*q-6079*m)^2 ≤ 46240000*m)

/-- Verify a trace of indices, square divisors and running upper counts. -/
def verify : List (Nat × Nat × Nat) → Nat → Nat → Nat → Nat → Bool
  | [], n, q, N, Q => decide (n=N ∧ q=Q)
  | (m,d,c)::rest, n, q, N, Q =>
    decide (m=n+1) && decide (c=q+(if excludes m d then 0 else 1)) &&
      good m c && verify rest m c N Q

end LeanLab.BS2022GRH.Witness700
