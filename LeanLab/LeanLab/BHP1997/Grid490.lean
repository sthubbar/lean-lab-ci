/-
P0069, page 51. Exact finite grid arithmetic, separated from the analytic bridge.
The existing definitions and shifted row theorem retain their exact text.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Lean.Elab.Tactic.Omega

namespace LeanLab.BHP1997.DecompC165d
open Classical

/-- Page 51. Integer numerators of the 4096-cell E2 grid, denominator 409600000. -/
def lowerTwoGridPoint (i : ℕ) : ℕ := 51195904 + 37501*i
/-- Page 51. Sufficient whole-cell tests for D and the two repaired Q regions. -/
def lowerTwoGridDQ (a A b B : ℕ) : Bool := decide (
  150000000*(A+2*B) ≤ 84373897*409600000 ∨
  (100000000*(4*A+7*B) ≤ 212497999*409600000 ∧
    150004807*409600000 ≤ 400000000*(a+b)) ∨
  (1100000000*B ≤ 249927989*409600000 ∧
    100000000*(4*A+5*B) ≤ 212497999*409600000 ∧
    105001763*409600000 ≤ 240000000*(a+b)))
/-- Page 48. Sufficient whole-cell tests for R, P1 and P2 on the E2 grid. -/
def lowerTwoGridRP (a A b B : ℕ) : Bool := decide (
  B ≤ a ∧ 2*A ≤ 409600000 ∧ 1100000000*B ≤ 249927989*409600000 ∧
    ((100000000*(2*B) ≤ 100000000*a+12497999*409600000 ∧
        1100000000*A ≤ 249927989*409600000) ∨
      (187502001*409600000 ≤ 100000000*(4*a+3*b) ∧
        100000000*(4*A+3*B) ≤ 212497999*409600000) ∨
      (187502001*409600000 ≤ 100000000*(4*a+b) ∧
        100000000*(4*A+B) ≤ 212497999*409600000)))
/-- Page 51. Upward integer division of a rational tangent cell envelope, scale 10000. -/
def lowerTwoTangentWeight (p cap a b : ℕ) : ℕ :=
  let r := 409600000-a-b
  let num := 10000000*r-(10000000-p*cap)*b
  (10000*409600000^3*num + p*1000000*r*a*b*b-1)/(p*1000000*r*a*b*b)
/-- Page 51. Integer ceiling of the three basic Buchstab envelopes. -/
def lowerTwoBaseWeight (a A b B : ℕ) : ℕ :=
  let d := a*b*b
  let ceil := fun n den : ℕ => (n+den-1)/den
  if A+B < 409600000 then
    min (ceil (10000*409600000^3) d)
      (max (ceil (10000*567144*409600000^3) (1000000*d))
        (ceil (10000*B*409600000^3) ((409600000-A-B)*d)))
  else ceil (10000*409600000^3) d
/-- Page 51. Whole-cell integer majorant for the E2 Buchstab integrand, scale 10000. -/
def lowerTwoGridWeight (i j : ℕ) : ℕ :=
  let a := lowerTwoGridPoint i
  let b := lowerTwoGridPoint j
  let A := a+37501
  let B := b+37501
  if A < b ∨ 409600000 < a+2*b then 0
  else if lowerTwoGridDQ a A b B || lowerTwoGridRP a A b B then 0
  else
    let base := lowerTwoBaseWeight a A b B
    if 3*B ≤ 409600000-A then
      min base (min (lowerTwoTangentWeight 10 0 a b)
        (min (lowerTwoTangentWeight 11 95311 a b)
        (min (lowerTwoTangentWeight 12 182322 a b)
        (min (lowerTwoTangentWeight 13 262365 a b)
        (min (lowerTwoTangentWeight 14 336473 a b)
        (min (lowerTwoTangentWeight 15 405466 a b)
          (lowerTwoTangentWeight 16 470004 a b)))))))
    else base

/-- Page 51. The full integer E2 cell sum. Its scale is 10000. -/
def lowerTwoGridTotal : ℕ :=
  ∑ i ∈ Finset.range 4096, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight i j

/-- Page 51. Eight-row blocks of the exact E2 integer sum. -/
def lowerTwoGridBlock (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range 8, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (8*k+i) j

/-- Page 51. Peel one row of a shifted finite grid block. -/
theorem lowerTwo_shifted_row_peel (s n : ℕ) :
    (∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (s+i) j) =
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (s+i) j)
        + (∑ j ∈ Finset.range 4096, lowerTwoGridWeight (s+n) j) := by
  rw [Finset.sum_range_succ]

/-- Page 51. A grid cell outside the support or covered by a deleted region has zero weight.
Auxiliary finite bookkeeping for the existing whole-cell certificate. -/
theorem lowerTwo_grid_zero_of_cover (i j : ℕ)
 (h : lowerTwoGridPoint i+37501 < lowerTwoGridPoint j ∨
 409600000 < lowerTwoGridPoint i+2*lowerTwoGridPoint j ∨
 lowerTwoGridDQ (lowerTwoGridPoint i) (lowerTwoGridPoint i+37501)
   (lowerTwoGridPoint j) (lowerTwoGridPoint j+37501) = true ∨
 lowerTwoGridRP (lowerTwoGridPoint i) (lowerTwoGridPoint i+37501)
   (lowerTwoGridPoint j) (lowerTwoGridPoint j+37501) = true) : lowerTwoGridWeight i j = 0 := by
 unfold lowerTwoGridWeight
 rcases h with h | h | h | h
 · rw [ite_eq_left (Or.inl h)]
 · rw [ite_eq_left (Or.inr h)]
 · by_cases ho : lowerTwoGridPoint i+37501 < lowerTwoGridPoint j ∨ 409600000 < lowerTwoGridPoint i+2*lowerTwoGridPoint j
   · exact ite_eq_left ho
   · rw [ite_eq_right ho]
     exact ite_eq_left (Bool.or_eq_true_iff.mpr (Or.inl h))
 · by_cases ho : lowerTwoGridPoint i+37501 < lowerTwoGridPoint j ∨ 409600000 < lowerTwoGridPoint i+2*lowerTwoGridPoint j
   · exact ite_eq_left ho
   · rw [ite_eq_right ho]
     exact ite_eq_left (Bool.or_eq_true_iff.mpr (Or.inr h))

end LeanLab.BHP1997.DecompC165d
