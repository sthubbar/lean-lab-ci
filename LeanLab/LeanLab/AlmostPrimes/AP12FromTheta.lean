import LeanLab.AlmostPrimes.RR12Published
import LeanLab.AlmostPrimes.U1504DudekOdd12

/-!
# The modulus twelve prime count from the published theta input

AI wrote the Lean code. Goldbach is open.
Ramaré and Rumely 1996, Theorems 1 and 2, page 398, Table 1 page 419,
Table 2 page 422, https://doi.org/10.1090/S0025-5718-96-00669-2.
The Abel summation identity is in AP12Theta. The analytic conclusions are
CONDITIONAL on the named theta inputs.
-/

noncomputable section
namespace LeanLab.AlmostPrimes.AP12FromTheta

open Finset Real AP12Theta U1445DudekOdd U1504DudekOdd12

/-- The real count at an integer agrees with the existing primesAP convention. -/
lemma count12_nat (a x : ℕ) : count12 a x = ((primesAP x 12 a).card : ℝ) := by
  unfold count12 primesAP
  rw [Nat.floor_natCast]
  congr 2

/-- AP12Lower 0.21 by partial summation. CONDITIONAL ON the exact printed theta input. -/
theorem ap12Lower_of_theta (h : RR12ThetaLower) : AP12Lower 0.21 := by
  intro a x ha hx
  have hxR : (10 ^ 9 : ℝ) ≤ x := by exact_mod_cast hx
  simpa only [count12_nat] using count12_lower_from_1e9 h a ha hxR

/-- The complete published table rows imply AP12Lower 0.21.
CONDITIONAL ON RR12Published.Published only. -/
theorem ap12Lower_of_published (h : RR12Published.Published) : AP12Lower 0.21 :=
  ap12Lower_of_theta (RR12Published.lower_of_published h)

/-- The odd half of Dudek 2017 above one billion. CONDITIONAL ON RR12ThetaLower only. -/
theorem dudek_odd_from_theta (h : RR12ThetaLower) (N : ℕ) (hO : Odd N)
    (hN : 10 ^ 9 < N) : ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p) :=
  dudek_odd_from_1e9_ap12 (ap12Lower_of_theta h) N hO hN

end LeanLab.AlmostPrimes.AP12FromTheta

#print axioms LeanLab.AlmostPrimes.AP12FromTheta.count12_nat
#print axioms LeanLab.AlmostPrimes.AP12FromTheta.ap12Lower_of_theta
#print axioms LeanLab.AlmostPrimes.AP12FromTheta.dudek_odd_from_theta

#print axioms LeanLab.AlmostPrimes.AP12FromTheta.ap12Lower_of_published
