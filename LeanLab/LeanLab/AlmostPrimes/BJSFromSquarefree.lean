import LeanLab.AlmostPrimes.U1497DudekAll

/-!
# The even square-free input of BJS Theorem 5

AI wrote the Lean code. Goldbach is open.
Bordignon, Johnston and Starichkova, arXiv 2207.09452, Section 10, page 63,
Theorem 5 and the quoted Dudek Theorem 53. The printed exponent is 29.3.
The corrected Chen threshold 32.73 is the existing lab variant.
The square-free input is proved by the existing split window chain and the
unconditional even analytic theorem. No progression lower bound is used here.
-/

namespace LeanLab.AlmostPrimes.BJSFromSquarefree

open Real DudekLarge Thm5

/-- The finite even square-free input is unconditional, through U1497Split. -/
theorem dudekEvenBelow_split : DudekEvenBelow :=
  fun N hE h4 _ => U1497DudekAll.dudek_even_split N hE h4

/-- The exact exponent 29.3, with the square-free input discharged.
CONDITIONAL ON the corrected Chen representation bound and the two Dusart bounds only. -/
theorem bjs_all_of_chen_dusart
    (hChen3273 : ∀ N : ℕ, Even N → exp (exp 32.73) < N → PrimePlusAlmostPrime 2 N)
    (hD : LeanLab.Common.ThetaWindow.DusartThm52k2) (hP : DusartPi11) :
    ∀ N : ℕ, Even N → 4 ≤ N → ∃ k : ℕ, (k : ℝ) ≤ exp 29.3 ∧ PrimePlusAlmostPrime k N :=
  bjs_thm5_of_3273_small hChen3273 dudekEvenBelow_split hD hP

end LeanLab.AlmostPrimes.BJSFromSquarefree

#print axioms LeanLab.AlmostPrimes.BJSFromSquarefree.dudekEvenBelow_split
#print axioms LeanLab.AlmostPrimes.BJSFromSquarefree.bjs_all_of_chen_dusart
