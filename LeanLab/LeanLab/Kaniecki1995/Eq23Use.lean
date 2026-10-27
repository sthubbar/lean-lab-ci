/-
P0022, Kaniecki 1995: the Section 3 results with inequality (23) discharged by `eq23`.
AI-written Lean code, Claude, 2026-10-18, run 20261018T1903Z-4829, unit U-0967.
Binary Goldbach is OPEN. These remain CONDITIONAL on RH and the cited inputs named.
-/
import LeanLab.Kaniecki1995.Eq23Proof
import LeanLab.Kaniecki1995.Reduction

namespace LeanLab.Kaniecki1995

/-- Interval property, CONDITIONAL ON RH, Lemma 5, Lemma 6, Young-Potler. -/
theorem interval_of' (hRH : RiemannHypothesis) (h5 : Lemma5) (h6 : Lemma6)
    (hYP : YoungPotler) : IntervalProperty := interval_of hRH h5 eq23 h6 hYP

/-- Theorem, odd part, CONDITIONAL ON Lemma 5, Lemma 6, Young-Potler, Sinisalo, Chen-Wang. -/
theorem theoremOdd_of' (h5 : Lemma5) (h6 : Lemma6) (hYP : YoungPotler) (hS : Sinisalo)
    (hCW : ChenWang) : TheoremOdd := theoremOdd_of h5 eq23 h6 hYP hS hCW

/-- Theorem, even part, CONDITIONAL ON Lemma 5, Lemma 6, Young-Potler, Chen-Wang. -/
theorem theoremEven_of' (h5 : Lemma5) (h6 : Lemma6) (hYP : YoungPotler) (hCW : ChenWang) :
    TheoremEven := theoremEven_of h5 eq23 h6 hYP hCW

/-- Remark, CONDITIONAL ON Lemma 5 only. -/
theorem remark_of' (h5 : Lemma5) : RemarkStatement := remark_of h5 eq23

#print axioms eq23
#print axioms measure_A_ge
#print axioms integrand_ge
#print axioms theta_eq_of_no_prime
#print axioms interval_of'
#print axioms theoremOdd_of'
#print axioms theoremEven_of'
#print axioms remark_of'

end LeanLab.Kaniecki1995
