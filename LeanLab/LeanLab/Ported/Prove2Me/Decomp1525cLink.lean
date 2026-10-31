/-
Lean Lab bridge from the attributed Prove2Me port to Vaughan's first moment.
Source: Vaughan 1977 pages 96 and 103, equations 2.15 and 2.16 and Lemma 11.
https://doi.org/10.1515/crll.1977.290.93
The remaining analytic input is equation 2.15.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Decomp1525c
import LeanLab.Ported.Prove2Me.Decomp1525cAnalytic
import LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals

open LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Inputs

namespace LeanLab.Ported.Prove2Me.Decomp1525cLink

theorem distributionError_of_eq215 (h215 : Eq215) : DistributionError := by
  have h216 := LeanLab.Ported.Prove2Me.Decomp1525cAnalytic.eq216_of_eq215 h215
  exact LeanLab.SchnirelmannBounds.Decomp1525c.distribution_of h215
    (fun x hx => LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Intervals.prime_interval_approximation_integral
      h215 h216 hx)

theorem lemma11_of_eq215 (h215 : Eq215) :
    LeanLab.SchnirelmannBounds.Vaughan1977Lemma12.Lemma11 :=
  LeanLab.SchnirelmannBounds.Vaughan1977Quadrature.lemma11_of_distribution
    (distributionError_of_eq215 h215)

end LeanLab.Ported.Prove2Me.Decomp1525cLink
