import LeanLab.RieselVaughan1983.Lemma1Gamma1
import LeanLab.RieselVaughan1983.Lemma1BandsDeep

open Real Finset Filter Topology

namespace LeanLab.RieselVaughan1983

/-- LEAF. Lemma 1 for 0 < x < 2. -/
theorem lemma1_lt_two_leaf (hg1 : -729 / 10000 < stieltjes1) (hg1' : stieltjes1 < -7 / 100)
    (x : ℝ) (hx0 : 0 < x) (hx2 : x < 2) :
    |lem1E stieltjes1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  exact lemma1_lt_two stieltjes1 hg1 hg1' x hx0 hx2

/-- LEAF. Lemma 1 for 2 <= x < 16. -/
theorem lemma1_2_16_leaf (hg1 : -729 / 10000 < stieltjes1) (hg1' : stieltjes1 < -7 / 100)
    (x : ℝ) (hx2 : 2 ≤ x) (hx16 : x < 16) :
    |lem1E stieltjes1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  exact lemma1_2_16 stieltjes1 (by linarith) hg1' x hx2 hx16

/-- LEAF. Lemma 1 for 16 <= x. -/
theorem lemma1_ge16_leaf (_hg1 : -729 / 10000 < stieltjes1) (_hg1' : stieltjes1 < -7 / 100)
    (x : ℝ) (hx16 : 16 ≤ x) :
    |lem1E stieltjes1 x| < 1641 / 1000 * x ^ (-(1 / 3 : ℝ)) := by
  exact lemma1_ge16_stieltjes1 x hx16

/-- The exact cited statement of Lemma 1 at stieltjes1. -/
theorem lemma1_stieltjes1_decomposed (hg1 : -729 / 10000 < stieltjes1) (hg1' : stieltjes1 < -7 / 100) :
    Lemma1P stieltjes1 := by
  intro x hx0
  by_cases h2 : x < 2
  · exact lemma1_lt_two_leaf hg1 hg1' x hx0 h2
  · push Not at h2
    by_cases h16 : x < 16
    · exact lemma1_2_16_leaf hg1 hg1' x h2 h16
    · push Not at h16
      exact lemma1_ge16_leaf hg1 hg1' x h16

end LeanLab.RieselVaughan1983
