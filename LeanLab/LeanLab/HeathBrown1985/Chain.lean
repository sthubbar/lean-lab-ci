/-
P0096 Heath-Brown 1985: Theorem 2 from Lemma 1 and the bound 2.5.
The divisor moments 2.2 with t = 2, 3 are proved in DivMoments.lean.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
-/
import LeanLab.HeathBrown1985.Theorem2
import LeanLab.HeathBrown1985.Lemma2
import LeanLab.HeathBrown1985.DivMoments

namespace LeanLab.HeathBrown1985

/-- Theorem 2 rests only on Lemma 1, 2.6 and 2.7, the bound 2.5 and 2.2 with `t = 2, 3`. -/
theorem theorem2_of_lemma1 (h6 : Lemma1_6) (h7 : Lemma1_7) (h5 : Bound2_5)
    (hd2 : DivMoment2) (hd3 : DivMoment3) : Theorem2 :=
  theorem2_of h6 (lemma2_of h7 h5 hd2 hd3)

/-- Lemma 2 from Lemma 1, 2.7, and the bound 2.5 alone. -/
theorem lemma2_of_lemma1 (h7 : Lemma1_7) (h5 : Bound2_5) : Lemma2 :=
  lemma2_of h7 h5 divMoment2 divMoment3

/-- **Theorem 2 from Lemma 1 and the bound 2.5 alone.** -/
theorem theorem2_of_lemma1' (h6 : Lemma1_6) (h7 : Lemma1_7) (h5 : Bound2_5) : Theorem2 :=
  theorem2_of h6 (lemma2_of_lemma1 h7 h5)

end LeanLab.HeathBrown1985
