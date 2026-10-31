import Mathlib
import LeanLab.KadiriLumley2014.Decomp92

namespace LeanLab.KadiriLumley2014.Task336

open Real
open Set
open LeanLab.KadiriLumley2014.Task64
open LeanLab.KadiriLumley2014.Task92

-- We decompose smoothed_explicit_lower

/-- LEAF. Page 4 Lemma 2.2 and equations 2.16 to 2.19.
For m ≥ 2, positive delta and u at most 0.0001 and X ≥ exp 38, the absolute zero summand is summable.
The explicit formula cites Ramare and Saouter 2003 Lemma 4. -/
theorem lemma2_2_summable {m : ℕ} (hm : 2 ≤ m) {δ u X : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) :
    Summable (zeroSummand m δ u X) := by sorry

/-- LEAF. Page 4 Lemma 2.2 and equations 2.16 to 2.19.
For m ≥ 2, positive delta and u at most 0.0001 and X ≥ exp 38, J is at least exp u minus 1 times X times F0 minus Sigma, minus u divided by twice X.
The explicit formula cites Ramare and Saouter 2003 Lemma 4. -/
theorem lemma2_2_inequality {m : ℕ} (hm : 2 ≤ m) {δ u X : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) :
    (Real.exp u - 1) * X * (1 + δ / 2 - zeroError m δ u X) - u / (2 * X) ≤
      psiAverage m δ u X := by sorry

/-- Assembly of smoothed_explicit_lower from the above leaves. -/
theorem smoothed_explicit_lower_assembly {m : ℕ} (hm : 2 ≤ m) {δ u X : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) :
    Summable (zeroSummand m δ u X) ∧
      (Real.exp u - 1) * X * (1 + δ / 2 - zeroError m δ u X) - u / (2 * X) ≤
        psiAverage m δ u X :=
  ⟨lemma2_2_summable hm hδ hδ1 hu hu1 hX, lemma2_2_inequality hm hδ hδ1 hu hu1 hX⟩

end LeanLab.KadiriLumley2014.Task336
