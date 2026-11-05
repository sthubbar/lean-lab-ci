import LeanLab.RamareSaouter2003.Decomp359a
import LeanLab.RamareSaouter2003.Decomp359b
import LeanLab.RamareSaouter2003.Decomp359c
import LeanLab.RamareSaouter2003.Decomp359d
import LeanLab.RamareSaouter2003.Decomp359e
import LeanLab.RamareSaouter2003.Decomp359f
import LeanLab.RamareSaouter2003.Decomp359g
import LeanLab.RamareSaouter2003.CountConvergence359

/-!
P0099 pp. 14 to 20. Refreshed assemblies for the task359 source leaves.
Existing files and their sealed statements remain unchanged.
The six new analytic leaves and the original excluded citations stay OPEN.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Assembly359

open Real Chebyshev Smooth Thm4Parts Thm4Literal Thm4Assembly L3Zeta L3Zeros Decomp290c

/-- P0099 pp. 19 and 20, convergence of the smoothed zero series.
CONDITIONAL ON Decomp359b.positive_square_partial_bound.
The finite near support and the uniform far norm estimate are proved. -/
theorem zeroTerm_summable (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001) :
    Summable (zeroTerm m X u) := by
  classical
  obtain ⟨C, _, hC⟩ := Decomp359c.far_norm_majorant m X u hm hX hu hmu
  have htail := (Decomp359b.reciprocal_tail_summable m (by omega)).mul_left C
  have hfar : Summable (fun i : ZI => if (1000 : ℝ) < |gZ i| then
      zeroTerm m X u i else 0) := Summable.of_norm_bounded htail hC
  have hnear : Summable (fun i : ZI => if |gZ i| ≤ (1000 : ℝ) then
      zeroTerm m X u i else 0) := summable_of_hasFiniteSupport (Decomp359a.near_support_finite m X u)
  convert hnear.add hfar using 1
  funext i
  by_cases h : |gZ i| ≤ (1000 : ℝ)
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

/-- P0099 p. 19, the explicit formula split at height T.
CONDITIONAL ON the new single-scale formula, series subtraction and reciprocal leaf. -/
theorem weighted_formula (m : ℕ) (X u T : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001)
    (hT : 1000 ≤ T) :
    (∫ t in (0 : ℝ)..1, Dψ X u (m * u) t * fm m t) =
      (∫ t in (0 : ℝ)..1,
        (Real.exp u * (1 + m * u * t) * X - (1 + m * u * t) * X) * fm m t) -
      nearSum m X u T - farSum m X u T -
        ∫ t in (0 : ℝ)..1,
          (1 / 2) * (Real.log (1 - 1 / (Real.exp u * ((1 + m * u * t) * X)) ^ 2) -
            Real.log (1 - 1 / ((1 + m * u * t) * X) ^ 2)) * fm m t := by
  have hs := Decomp290c.zero_sum_split m X u T (zeroTerm_summable m X u hm hX hu hmu)
  have hf := Decomp359d.weighted_formula_total m X u hm hX hu hmu
  linarith

/-- P0099 p. 14, Lemma 1 with both signs.
CONDITIONAL ON the new Rosser leaves and the unchanged original low_count citation. -/
theorem lemma1_two_sided : L1Zeta.Lemma1N := by
  intro T hT
  by_cases h : T ≤ 1400
  · have hR := Decomp290b.low_count T hT h
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1000) hT
    have hlow := VerifyU1333.log_thousand_ge
    have hpi := VerifyU1333.log_two_pi_le
    have hbound : (2 : ℝ) ≤ 0.67 * Real.log (T / (2 * π)) := by
      rw [Real.log_div (by linarith : T ≠ 0) (by positivity : 2 * π ≠ 0)]
      linarith
    exact hR.trans hbound
  · have hR := Decomp359g.high_count T (by linarith)
    have hE := VerifyU1333.rosser_err_le T hT
    have hpos : 0 ≤ (0.2 : ℝ) / T := div_nonneg (by norm_num) (by linarith)
    linarith

/-- P0099 p. 14, exactly the original upper-count input.
CONDITIONAL ON the new Rosser leaves and the original low_count citation. -/
theorem lemma1_cited : Row1.Lemma1Upper L1Zeta.NZr := by
  intro T hT
  have h := lemma1_two_sided T hT
  have hab := le_abs_self (L1Zeta.NZr T -
    (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8))
  linarith

/-- P0099 p. 20, display 15, with the proved near count and far majorant.
CONDITIONAL ON the new analytic leaves and the original verified_height citation. -/
theorem display15 (hN : L1Zeta.Lemma1N) :
    JLower15Lit L1Zeta.NZr (ZsF gZ bZ) 3300000000 := by
  intro m X u T hm hX hu hmu hT hTT
  apply Decomp1531b.display15_of_split (Near := nearSum m X u T) (Far := farSum m X u T) hm hX hu hmu
  · change (∫ t in (0 : ℝ)..1, Dψ X u (m * u) t * fm m t) = _
    have hs := Decomp290c.zero_sum_split m X u T
      (CountConvergence359.zeroTerm_summable_of_count hN m X u hm hX hu hmu)
    have hf := Decomp359d.weighted_formula_total m X u hm hX hu hmu
    linarith
  · exact Decomp359f.near_sum_le Decomp290a.verified_height m X u T hm hX hu hmu hT hTT
  · exact CountConvergence359.far_sum_le hN m X u T hm hX hu hmu hT

/-- P0099 pp. 18 to 20, Theorem 4 from the true count input.
CONDITIONAL ON the new analytic leaves and the excluded original citations. -/
theorem theorem4_of_lemma1 (hN : L1Zeta.Lemma1N) : Theorem4Fm L1Zeta.NZr 3300000000 :=
  Thm4LiteralZeta.theorem4Fm_of_zeta_lit Decomp290a.brun_titchmarsh Decomp290a.schoenfeld
    (display15 hN) Decomp290a.verified_height (L1Zeta.lemma1Count_zeta hN)

/-- P0099 pp. 18 to 20, exactly the original Theorem 4 target.
CONDITIONAL ON five new OPEN leaves and five excluded original cited leaves.
There is no additional target hypothesis and no sorry in this assembly. -/
theorem theorem4_cited : Theorem4Fm L1Zeta.NZr 3300000000 :=
  theorem4_of_lemma1 lemma1_two_sided

end LeanLab.RamareSaouter2003.Assembly359

#print axioms LeanLab.RamareSaouter2003.Assembly359.zeroTerm_summable
#print axioms LeanLab.RamareSaouter2003.Assembly359.weighted_formula
#print axioms LeanLab.RamareSaouter2003.Assembly359.lemma1_two_sided
#print axioms LeanLab.RamareSaouter2003.Assembly359.lemma1_cited
#print axioms LeanLab.RamareSaouter2003.Assembly359.display15
#print axioms LeanLab.RamareSaouter2003.Assembly359.theorem4_of_lemma1
#print axioms LeanLab.RamareSaouter2003.Assembly359.theorem4_cited
