/-
P0059 arXiv 1407.7902v1 page 9 equation 2.64, page 11 Theorem 3.2, page 13 Table 2.
Assemble the positive analytic zero envelope and an explicit numerical certificate.
The published and analytic leaves remain CONDITIONAL.
AI wrote this Lean code. CODEX task259. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroBounds259
import LeanLab.KadiriLumley2014.BudgetBase259
import LeanLab.KadiriLumley2014.Kernel259
import LeanLab.KadiriLumley2014.TableRounding

namespace LeanLab.KadiriLumley2014.Task259

open Real Set MeasureTheory
open Task64 Task92 Task301

/-- The normalized Proposition 2.3 budget with Sigma replaced by the positive Rosser envelope. -/
noncomputable def envelopeBudget (m : ℕ) (δ u X a T1 σ c1 c2 c3 : ℝ) : ℝ :=
  rosserZeroEnvelope m δ u X T1 σ c1 c2 c3 + u / (2 * (Real.exp u - 1) * X ^ 2) +
    (2.05022 * 10 ^ (-3 : ℤ)) / ((Real.exp u - 1) * Real.sqrt X) +
    (2 * (1 + δ) * tailMass m a / (∫ t in (0 : ℝ)..1, weight m t)) *
      (Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1)))

/-- The printed lower a never satisfies the exact denominator premise of the sealed budget.
This is the rounding obstruction to using its numerical margin in that leaf. -/
theorem printed_a_not_exact {r : PrintedRow} (hr : r ∈ tableTwo) :
    (r.gapDenom : ℝ) ≠ 1 / intervalFraction r.deltaQ r.uQ r.aQ := by
  intro h
  have hb := (tableTwo_rounding_bracket hr).1
  rw [h] at hb
  by_cases hg : intervalFraction r.deltaQ r.uQ r.aQ = 0
  · norm_num [hg] at hb
  · rw [one_div_mul_cancel hg] at hb
    linarith

/-- The exact original zero budget assembled from the published inputs, Lemmas 2.5 and 2.6
and a numerical certificate supplied as a hypothesis.
CONDITIONAL ON the seven cited or analytic leaves and that certificate. -/
theorem table_zero_budget_of_certificate {r : PrintedRow} (hr : r ∈ tableTwo) {a X : ℝ}
    (ha : a ∈ Icc (r.aQ : ℝ) ((r.aQ : ℝ) + 1 / 10000))
    (_hD : (r.gapDenom : ℝ) = 1 / intervalFraction r.deltaQ r.uQ a)
    (_hX : Real.exp 38 ≤ X)
    (_hx : r.threshold < Real.exp r.uQ * (X * (1 + (r.deltaQ : ℝ) * (1 - a))))
    (hCert :
    ∃ (Y T1 : ℝ) (d : ℕ × ℚ × ℚ × ℚ),
      Real.exp 38 ≤ Y ∧ Y ≤ X ∧ 1 < Y * (Real.exp r.uQ - 1) ∧
      d ∈ densityTable ∧ d.1 = r.sigmaUnits ∧
      (r.height : ℝ) ≤ T1 ∧ T1 ≤ (r.height : ℝ) + 1 ∧
      1132491 ≤ T1 ∧ T1 ≤ 30610000000 ∧
      Real.log Y < 5.69693 * r.m * (Real.log 30610000000) ^ 2 ∧
      envelopeBudget r.m r.deltaQ r.uQ Y a T1 ((d.1 : ℝ) / 100) d.2.1 d.2.2.1 d.2.2.2 <
        1 + (r.deltaQ : ℝ) / 2 ) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X +
      tailCoefficient r.deltaQ r.uQ X * tailMass r.m a /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * X) <
      (Real.exp r.uQ - 1) * X *
        (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ X) := by
  obtain ⟨Y, T1, d, hY, hYX, hgap, hd, _hσmatch, _hT1lo, _hT1hi, hT0, hTH, hlog, hnum⟩ :=
    hCert
  have hp := tableTwo_parameters r hr
  have hs := table_small_steps r hr
  have hm : 2 ≤ r.m := hp.1
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
  have hδ1 : (r.deltaQ : ℝ) ≤ 0.0001 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.1
    norm_num at h ⊢
    exact h
  have hu : (0 : ℝ) < r.uQ := by
    have h : (1 / (10 : ℝ) ^ 12) ≤ r.uQ := by
      have hh := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
      norm_num at hh ⊢
      exact hh
    linarith
  have hu1 : (r.uQ : ℝ) ≤ 0.0001 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.2
    norm_num at h ⊢
    exact h
  have hm0 : (r.m : ℝ) ≠ 0 := by exact_mod_cast (show r.m ≠ 0 by omega)
  have hδu : (r.deltaQ : ℝ) = r.m * (r.uQ : ℝ) := by
    simp only [PrintedRow.uQ, Rat.cast_div, Rat.cast_natCast]
    field_simp
  have hdpar := densityTable_domain d hd
  have hc1 : (0 : ℝ) ≤ d.2.1 := by exact_mod_cast hdpar.2.2.1.le
  have hc2 : (0 : ℝ) ≤ d.2.2.1 := by exact_mod_cast hdpar.2.2.2.1.le
  have hσ : (3 / 5 : ℝ) < (d.1 : ℝ) / 100 := by
    have h : (60 : ℝ) < d.1 := by exact_mod_cast hdpar.1
    linarith
  have hσ1 : (d.1 : ℝ) / 100 < 1 := by
    have h : (d.1 : ℝ) < 100 := by exact_mod_cast hdpar.2.1
    linarith
  have hY10 : 10 < Y := by linarith [Real.add_one_le_exp (38 : ℝ)]
  have hY0 : 0 < Y := by linarith
  have hS := lemma2_5_positive r.m hm hY10 hT0 hTH hσ hσ1
    published_verified_height published_low_zero_data published_zero_free_region published_zero_count
    (published_zero_density hd) hc1 hc2 hlog
  have hzero := lemma2_6_positive hm hδ hδ1 hu hu1 hδu hY10 hT0 hTH hσ hσ1
    published_verified_height published_low_zero_data published_zero_free_region published_zero_count
    (published_zero_density hd) hc1 hc2 hlog hS
  have hbudget : normalizedBudget r.m r.deltaQ r.uQ Y a < 1 + (r.deltaQ : ℝ) / 2 := by
    unfold normalizedBudget envelopeBudget at *
    linarith
  have ha0 : (0 : ℝ) ≤ a := by
    have h : (0 : ℝ) ≤ r.aQ := by
      exact_mod_cast (tableTwo_rounding_arithmetic r hr).1.2.2.2.1
    exact h.trans ha.1
  have ha2 : a ≤ 1 / 2 := by
    have h : (r.aQ : ℝ) + 1 / 10000 ≤ 1 / 2 := by
      have hh := (Rat.cast_le (K := ℝ)).mpr (tableTwo_rounding_arithmetic r hr).1.2.2.2.2.1
      push_cast at hh
      norm_num at hh ⊢
      exact hh
    exact ha.2.trans h
  have hsum := absolute_zero_summable (by omega : 0 < r.m) hδ hu hY0
  have hprop := normalizedBudget_lt_of_base r.m hδ.le hu hY0 hYX ha0 ha2 hgap hsum hbudget
  exact (normalizedBudget_lt_iff r.m r.deltaQ a hu (hY0.trans_le hYX)).mp hprop

end LeanLab.KadiriLumley2014.Task259
