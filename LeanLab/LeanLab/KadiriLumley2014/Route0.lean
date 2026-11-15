/-
P0059 Kadiri and Lumley 2014, arXiv 1407.7902v1.
Page 9 Theorem 2.7 display 2.64, pages 8 and 9 Lemma 2.6 with the coefficients of
displays 2.51, 2.54, 2.58, 2.60, 2.62 and 2.63, page 8 displays 2.40 to 2.44,
page 3 equation 2.7, page 11 Theorem 3.2, page 12 Table 1 row sigma = 0.92 and
page 13 Table 2 row 1, the row with threshold x0 = 4*10^18 and delta = 35800/10^12,
stored as logIndex 0.
This file assembles the certified lower bounds of Route0Factor, Route0Low, Route0Mid,
Route0Density and Route0Tail into a lower bound for the lab's envelopeBudget at that
row, and concludes that the numerical hypothesis hnum of
Task92.table_endpoint_budget_of_envelope FAILS there with the printed height and the
printed sigma row. This is a statement about the lab's envelope as transcribed on main,
with the corrected zeroS5 of DECISION U-1626.
It does not say that Task92.table_endpoint_budget is false: that leaf has the true zero sum.
AI wrote this Lean code, burst 2026-11-15. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.EndpointEnvelope
import LeanLab.KadiriLumley2014.Route0Factor
import LeanLab.KadiriLumley2014.Route0Low
import LeanLab.KadiriLumley2014.Route0Mid
import LeanLab.KadiriLumley2014.Route0Density
import LeanLab.KadiriLumley2014.Route43Density
import LeanLab.KadiriLumley2014.Route0Tail

namespace LeanLab.KadiriLumley2014.Route0

open Real
open LeanLab.KadiriLumley2014.Task64 LeanLab.KadiriLumley2014.Task92
  LeanLab.KadiriLumley2014.Task259

/-- Page 9 display 2.64 with the zero sum replaced by the Lemma 2.6 envelope, at the
parameters of Table 2 row 1, x0 = 4*10^18, and Table 1 row sigma = 0.92: the envelope
budget is at least 1 + delta/2. The certified lower bounds are 0.7175 for the B0 and B1
terms, 0.1530 for the B2 term, 0.0243 for the density term of display 2.62 and 0.1128
for the tail term; the other terms are nonnegative. It rests on the corrected zeroS5 of
DECISION U-1626 and does not bound the true zero sum. -/
theorem envelopeBudget_row0_ge {δ u X : ℝ} (hδ : δ = 35800 / 10 ^ 12) (hu : u = δ / 5)
    (hXlo : 4 * 10 ^ 18 / (1 + 1 / 10 ^ 6) ≤ X) (hXhi : X ≤ 4 * 10 ^ 18) :
    1 + δ / 2 ≤ envelopeBudget 5 δ u X (2129 / 10000 + 1 / 10000) 272519712 (92 / 100)
      5.5564 0.4426 (-170070000000) := by
  have hδ0 : 0 < δ := by rw [hδ]; norm_num
  have hu0 : 0 < u := by rw [hu]; positivity
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hXlo
  have hF : (86200 : ℝ) ≤ higherFactor 5 δ := higherFactor_five_ge hδ0.le
  have hF0 : 0 ≤ higherFactor 5 δ := by linarith
  have he : 0 < Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have hlow := low_terms_ge hδ hu hXlo hXhi
  have hmid := mid_term_ge hδ hu hXlo hXhi hF
  have hden := density_term_ge hδ hu hXlo hXhi hF
  have htail := tail_term_ge hδ hu hXlo hXhi
  have hS3 := Route43.zeroS3_five_nonneg
  have hS4 := Route43.zeroS4_row_nonneg
  have hB3a : 0 ≤ 2 * higherFactor 5 δ * (Real.exp (u * (92 / 100)) + 1) /
      (δ ^ 5 * (Real.exp u - 1)) * zeroS3 5 * X ^ ((92 / 100 : ℝ) - 1) := by
    have := Real.exp_pos (u * (92 / 100))
    have := Real.rpow_nonneg hX0.le ((92 / 100 : ℝ) - 1)
    positivity
  have hB3b : 0 ≤ 2 * higherFactor 5 δ * (Real.exp (u * (1 - 92 / 100)) + 1) /
      (δ ^ 5 * (Real.exp u - 1)) * zeroS3 5 * X ^ (-(92 / 100 : ℝ)) := by
    have := Real.exp_pos (u * (1 - 92 / 100))
    have := Real.rpow_nonneg hX0.le (-(92 / 100 : ℝ))
    positivity
  have hC4 : 0 ≤ 2 * (Real.exp u + 1) * higherFactor 5 δ / ((Real.exp u - 1) * δ ^ 5) *
      zeroS4 5 5.5564 0.4426 (-170070000000) *
        X ^ (-1 + 1 / (5.69693 * Real.log 30610000000)) := by
    have := Real.exp_pos u
    have := Real.rpow_nonneg hX0.le (-1 + 1 / (5.69693 * Real.log 30610000000))
    positivity
  have hut : 0 ≤ u / (2 * (Real.exp u - 1) * X ^ 2) := by positivity
  have hsq : 0 ≤ (2.05022 * 10 ^ (-3 : ℤ)) / ((Real.exp u - 1) * Real.sqrt X) := by
    have := Real.sqrt_nonneg X
    positivity
  unfold envelopeBudget rosserZeroEnvelope
  dsimp only
  rw [add_mul]
  linarith

/-- Page 9 display 2.64 with the zero sum bounded as in Lemma 2.6 FAILS at Table 2 row 1, x0 = 4*10^18:
with the printed height T1 = 272519712, the Table 1 row sigma = 0.92 and the endpoint
rowEndpointX of the row, the lab's envelope budget is not below 1 + delta/2. This is the
negation of the hypothesis hnum of Task92.table_endpoint_budget_of_envelope at this row,
height and sigma row only, and it rests on the corrected zeroS5 of DECISION U-1626.
It does NOT show that Task92.table_endpoint_budget is false: it concerns the envelope as
transcribed on main, not the true zero sum of that leaf, which stays OPEN. Other heights
T1 or sigma rows are not covered. -/
theorem table_row0_envelope_fails :
    let r : PrintedRow := ⟨0, 5, 35800, 272519712, 92, 2129, 36082898⟩
    let d : ℕ × ℚ × ℚ × ℚ := (92, 5.5564, 0.4426, -170070000000)
    r ∈ tableTwo ∧ d ∈ densityTable ∧ d.1 = r.sigmaUnits ∧
    ¬ (envelopeBudget r.m r.deltaQ r.uQ (rowEndpointX r) ((r.aQ : ℝ) + 1 / 10000)
        (r.height : ℝ) ((d.1 : ℝ) / 100) d.2.1 d.2.2.1 d.2.2.2 < 1 + (r.deltaQ : ℝ) / 2) := by
  intro r d
  have hδ : ((r.deltaQ : ℚ) : ℝ) = 35800 / 10 ^ 12 := by
    simp [r, PrintedRow.deltaQ]
  have hu : ((r.uQ : ℚ) : ℝ) = ((r.deltaQ : ℚ) : ℝ) / 5 := by
    simp [r, PrintedRow.uQ]
  have hu' : ((r.uQ : ℚ) : ℝ) = 35800 / 10 ^ 12 / 5 := by rw [hu, hδ]
  have hthr : r.threshold = 4 * 10 ^ 18 := by
    simp [r, PrintedRow.threshold, evenBase]; norm_num
  have he1 : 1 ≤ Real.exp ((r.uQ : ℚ) : ℝ) := by
    apply Real.one_le_exp
    rw [hu']; norm_num
  have he2 : Real.exp ((r.uQ : ℚ) : ℝ) ≤ 1 / (1 - ((r.uQ : ℚ) : ℝ)) :=
    Real.exp_bound_div_one_sub_of_interval (by rw [hu']; norm_num) (by rw [hu']; norm_num)
  have he3 : Real.exp ((r.uQ : ℚ) : ℝ) ≤ 1 + 1 / 10 ^ 8 := by
    refine he2.trans ?_
    rw [hu']; norm_num
  have hS1 : 1 ≤ Real.exp ((r.uQ : ℚ) : ℝ) * (1 + ((r.deltaQ : ℚ) : ℝ)) := by
    have : (0 : ℝ) ≤ ((r.deltaQ : ℚ) : ℝ) := by rw [hδ]; norm_num
    nlinarith
  have hS2 : Real.exp ((r.uQ : ℚ) : ℝ) * (1 + ((r.deltaQ : ℚ) : ℝ)) ≤ 1 + 1 / 10 ^ 6 := by
    have h1 : (1 + ((r.deltaQ : ℚ) : ℝ)) ≤ 1 + 4 / 10 ^ 8 := by rw [hδ]; norm_num
    calc Real.exp ((r.uQ : ℚ) : ℝ) * (1 + ((r.deltaQ : ℚ) : ℝ))
        ≤ (1 + 1 / 10 ^ 8) * (1 + 4 / 10 ^ 8) :=
          mul_le_mul he3 h1 (by rw [hδ]; norm_num) (by norm_num)
      _ ≤ _ := by norm_num
  have hXlo : 4 * 10 ^ 18 / (1 + 1 / 10 ^ 6) ≤ rowEndpointX r := by
    unfold rowEndpointX
    rw [hthr]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hS2
  have hXhi : rowEndpointX r ≤ 4 * 10 ^ 18 := by
    unfold rowEndpointX
    rw [hthr]
    exact div_le_self (by norm_num) hS1
  have h := envelopeBudget_row0_ge hδ hu hXlo hXhi
  refine ⟨by simp [r, tableTwo], by simp [d, densityTable], rfl, not_lt.mpr ?_⟩
  have e1 : ((r.aQ : ℚ) : ℝ) + 1 / 10000 = 2129 / 10000 + 1 / 10000 := by
    simp [r, PrintedRow.aQ]
  have e2 : ((r.height : ℕ) : ℝ) = 272519712 := by simp [r]
  have e3 : ((d.1 : ℕ) : ℝ) / 100 = 92 / 100 := by simp [d]
  have e4 : ((d.2.1 : ℚ) : ℝ) = 5.5564 := by simp [d]
  have e5 : ((d.2.2.1 : ℚ) : ℝ) = 0.4426 := by simp [d]
  have e6 : ((d.2.2.2 : ℚ) : ℝ) = -170070000000 := by simp [d]
  have e7 : r.m = 5 := rfl
  rw [e1, e2, e3, e4, e5, e6, e7]
  exact h

end LeanLab.KadiriLumley2014.Route0

#print axioms LeanLab.KadiriLumley2014.Route0.envelopeBudget_row0_ge
#print axioms LeanLab.KadiriLumley2014.Route0.table_row0_envelope_fails
