/-
P0059, Kadiri and Lumley 2014, arXiv 1407.7902v1, page 5 display 2.28, page 7 display 2.47 and
page 9 displays 2.59 and 2.60, with Table 2 on page 13. SPLIT of
endpoint_top_height_zero_tail_high_S10 from SPLIT_table_endpoint_budget_high.lean,
ROUTE BURST S10 burst-20261124, step tablehighb.
Every zero above H2 = 3e12 is bounded by display 2.28, proved in GIterated92 as
smoothingG_norm_higher_im, with e^(u beta) + 1 at most e^u + 1 and X^(beta - 1) at most 1, and
with the conjugate zeros handled by smoothingG_norm_conj of Conjugation301. This is display 2.59
with sigma0 = 1. The pointwise step is PROVED here. What is left is the reciprocal power sum over
zeros above 3e12, display 2.47 at H = 3e12, and a numeric check.
Uncertified mpmath: twice S3 of display 2.47 at 3e12 times 3e12^m is about 0.14 for m = 61 and 64,
below the leaf budget 1; the final product is about 1e-123 on rows 58 to 60 and 1e-129 on row
150, against the budget 1e-5.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.SPLIT_table_endpoint_budget_high
import LeanLab.KadiriLumley2014.GIterated92
import LeanLab.KadiriLumley2014.Conjugation301
import LeanLab.KadiriLumley2014.SPLIT_endpoint_top_height_zero_tail_high_numeric

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open scoped ComplexConjugate
open Task64

/-- The higher factor F of page 5 display 2.24 is nonnegative. -/
theorem higherFactor_nonneg_S10 (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ higherFactor m δ := by
  unfold higherFactor
  refine div_nonneg ?_ (weight_mass_pos m).le
  refine intervalIntegral.integral_nonneg (by norm_num) (fun t ht => ?_)
  have h1 : 0 ≤ 1 + δ * t := by nlinarith [ht.1]
  exact mul_nonneg (pow_nonneg h1 _) (abs_nonneg _)

/-- Page 5 display 2.28 with the trivial factor X^(beta - 1) at most 1, the summand of display
2.59 with sigma0 = 1, for a zero of either sign of ordinate. PROVED. -/
theorem zeroSummand_le_top_S10 (m : ℕ) {δ u X : ℝ} (hδ : 0 < δ) (hu : 0 < u) (hX : 1 ≤ X)
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) (hγ : 0 < |ρ.1.im|) :
    zeroSummand m δ u X ρ ≤
      higherFactor m δ * (Real.exp u + 1) / ((Real.exp u - 1) * δ ^ m) *
        ((analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / |ρ.1.im| ^ (m + 1)) := by
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hF := higherFactor_nonneg_S10 m hδ.le
  have key : ∀ s : ℂ, 0 < s.re → s.re < 1 → 0 < s.im →
      ‖smoothingG m δ u s‖ ≤ higherFactor m δ * (Real.exp u + 1) /
        ((Real.exp u - 1) * δ ^ m * s.im ^ (m + 1)) := by
    intro s h1 h2 h3
    refine (smoothingG_norm_higher_im m hδ hu h1 h2.le h3).trans ?_
    have hus : u * s.re ≤ u := by nlinarith
    have hnum : higherFactor m δ * (Real.exp (u * s.re) + 1) ≤
        higherFactor m δ * (Real.exp u + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.exp_le_exp.mpr hus]) hF
    have hD : 0 ≤ (Real.exp u - 1) * δ ^ m * s.im ^ (m + 1) := by positivity
    exact div_le_div_of_nonneg_right hnum hD
  have hG : ‖smoothingG m δ u ρ‖ ≤ higherFactor m δ * (Real.exp u + 1) /
      ((Real.exp u - 1) * δ ^ m * |ρ.1.im| ^ (m + 1)) := by
    rcases lt_or_gt_of_ne (abs_pos.mp hγ) with hneg | hpos
    · have h := key (conj (ρ : ℂ)) (by simpa using ρ.2.2.1) (by simpa using ρ.2.2.2)
        (by simpa using hneg)
      rw [Task301.smoothingG_norm_conj m hδ.le u] at h
      rw [abs_of_neg hneg]
      simpa using h
    · rw [abs_of_pos hpos]
      exact key ρ ρ.2.2.1 ρ.2.2.2 hpos
  have hXp : X ^ ((ρ : ℂ).re - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith [ρ.2.2.2])
  have hmult : (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) := by positivity
  unfold zeroSummand
  calc (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖smoothingG m δ u ρ‖ *
        X ^ ((ρ : ℂ).re - 1)
      ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖smoothingG m δ u ρ‖ * 1 :=
        mul_le_mul_of_nonneg_left hXp (mul_nonneg hmult (norm_nonneg _))
    _ ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * (higherFactor m δ * (Real.exp u + 1) /
        ((Real.exp u - 1) * δ ^ m * |ρ.1.im| ^ (m + 1))) * 1 := by
        gcongr
    _ = _ := by
        have ha : |ρ.1.im| ^ (m + 1) ≠ 0 := by positivity
        have hd : δ ^ m ≠ 0 := by positivity
        rw [mul_one]
        field_simp

/-- LEAF: page 7 display 2.47 at the verified height H = 3e12 of Platt and Trudgian 2021, for
both signs of the ordinate, from the Riemann von Mangoldt count with Rosser's error, input b of
Theorem 2.4 on page 6, for the parameter m of rows 58, 59, 60 and 150 of Table 2 on page 13,
where m is 61 or 64. Twice S3 at 3e12 is about 0.14 / 3e12^m by uncertified mpmath, below the
stated 1 / 3e12^m. Class HARD. -/
theorem endpoint_top_power_tail_S10 {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex)
    (s : Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ 3000000000000),
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / |ρ.1.im| ^ (r.m + 1) ≤
      1 / (3000000000000 : ℝ) ^ r.m := by
  sorry

/-- LEAF: page 9 display 2.60 with sigma = 1 at H = 3e12, the numeric size of the top range for
rows 58, 59, 60 and 150 of Table 2 on page 13: F_{m,m,delta} of display 2.24 times
(e^u + 1) / ((e^u - 1) delta^m) times 3e12^-m is at most 1e-5. Uncertified mpmath: F is about
1.86e120 on rows 58 to 60 and 2.97e127 on row 150, delta times 3e12 is about 13800, and the
product is about 1e-123 and 1e-129. Class MEDIUM. -/
theorem endpoint_top_numeric_S10 {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex) :
    higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) / ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) *
        (1 / (3000000000000 : ℝ) ^ r.m) ≤ 1 / 100000 := by
  exact endpoint_top_numeric_S10_helper hr hhigh

/-- Assembly: the exact statement of endpoint_top_height_zero_tail_high_S10 from the proved
pointwise bound and the two leaves. -/
theorem endpoint_top_height_zero_tail_high_split_S10 {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex)
    (s : Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ 3000000000000),
        zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r) ρ ≤ 1 / 100000 := by
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
  have hδ1 : (r.deltaQ : ℝ) ≤ 1 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.1
    have h2 : ((0.0001 : ℚ) : ℝ) ≤ 1 := by norm_num
    linarith
  have hu : (0 : ℝ) < r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    have h2 : (0 : ℝ) < ((1 / 10 ^ 12 : ℚ) : ℝ) := by norm_num
    linarith
  have hu1 : (r.uQ : ℝ) ≤ 1 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.2
    have h2 : ((0.0001 : ℚ) : ℝ) ≤ 1 := by norm_num
    linarith
  have hX : 1 ≤ rowEndpointX r := by
    unfold rowEndpointX PrintedRow.threshold
    have hne : r.logIndex ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    have hexpu : Real.exp (r.uQ : ℝ) ≤ 3 := by
      have := Real.exp_le_exp.mpr hu1
      have h3 := Real.exp_one_lt_d9
      linarith
    have hden : 0 < Real.exp (r.uQ : ℝ) * (1 + (r.deltaQ : ℝ)) := by positivity
    have hthr : (59 : ℝ) ≤ Real.exp (r.logIndex : ℝ) := by
      have h1 := Real.add_one_le_exp (r.logIndex : ℝ)
      have h2 : (58 : ℝ) ≤ r.logIndex := by exact_mod_cast hhigh
      linarith
    rw [le_div_iff₀ hden]
    nlinarith
  have he : 0 < Real.exp (r.uQ : ℝ) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hC : 0 ≤ higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) /
      ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) :=
    div_nonneg (mul_nonneg (higherFactor_nonneg_S10 r.m hδ.le) (by positivity))
      (mul_pos he (pow_pos hδ _)).le
  calc ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ 3000000000000),
        zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r) ρ
      ≤ ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ 3000000000000),
          higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) /
            ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) *
          ((analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / |ρ.1.im| ^ (r.m + 1)) := by
        refine Finset.sum_le_sum (fun ρ hρ => ?_)
        have hρ' := (Finset.mem_filter.mp hρ).2
        exact zeroSummand_le_top_S10 r.m hδ hu hX ρ (by linarith)
    _ = higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) /
          ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) *
        ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ 3000000000000),
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / |ρ.1.im| ^ (r.m + 1) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) /
          ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) *
        (1 / (3000000000000 : ℝ) ^ r.m) :=
        mul_le_mul_of_nonneg_left (endpoint_top_power_tail_S10 hr hhigh s) hC
    _ ≤ 1 / 100000 := endpoint_top_numeric_S10 hr hhigh

#print axioms zeroSummand_le_top_S10
#print axioms endpoint_top_height_zero_tail_high_split_S10

end LeanLab.KadiriLumley2014.Task92
