/-
P0059, Kadiri and Lumley 2014, arXiv 1407.7902v1, page 5 display 2.28, page 6 Theorem 2.4 a,
page 7 display 2.47 and Table 2 on page 13. SPLIT of endpoint_mid_height_zero_sum_high_S10 from
SPLIT_table_endpoint_budget_high.lean, ROUTE BURST S10 burst-20261124, step tablehighc.
The zeros with ordinate between H = 3.061e10 and H2 = 3e12 lie on the critical line by the
verification of Platt and Trudgian 2021, Theorem 2.4 a with H2. Each summand is then at most
display 2.28 times X^(-1/2), PROVED here from smoothingG_norm_higher_im and smoothingG_norm_conj,
and the reciprocal powers above H are bounded by display 2.47 at H, both signs.
Uncertified mpmath: twice S3 at 3.061e10 times 3.061e10^m is 0.1165 for m = 61 and 0.1110 for
m = 64; the final product is at most 1.3e-13 on rows 58 to 60 and 2.1e-33 on row 150, against
the budget 1e-5.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.SPLIT_endpoint_top_height_zero_tail_high

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open scoped ComplexConjugate
open Task64

/-- Page 5 display 2.28 for a zero of either sign, keeping the factor X^(beta - 1). PROVED. -/
theorem zeroSummand_le_rpow_S10 (m : ℕ) {δ u X : ℝ} (hδ : 0 < δ) (hu : 0 < u) (hX : 0 ≤ X)
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) (hγ : 0 < |ρ.1.im|) :
    zeroSummand m δ u X ρ ≤
      higherFactor m δ * (Real.exp u + 1) / ((Real.exp u - 1) * δ ^ m) *
        ((analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / |ρ.1.im| ^ (m + 1)) *
          X ^ ((ρ : ℂ).re - 1) := by
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
  have hXp : 0 ≤ X ^ ((ρ : ℂ).re - 1) := Real.rpow_nonneg hX _
  have hmult : (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) := by positivity
  unfold zeroSummand
  calc (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖smoothingG m δ u ρ‖ *
        X ^ ((ρ : ℂ).re - 1)
      ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * (higherFactor m δ * (Real.exp u + 1) /
        ((Real.exp u - 1) * δ ^ m * |ρ.1.im| ^ (m + 1))) * X ^ ((ρ : ℂ).re - 1) := by
        gcongr
    _ = _ := by
        have ha : |ρ.1.im| ^ (m + 1) ≠ 0 := by positivity
        have hd : δ ^ m ≠ 0 := by positivity
        field_simp

/-- LEAF: page 6 Theorem 2.4 a with the verified height 3e12 of Platt and Trudgian 2021,
Bull. London Math. Soc. 53, arXiv 2004.09765, main theorem: every nontrivial zero with absolute
ordinate at most 3e12 has real part one half. Their verified height is 3000175332800. This is
a citation of a rigorous computation, outside P0059. Class HARD. -/
theorem verified_height_three_e12_S10
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1})
    (hγ : |ρ.1.im| ≤ 3000000000000) : (ρ : ℂ).re = 1 / 2 := by
  sorry

/-- LEAF: page 7 display 2.47 at H = 3.061e10 for both signs of the ordinate, from the Riemann
von Mangoldt count with Rosser's error, input b of Theorem 2.4 on page 6, for the parameter m
of rows 58, 59, 60 and 150 of Table 2 on page 13, where m is 61 or 64. The lab proves the one
sign tsum form from RosserCountBound as the private power_tail of ZeroBounds259. Uncertified
mpmath: twice S3 times 3.061e10^m is 0.1165 and 0.1110, below the stated 1. Class HARD. -/
theorem endpoint_mid_power_tail_S10 {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex)
    (s : Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ 30610000000),
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / |ρ.1.im| ^ (r.m + 1) ≤
      1 / (30610000000 : ℝ) ^ r.m := by
  sorry

/-- LEAF: numeric size of the middle range for rows 58, 59, 60 and 150 of Table 2 on page 13:
F_{m,m,delta} of display 2.24 times (e^u + 1) / ((e^u - 1) delta^m), times 3.061e10^-m, times
X^(-1/2) at the row endpoint, is at most 1e-5. Uncertified mpmath 1.23e-13, 7.6e-14, 4.7e-14
and 2.1e-33. Class MEDIUM. -/
theorem endpoint_mid_numeric_S10 {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex) :
    higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) / ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) *
        (1 / (30610000000 : ℝ) ^ r.m) * rowEndpointX r ^ ((1 : ℝ) / 2 - 1) ≤ 1 / 100000 := by
  sorry

/-- Assembly: the exact statement of endpoint_mid_height_zero_sum_high_S10 from the proved
pointwise bound and the three leaves. -/
theorem endpoint_mid_height_zero_sum_high_split_S10 {r : PrintedRow} (hr : r ∈ tableTwo)
    (hhigh : 58 ≤ r.logIndex)
    (s : Finset {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ 30610000000 ∧ |ρ.1.im| ≤ 3000000000000),
        zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r) ρ ≤ 1 / 100000 := by
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
  have hu : (0 : ℝ) < r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    have h2 : (0 : ℝ) < ((1 / 10 ^ 12 : ℚ) : ℝ) := by norm_num
    linarith
  have hX : 0 < rowEndpointX r := by
    unfold rowEndpointX PrintedRow.threshold
    have hne : r.logIndex ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    positivity
  have he : 0 < Real.exp (r.uQ : ℝ) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hC : 0 ≤ higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) /
      ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) :=
    div_nonneg (mul_nonneg (higherFactor_nonneg_S10 r.m hδ.le) (by positivity))
      (mul_pos he (pow_pos hδ _)).le
  have hXh : 0 ≤ rowEndpointX r ^ ((1 : ℝ) / 2 - 1) := Real.rpow_nonneg hX.le _
  have hsub : s.filter (fun ρ => ¬ |ρ.1.im| ≤ 30610000000 ∧ |ρ.1.im| ≤ 3000000000000) =
      (s.filter (fun ρ => |ρ.1.im| ≤ 3000000000000)).filter
        (fun ρ => ¬ |ρ.1.im| ≤ 30610000000) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun ρ _ => and_comm)
  rw [hsub]
  set C := higherFactor r.m r.deltaQ * (Real.exp r.uQ + 1) /
      ((Real.exp r.uQ - 1) * (r.deltaQ : ℝ) ^ r.m) with hCdef
  calc ∑ ρ ∈ (s.filter (fun ρ => |ρ.1.im| ≤ 3000000000000)).filter
          (fun ρ => ¬ |ρ.1.im| ≤ 30610000000),
        zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r) ρ
      ≤ ∑ ρ ∈ (s.filter (fun ρ => |ρ.1.im| ≤ 3000000000000)).filter
          (fun ρ => ¬ |ρ.1.im| ≤ 30610000000),
          C * ((analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / |ρ.1.im| ^ (r.m + 1)) *
            rowEndpointX r ^ ((1 : ℝ) / 2 - 1) := by
        refine Finset.sum_le_sum (fun ρ hρ => ?_)
        have hρ1 := Finset.mem_filter.mp hρ
        have hρ2 := (Finset.mem_filter.mp hρ1.1).2
        have hre := verified_height_three_e12_S10 ρ hρ2
        have h := zeroSummand_le_rpow_S10 r.m hδ hu hX.le ρ (by linarith [hρ1.2])
        rw [hre] at h
        exact h
    _ = C * (∑ ρ ∈ (s.filter (fun ρ => |ρ.1.im| ≤ 3000000000000)).filter
          (fun ρ => ¬ |ρ.1.im| ≤ 30610000000),
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / |ρ.1.im| ^ (r.m + 1)) *
            rowEndpointX r ^ ((1 : ℝ) / 2 - 1) := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ C * (1 / (30610000000 : ℝ) ^ r.m) * rowEndpointX r ^ ((1 : ℝ) / 2 - 1) := by
        gcongr
        exact endpoint_mid_power_tail_S10 hr hhigh _
    _ ≤ 1 / 100000 := endpoint_mid_numeric_S10 hr hhigh

#print axioms zeroSummand_le_rpow_S10
#print axioms endpoint_mid_height_zero_sum_high_split_S10

end LeanLab.KadiriLumley2014.Task92
