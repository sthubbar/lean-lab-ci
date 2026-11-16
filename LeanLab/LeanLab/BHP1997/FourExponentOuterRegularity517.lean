/-
P0069, Section 5, page 51, display 5.17.
Regularity in the three outer exponent coordinates away from the jumps.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentKernel517

namespace LeanLab.BHP1997.LowerShortC165
open Decomp514a

/-- Page 51 display 5.17. The smooth Buchstab density has a uniform
Lipschitz bound in any one of its first three denominator factors. -/
theorem four_exponent_density_coordinate_outer {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {T a e b c d : ℝ} (ha : (1/10 : ℝ) ≤ a) (he : (1/10 : ℝ) ≤ e)
    (hb : (1/10 : ℝ) ≤ b) (hc : (1/10 : ℝ) ≤ c) (hd : (1/10 : ℝ) ≤ d)
    (hu : 1 ≤ (T-a)/d) (hv : 1 ≤ (T-e)/d) :
    |ω ((T-a)/d)/(a*b*c*d^2) - ω ((T-e)/d)/(e*b*c*d^2)| ≤
      2000000 * |a-e| := by
  have ha0 : 0 < a := by linarith
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  have hae : (1/100 : ℝ) ≤ a*e := by nlinarith
  have harg : |(T-a)/d-(T-e)/d| ≤ 10*|a-e| := by
    have heq : (T-a)/d-(T-e)/d = (e-a)/d := by ring
    rw [heq, abs_div, abs_of_pos hd0, abs_sub_comm e a]
    apply (div_le_iff₀ hd0).mpr
    nlinarith [mul_nonneg (abs_nonneg (a-e)) (sub_nonneg.mpr hd)]
  have hinv : |1/a-1/e| ≤ 100*|a-e| := by
    have heq : 1/a-1/e = (e-a)/(a*e) := by field_simp <;> ring
    rw [heq, abs_div, abs_of_pos (mul_pos ha0 he0), abs_sub_comm e a]
    apply (div_le_iff₀ (mul_pos ha0 he0)).mpr
    nlinarith [mul_nonneg (abs_nonneg (a-e)) (sub_nonneg.mpr hae)]
  have hw := (four_density_buchstab_lipschitz hω hz hu hv).trans harg
  have hw0 := four_density_buchstab_nonneg hω hz ((T-e)/d)
  have hw1 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz ((T-e)/d)
  have hwabs : |ω ((T-e)/d)| ≤ 1 := by rwa [abs_of_nonneg hw0]
  have hfirst : |(ω ((T-a)/d)-ω ((T-e)/d))/a| ≤ 100*|a-e| := by
    rw [abs_div, abs_of_pos ha0]
    apply (div_le_iff₀ ha0).mpr
    calc _ ≤ 10*|a-e| := hw
      _ ≤ _ := by nlinarith [mul_nonneg (abs_nonneg (a-e)) (sub_nonneg.mpr ha)]
  have hsecond : |ω ((T-e)/d)*(1/a-1/e)| ≤ 100*|a-e| := by
    rw [abs_mul]
    calc _ ≤ 1*|1/a-1/e| := mul_le_mul_of_nonneg_right hwabs (abs_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hinv
  have hmid : |ω ((T-a)/d)/a-ω ((T-e)/d)/e| ≤ 200*|a-e| := by
    have heq : ω ((T-a)/d)/a-ω ((T-e)/d)/e =
        (ω ((T-a)/d)-ω ((T-e)/d))/a + ω ((T-e)/d)*(1/a-1/e) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (by linarith)
  have hbc : (1/100 : ℝ) ≤ b*c := by nlinarith
  have hd2 : (1/100 : ℝ) ≤ d^2 := by nlinarith
  have hden : (1/10000 : ℝ) ≤ b*c*d^2 := by nlinarith
  have hden0 : 0 < b*c*d^2 := by linarith
  have heq : ω ((T-a)/d)/(a*b*c*d^2)-ω ((T-e)/d)/(e*b*c*d^2) =
      (ω ((T-a)/d)/a-ω ((T-e)/d)/e)/(b*c*d^2) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, abs_div, abs_of_pos hden0]
  apply (div_le_iff₀ hden0).mpr
  calc _ ≤ 200*|a-e| := hmid
    _ ≤ _ := by nlinarith [mul_nonneg (abs_nonneg (a-e)) (sub_nonneg.mpr hden)]

/-- Page 51 display 5.17. The active E4 kernel is uniformly Lipschitz
in its a coordinate. -/
theorem four_exponent_kernel_coordinate_a {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε s a b c d e : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hr1 : lowerFourRegion ε a b c d) (hr2 : lowerFourRegion ε e b c d)
    (hu : 1 ≤ (s-a-b-c-d)/d) (hv : 1 ≤ (s-e-b-c-d)/d) :
    |fourExponentKernel ω ε s a b c d - fourExponentKernel ω ε s e b c d| ≤
      2000000 * |a-e| := by
  obtain ⟨hd, hdc, hcb, hba, _, _⟩ := four_density_region_box hε hε8 hr1
  obtain ⟨_, hdc', hcb', hba', _, _⟩ := four_density_region_box hε hε8 hr2
  have ha : (1/10 : ℝ) ≤ a := by linarith
  have hb : (1/10 : ℝ) ≤ b := by linarith
  have hc : (1/10 : ℝ) ≤ c := by linarith
  have he : (1/10 : ℝ) ≤ e := by linarith
  have harg1 : (s-b-c-d-a)/d = (s-a-b-c-d)/d := by ring
  have harg2 : (s-b-c-d-e)/d = (s-e-b-c-d)/d := by ring
  have h := four_exponent_density_coordinate_outer (T := s-b-c-d) hω hz ha he hb hc hd
    (by simpa only [harg1] using hu) (by simpa only [harg2] using hv)
  have hden1 : a*b*c*d^2 = a*b*c*d^2 := by ring
  have hden2 : e*b*c*d^2 = e*b*c*d^2 := by ring
  simpa only [fourExponentKernel, if_pos hr1, if_pos hr2,
    if_neg (not_lt.mpr hu), if_neg (not_lt.mpr hv), harg1, harg2, hden1, hden2] using h

/-- Page 51 display 5.17. The active E4 kernel is uniformly Lipschitz
in its b coordinate. -/
theorem four_exponent_kernel_coordinate_b {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε s a b c d e : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hr1 : lowerFourRegion ε a b c d) (hr2 : lowerFourRegion ε a e c d)
    (hu : 1 ≤ (s-a-b-c-d)/d) (hv : 1 ≤ (s-a-e-c-d)/d) :
    |fourExponentKernel ω ε s a b c d - fourExponentKernel ω ε s a e c d| ≤
      2000000 * |b-e| := by
  obtain ⟨hd, hdc, hcb, hba, _, _⟩ := four_density_region_box hε hε8 hr1
  obtain ⟨_, hdc', hcb', hba', _, _⟩ := four_density_region_box hε hε8 hr2
  have ha : (1/10 : ℝ) ≤ a := by linarith
  have hb : (1/10 : ℝ) ≤ b := by linarith
  have hc : (1/10 : ℝ) ≤ c := by linarith
  have he : (1/10 : ℝ) ≤ e := by linarith
  have harg1 : (s-a-c-d-b)/d = (s-a-b-c-d)/d := by ring
  have harg2 : (s-a-c-d-e)/d = (s-a-e-c-d)/d := by ring
  have h := four_exponent_density_coordinate_outer (T := s-a-c-d) hω hz hb he ha hc hd
    (by simpa only [harg1] using hu) (by simpa only [harg2] using hv)
  have hden1 : b*a*c*d^2 = a*b*c*d^2 := by ring
  have hden2 : e*a*c*d^2 = a*e*c*d^2 := by ring
  simpa only [fourExponentKernel, if_pos hr1, if_pos hr2,
    if_neg (not_lt.mpr hu), if_neg (not_lt.mpr hv), harg1, harg2, hden1, hden2] using h

/-- Page 51 display 5.17. The active E4 kernel is uniformly Lipschitz
in its c coordinate. -/
theorem four_exponent_kernel_coordinate_c {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε s a b c d e : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hr1 : lowerFourRegion ε a b c d) (hr2 : lowerFourRegion ε a b e d)
    (hu : 1 ≤ (s-a-b-c-d)/d) (hv : 1 ≤ (s-a-b-e-d)/d) :
    |fourExponentKernel ω ε s a b c d - fourExponentKernel ω ε s a b e d| ≤
      2000000 * |c-e| := by
  obtain ⟨hd, hdc, hcb, hba, _, _⟩ := four_density_region_box hε hε8 hr1
  obtain ⟨_, hdc', hcb', hba', _, _⟩ := four_density_region_box hε hε8 hr2
  have ha : (1/10 : ℝ) ≤ a := by linarith
  have hb : (1/10 : ℝ) ≤ b := by linarith
  have hc : (1/10 : ℝ) ≤ c := by linarith
  have he : (1/10 : ℝ) ≤ e := by linarith
  have harg1 : (s-a-b-d-c)/d = (s-a-b-c-d)/d := by ring
  have harg2 : (s-a-b-d-e)/d = (s-a-b-e-d)/d := by ring
  have h := four_exponent_density_coordinate_outer (T := s-a-b-d) hω hz hc he ha hb hd
    (by simpa only [harg1] using hu) (by simpa only [harg2] using hv)
  have hden1 : c*a*b*d^2 = a*b*c*d^2 := by ring
  have hden2 : e*a*b*d^2 = a*b*e*d^2 := by ring
  simpa only [fourExponentKernel, if_pos hr1, if_pos hr2,
    if_neg (not_lt.mpr hu), if_neg (not_lt.mpr hv), harg1, harg2, hden1, hden2] using h

#print axioms four_exponent_density_coordinate_outer
#print axioms four_exponent_kernel_coordinate_a
#print axioms four_exponent_kernel_coordinate_b
#print axioms four_exponent_kernel_coordinate_c
end LeanLab.BHP1997.LowerShortC165
