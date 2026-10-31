import LeanLab.RieselVaughan1983.Lemma3PartialSummation

/-! The integrated error bound in equation 3.16 on page 52.
AI wrote the Lean code. Binary Goldbach is OPEN. -/
namespace LeanLab.RieselVaughan1983.Lemma3
open Real Finset MeasureTheory
open LeanLab.RieselVaughan1983.Lemma2
noncomputable section

def D (u : ℝ) : ℝ := 2 * Ctw * S u - M u

lemma A5_pos : 0 < A5 := by
  unfold A5
  have h := one_le_H
  have hC := Ctw_pos
  positivity

lemma kernel_continuousOn (z : ℝ) (hz : 1 ≤ z) :
    ContinuousOn (fun u : ℝ => z / (z + u) ^ 2) (Set.Icc 1 z) := by
  apply continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
  intro u hu
  exact pow_ne_zero 2 (by linarith [hu.1] : z + u ≠ 0)

lemma kernel_S_integrable (z : ℝ) (hz : 1 ≤ z) :
    IntegrableOn (fun u : ℝ => z * S u / (z + u) ^ 2) (Set.Icc 1 z) := by
  have hk : IntegrableOn (fun u : ℝ => z / (z + u) ^ 2) (Set.Icc 1 z) :=
    (kernel_continuousOn z hz).integrableOn_compact isCompact_Icc
  have h := integrableOn_mul_sum_Icc (fun q => sieveCoeff q) (m := 1)
    (by norm_num : (0 : ℝ) ≤ 1) hk
  convert h using 1
  funext u
  unfold S
  ring

lemma M_continuousOn (z : ℝ) : ContinuousOn M (Set.Icc 1 z) := by
  have hl : ContinuousOn Real.log (Set.Icc 1 z) := by
    apply Real.continuousOn_log.mono
    intro u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [hu.1]
  change ContinuousOn (fun u : ℝ => Real.log u ^ 2 + A3 * Real.log u + A4) (Set.Icc 1 z)
  exact ((hl.pow 2).add (continuousOn_const.mul hl)).add continuousOn_const

lemma kernel_M_integrable (z : ℝ) (hz : 1 ≤ z) :
    IntegrableOn (fun u : ℝ => z * M u / (z + u) ^ 2) (Set.Icc 1 z) := by
  have h : ContinuousOn (fun u : ℝ => z / (z + u) ^ 2 * M u) (Set.Icc 1 z) :=
    (kernel_continuousOn z hz).mul (M_continuousOn z)
  have hi : IntegrableOn (fun u : ℝ => z / (z + u) ^ 2 * M u) (Set.Icc 1 z) :=
    h.integrableOn_compact isCompact_Icc
  convert hi using 1
  funext u
  ring

lemma kernel_D_integrable (z : ℝ) (hz : 1 ≤ z) :
    IntegrableOn (fun u : ℝ => z * D u / (z + u) ^ 2) (Set.Icc 1 z) := by
  have h := ((kernel_S_integrable z hz).const_mul (2 * Ctw)).sub (kernel_M_integrable z hz)
  apply h.congr
  filter_upwards [] with u
  dsimp
  unfold D
  ring

lemma error_decomposition (z : ℝ) (hz : 1 ≤ z) :
    2 * Ctw * S2 z - M z / 2 - (∫ u in Set.Ioc 1 z, z * M u / (z + u) ^ 2) =
      D z / 2 + ∫ u in Set.Ioc 1 z, z * D u / (z + u) ^ 2 := by
  have hS := S2_partial_summation z hz
  have he : (∫ u in Set.Ioc 1 z, z * D u / (z + u) ^ 2) =
      (2 * Ctw) * (∫ u in Set.Ioc 1 z, z * S u / (z + u) ^ 2) -
        (∫ u in Set.Ioc 1 z, z * M u / (z + u) ^ 2) := by
    have hfun : (fun u : ℝ => z * D u / (z + u) ^ 2) =
        (fun u => (2 * Ctw) * (z * S u / (z + u) ^ 2) - z * M u / (z + u) ^ 2) := by
      funext u; unfold D; ring
    have his : IntegrableOn (fun u : ℝ => (2 * Ctw) * (z * S u / (z + u) ^ 2))
        (Set.Icc 1 z) := (kernel_S_integrable z hz).const_mul (2 * Ctw)
    rw [hfun, integral_sub
      (his.mono_set Set.Ioc_subset_Icc_self)
      ((kernel_M_integrable z hz).mono_set Set.Ioc_subset_Icc_self), integral_const_mul]
  rw [he, hS]
  unfold D
  ring

lemma power_integral (z : ℝ) (hz : 1 ≤ z) :
    (∫ u in Set.Ioc 1 z, u ^ (-(1 / 3 : ℝ))) =
      3 / 2 * ((z : ℝ) ^ (2 / 3 : ℝ) - 1) := by
  rw [← intervalIntegral.integral_of_le hz, integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 3 : ℝ)))]
  norm_num
  ring

lemma kernel_error_bound (z u : ℝ) (hz : 1 ≤ z) (hu : u ∈ Set.Icc 1 z) :
    |z * D u / (z + u) ^ 2| ≤ (A5 / z) * u ^ (-(1 / 3 : ℝ)) := by
  have hz0 : 0 < z := by linarith
  have hu0 : 0 < u := by linarith [hu.1]
  have hD : |D u| ≤ A5 * u ^ (-(1 / 3 : ℝ)) := by
    simpa only [D, M, sub_add_eq_sub_sub] using (lemma2_unconditional u hu.1).le
  have hk : z / (z + u) ^ 2 ≤ 1 / z := by
    apply (div_le_div_iff₀ (by positivity) hz0).mpr
    nlinarith
  rw [abs_div, abs_mul, abs_of_pos hz0, abs_of_nonneg (sq_nonneg (z + u))]
  calc _ = (z / (z + u) ^ 2) * |D u| := by ring
    _ ≤ (1 / z) * (A5 * u ^ (-(1 / 3 : ℝ))) :=
      mul_le_mul hk hD (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma kernel_error_integral_le (z : ℝ) (hz : 1 ≤ z) :
    |∫ u in Set.Ioc 1 z, z * D u / (z + u) ^ 2| ≤
      A5 / z * (3 / 2 * (z ^ (2 / 3 : ℝ) - 1)) := by
  have hc : ContinuousOn (fun u : ℝ => (A5 / z) * u ^ (-(1 / 3 : ℝ))) (Set.Icc 1 z) := by
    apply continuousOn_const.mul
    apply continuousOn_id.rpow_const
    intro u hu
    exact Or.inl (by change u ≠ 0; linarith [hu.1])
  have hi : IntegrableOn (fun u : ℝ => (A5 / z) * u ^ (-(1 / 3 : ℝ))) (Set.Ioc 1 z) :=
    (hc.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hd := ((kernel_D_integrable z hz).mono_set Set.Ioc_subset_Icc_self).norm
  calc _ ≤ ∫ u in Set.Ioc 1 z, |z * D u / (z + u) ^ 2| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun u : ℝ => z * D u / (z + u) ^ 2) (μ := volume.restrict (Set.Ioc 1 z))
    _ ≤ ∫ u in Set.Ioc 1 z, (A5 / z) * u ^ (-(1 / 3 : ℝ)) := by
        apply integral_mono_ae (by simpa only [Real.norm_eq_abs] using hd) hi
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        exact kernel_error_bound z u hz ⟨hu.1.le, hu.2⟩
    _ = _ := by rw [integral_const_mul, power_integral z hz]

/-- Equation 3.16. -/
theorem eq316 (z : ℝ) (hz : 1 ≤ z) :
    |2 * Ctw * S2 z - M z / 2 - (∫ u in Set.Ioc 1 z, z * M u / (z + u) ^ 2)| <
      2 * A5 * z ^ (-(1 / 3 : ℝ)) := by
  have hz0 : 0 < z := by linarith
  have hD : |D z| < A5 * z ^ (-(1 / 3 : ℝ)) := by
    simpa only [D, M, sub_add_eq_sub_sub] using lemma2_unconditional z hz
  have hp : z ^ (2 / 3 : ℝ) / z = z ^ (-(1 / 3 : ℝ)) := by
    calc z ^ (2 / 3 : ℝ) / z = z ^ (2 / 3 : ℝ) / z ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = z ^ ((2 / 3 : ℝ) - 1) := (Real.rpow_sub hz0 _ _).symm
      _ = _ := by norm_num
  rw [error_decomposition z hz]
  calc _ ≤ |D z / 2| + |∫ u in Set.Ioc 1 z, z * D u / (z + u) ^ 2| := abs_add_le _ _
    _ < A5 * z ^ (-(1 / 3 : ℝ)) / 2 +
        A5 / z * (3 / 2 * (z ^ (2 / 3 : ℝ) - 1)) := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact add_lt_add_of_lt_of_le (div_lt_div_of_pos_right hD (by norm_num)) (kernel_error_integral_le z hz)
    _ ≤ _ := by
      have he : A5 / z * (3 / 2 * (z ^ (2 / 3 : ℝ) - 1)) =
          3 / 2 * A5 * z ^ (-(1 / 3 : ℝ)) - 3 / 2 * A5 / z := by
        rw [← hp]; ring
      rw [he]
      have he2 : A5 * z ^ (-(1 / 3 : ℝ)) / 2 +
          (3 / 2 * A5 * z ^ (-(1 / 3 : ℝ)) - 3 / 2 * A5 / z) =
          2 * A5 * z ^ (-(1 / 3 : ℝ)) - (3 / 2) * (A5 / z) := by ring
      rw [he2]
      exact sub_le_self _ (mul_nonneg (by norm_num) (div_nonneg A5_pos.le hz0.le))

end
end LeanLab.RieselVaughan1983.Lemma3

#print axioms LeanLab.RieselVaughan1983.Lemma3.A5_pos
#print axioms LeanLab.RieselVaughan1983.Lemma3.kernel_continuousOn
#print axioms LeanLab.RieselVaughan1983.Lemma3.kernel_S_integrable
#print axioms LeanLab.RieselVaughan1983.Lemma3.M_continuousOn
#print axioms LeanLab.RieselVaughan1983.Lemma3.kernel_M_integrable
#print axioms LeanLab.RieselVaughan1983.Lemma3.kernel_D_integrable
#print axioms LeanLab.RieselVaughan1983.Lemma3.error_decomposition
#print axioms LeanLab.RieselVaughan1983.Lemma3.power_integral
#print axioms LeanLab.RieselVaughan1983.Lemma3.kernel_error_bound
#print axioms LeanLab.RieselVaughan1983.Lemma3.kernel_error_integral_le
#print axioms LeanLab.RieselVaughan1983.Lemma3.eq316
