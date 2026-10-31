import LeanLab.RieselVaughan1983.Lemma3Weighted

/-! The partial summation identity on page 52 after equation 3.13.
AI wrote the Lean code. Binary Goldbach is OPEN. -/
namespace LeanLab.RieselVaughan1983.Lemma3
open Real Finset MeasureTheory
open LeanLab.RieselVaughan1983.Lemma2
noncomputable section

lemma sum_from_zero (f : ℕ → ℝ) (hf : f 0 = 0) (x : ℝ) :
    ∑ q ∈ Icc 0 ⌊x⌋₊, f q = ∑ q ∈ Icc 1 ⌊x⌋₊, f q := by
  rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons, hf, zero_add,
    ← Icc_add_one_left_eq_Ioc]
  rfl

lemma kernel_hasDerivAt (z t : ℝ) (hz : 1 ≤ z) (ht : t ∈ Set.Icc 1 z) :
    HasDerivAt (fun u : ℝ => z / (z + u)) (-z / (z + t) ^ 2) t := by
  have hzt : z + t ≠ 0 := by linarith [ht.1]
  have h := (hasDerivAt_const t z).div ((hasDerivAt_const t z).add (hasDerivAt_id t)) hzt
  change HasDerivAt (fun u : ℝ => z / (z + u))
    ((0 * (z + t) - z * (0 + 1)) / (z + t) ^ 2) t at h
  simpa only [zero_mul, zero_add, mul_one, zero_sub] using h

lemma kernel_deriv_integrable (z : ℝ) (hz : 1 ≤ z) :
    IntegrableOn (deriv (fun u : ℝ => z / (z + u))) (Set.Icc 1 z) := by
  have hc : ContinuousOn (fun t : ℝ => -z / (z + t) ^ 2) (Set.Icc 1 z) := by
    apply continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
    intro t ht
    exact pow_ne_zero 2 (by linarith [ht.1] : z + t ≠ 0)
  have hi : IntegrableOn (fun t : ℝ => -z / (z + t) ^ 2) (Set.Icc 1 z) :=
    hc.integrableOn_compact isCompact_Icc
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (kernel_hasDerivAt z t hz ht).deriv.symm

/-- The exact identity displayed before equation 3.15. -/
theorem S2_partial_summation (z : ℝ) (hz : 1 ≤ z) :
    S2 z = S z / 2 + ∫ u in Set.Ioc 1 z, z * S u / (z + u) ^ 2 := by
  have hz0 : 0 < z := by linarith
  have h := sum_mul_eq_sub_integral_mul₀ (fun q => sieveCoeff q) (by simp) z
    (fun t ht => (kernel_hasDerivAt z t hz ht).differentiableAt)
    (kernel_deriv_integrable z hz)
  have hleft : (∑ q ∈ Icc 0 ⌊z⌋₊, (z / (z + (q : ℝ))) * sieveCoeff q) = S2 z := by
    rw [sum_from_zero _ (by simp)]
    apply sum_congr rfl
    intro q hq
    have hden : z + (q : ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring
  have hright : (∫ t in Set.Ioc 1 z,
      deriv (fun u : ℝ => z / (z + u)) t * ∑ q ∈ Icc 0 ⌊t⌋₊, sieveCoeff q) =
      -(∫ t in Set.Ioc 1 z, z * S t / (z + t) ^ 2) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [(kernel_hasDerivAt z t hz ⟨ht.1.le, ht.2⟩).deriv, sum_from_zero _ (by simp)]
    unfold S
    ring
  rw [hleft, sum_from_zero _ (by simp), hright] at h
  have he : z / (z + z) = (1 / 2 : ℝ) := by field_simp; ring
  rw [he] at h
  simpa only [S, div_eq_mul_inv, one_mul, mul_comm, sub_neg_eq_add] using h

end
end LeanLab.RieselVaughan1983.Lemma3

#print axioms LeanLab.RieselVaughan1983.Lemma3.sum_from_zero
#print axioms LeanLab.RieselVaughan1983.Lemma3.kernel_hasDerivAt
#print axioms LeanLab.RieselVaughan1983.Lemma3.kernel_deriv_integrable
#print axioms LeanLab.RieselVaughan1983.Lemma3.S2_partial_summation
