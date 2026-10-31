import LeanLab.ChenDoubleSieve.SigmaCertificate

/-!
# Positivity and monotonicity of the sigma0 kernel

Source: https://arxiv.org/pdf/0705.1652, page 14, the definitions before Proposition 3.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Wu04Integral

/-- Sigma is nonnegative when the logarithm is nonnegative throughout the interval. -/
theorem sigma_nonneg {a b c : ℝ} (ha : 1 < a) (hab : a ≤ b) (hc : b - 1 ≤ c) :
    0 ≤ sigma a b c := by
  apply intervalIntegral.integral_nonneg hab
  intro t ht
  have ht1 : 0 < t - 1 := by linarith [ht.1]
  apply div_nonneg
  · apply Real.log_nonneg
    rw [le_div_iff₀ ht1]
    linarith [ht.2]
  · linarith [ht.1]

/-- Increasing c increases sigma on a fixed interval. -/
theorem sigma_mono_c {a b c d : ℝ} (ha : 1 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) :
    sigma a b c ≤ sigma a b d := by
  have hd : 0 < d := hc.trans_le hcd
  apply integral_mono_on hab (sigma_integrable ha hab hc) (sigma_integrable ha hab hd)
  intro t ht
  have ht1 : 0 < t - 1 := by linarith [ht.1]
  apply div_le_div_of_nonneg_right _ (by linarith [ht.1])
  exact log_le_log (div_pos hc ht1) (div_le_div_of_nonneg_right hcd ht1.le)

/-- Extending the integration interval adds a nonnegative tail. -/
theorem sigma_mono_right {a b d c : ℝ} (ha : 1 < a) (hab : a ≤ b) (hbd : b ≤ d)
    (hc : d - 1 ≤ c) : sigma a b c ≤ sigma a d c := by
  have hb : 1 < b := ha.trans_le hab
  have hc0 : 0 < c := by linarith
  have hi1 := sigma_integrable ha hab hc0
  have hi2 := sigma_integrable hb hbd hc0
  have hn := sigma_nonneg hb hbd hc
  unfold sigma at *
  rw [← integral_add_adjacent_intervals hi1 hi2]
  linarith

/-- Sigma 3 t+2 t+1 increases for t at least one. -/
theorem sigma_diagonal_mono : MonotoneOn (fun t : ℝ => sigma 3 (t + 2) (t + 1)) (Ici 1) := by
  intro t ht u hu htu
  change 1 ≤ t at ht
  change 1 ≤ u at hu
  have h1 := sigma_mono_c (a := 3) (b := t + 2) (c := t + 1) (d := u + 1)
    (by norm_num) (by linarith [ht]) (by linarith [ht]) (by linarith)
  have h2 := sigma_mono_right (a := 3) (b := t + 2) (d := u + 2) (c := u + 1)
    (by norm_num) (by linarith [ht]) (by linarith) (by linarith)
  exact h1.trans h2

/-- Sigma0 is nonnegative on the full integration range in Propositions 3 and 4. -/
theorem sigma0_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ sigma0 t := by
  have hn := sigma_nonneg (a := 3) (b := t + 2) (c := t + 1)
    (by norm_num) (by linarith) (by linarith)
  have hd : 0 < 1 - sigma 3 5 4 := by linarith [sigma_denominator_bounds.1]
  exact div_nonneg hn hd.le

/-- Sigma0 increases on the full integration range. -/
theorem sigma0_mono : MonotoneOn sigma0 (Ici 1) := by
  intro t ht u hu htu
  have hd : 0 ≤ 1 - sigma 3 5 4 := by linarith [sigma_denominator_bounds.1]
  exact div_le_div_of_nonneg_right (sigma_diagonal_mono ht hu htu) hd

/-- Sigma0 vanishes at the left endpoint. -/
theorem sigma0_one : sigma0 1 = 0 := by norm_num [sigma0, sigma]

/-- A rational enclosure of sigma0 at the right endpoint. -/
theorem sigma0_three_bounds : (4 / 21 : ℝ) ≤ sigma0 3 ∧ sigma0 3 ≤ 9 / 41 := by
  have hlo := sigma_3_5_4_bounds.1
  have hhi := sigma_3_5_4_bounds.2
  have hd : 0 < 1 - sigma 3 5 4 := by linarith
  norm_num only [sigma0, show (3 : ℝ) + 2 = 5 by norm_num, show (3 : ℝ) + 1 = 4 by norm_num]
  constructor
  · rw [le_div_iff₀ hd]; linarith
  · rw [div_le_iff₀ hd]; linarith

/-- A uniform rational interval for sigma0 on one to three. -/
theorem sigma0_bounds {t : ℝ} (ht : t ∈ Icc 1 3) :
    0 ≤ sigma0 t ∧ sigma0 t ≤ (9 / 41 : ℝ) := by
  exact ⟨sigma0_nonneg ht.1, (sigma0_mono ht.1 (by norm_num) ht.2).trans sigma0_three_bounds.2⟩

end LeanLab.ChenDoubleSieve.Wu04Integral

#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sigma_nonneg
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sigma_mono_c
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sigma_mono_right
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sigma_diagonal_mono
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sigma0_nonneg
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sigma0_mono
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sigma0_one
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sigma0_three_bounds
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sigma0_bounds
