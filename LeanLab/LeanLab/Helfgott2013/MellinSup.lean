/-
Actual smoothing sup bounds in Helfgott, arXiv:1312.7748v2, display 7.19 on page 60.
AI wrote this Lean code, OpenAI Codex, task31, 2026-10-22.
Binary Goldbach remains open.
-/
import LeanLab.Helfgott2013.MellinL2
import LeanLab.Helfgott2013.EtaTwoMoments
import LeanLab.Helfgott2013.SectionSevenSup

open Real MeasureTheory Set
open scoped Interval

namespace LeanLab.Helfgott2013.MellinSup
open EtaTwo EtaTwoMoments GaussianL2 MellinL2

/-- The certified raw logarithm bound also bounds the positive logarithm factor. -/
theorem phi_posLog_sup {t : ℝ} (ht : 0 ≤ t) :
    |phi t * Real.posLog t| ≤ (0.381157 : ℝ) := by
  have hn : 0 ≤ phi t * Real.posLog t := by
    have := Real.posLog_nonneg (x := t)
    unfold phi
    positivity
  rw [abs_of_nonneg hn]
  by_cases h1 : 1 ≤ t
  · rw [Real.posLog_eq_log (by rwa [abs_of_nonneg ht])]
    exact SectionSevenSup.phi_log_sup h1
  · rw [(Real.posLog_eq_zero_iff t).mpr (by rw [abs_of_nonneg ht]; linarith)]
    norm_num

#print axioms phi_posLog_sup

/-- The actual Mellin smoothing is nonnegative and has the paper's uniform sup bound. -/
theorem mellin_sup (w : ℝ) : 0 ≤ mellin w ∧ |mellin w| ≤ (1.414 : ℝ) := by
  have he (t : ℝ) : 0 ≤ etaTwo t := by
    unfold etaTwo
    split_ifs <;> positivity
  have hp (t : ℝ) : 0 ≤ phi t := by unfold phi; positivity
  have htne : ∀ t ∈ Icc (1 / 4 : ℝ) 1, t ≠ 0 := by
    intro t ht
    linarith [ht.1]
  have hpc : Continuous phi := by unfold phi; fun_prop
  have hc : ContinuousOn (fun t : ℝ => etaTwo t * phi (w / t) / t)
      (Icc (1 / 4 : ℝ) 1) :=
    (continuousOn_etaTwo.mul (hpc.comp_continuousOn
      (continuousOn_const.div continuousOn_id htne))).div continuousOn_id htne
  have hd : ContinuousOn (fun t : ℝ => etaTwo t / t * (2 / Real.exp 1))
      (Icc (1 / 4 : ℝ) 1) :=
    (continuousOn_etaTwo.div continuousOn_id htne).mul_const _
  have hv (u : ℝ) : phi u ≤ 2 / Real.exp 1 := by
    unfold phi
    rw [neg_div]
    calc
      _ ≤ 2 * Real.exp (-1) := LeanLab.Helfgott2013.phi_sup u
      _ = 2 / Real.exp 1 := by rw [Real.exp_neg]; rfl
  have hn : 0 ≤ mellin w := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    exact div_nonneg (mul_nonneg (he t) (hp _)) ht0.le
  refine ⟨hn, ?_⟩
  rw [abs_of_nonneg hn]
  calc
    _ ≤ ∫ t in (1 / 4 : ℝ)..1, etaTwo t / t * (2 / Real.exp 1) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hc.intervalIntegrable_of_Icc (by norm_num)) (hd.intervalIntegrable_of_Icc (by norm_num))
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      convert mul_le_mul_of_nonneg_left (hv (w / t)) (div_nonneg (he t) ht0.le) using 1 <;> ring
    _ = 4 * Real.log 2 ^ 2 * (2 / Real.exp 1) := by
      rw [intervalIntegral.integral_mul_const, etaTwo_div_moment_compact]
    _ ≤ 1.414 := LeanLab.Helfgott2013.etaStar_sup

#print axioms mellin_sup

/-- The actual weighted smoothing sup bound in display 7.19. -/
theorem mellin_posLog_sup {w : ℝ} (hw : 0 ≤ w) :
    |mellin w * Real.posLog w| ≤ (0.732513 : ℝ) := by
  have he (t : ℝ) : 0 ≤ etaTwo t := by
    unfold etaTwo
    split_ifs <;> positivity
  have hp (t : ℝ) : 0 ≤ phi t := by unfold phi; positivity
  have htne : ∀ t ∈ Icc (1 / 4 : ℝ) 1, t ≠ 0 := by
    intro t ht
    linarith [ht.1]
  have hpc : Continuous phi := by unfold phi; fun_prop
  have hc : ContinuousOn (fun t : ℝ => etaTwo t * phi (w / t) / t * Real.posLog w)
      (Icc (1 / 4 : ℝ) 1) :=
    ((continuousOn_etaTwo.mul (hpc.comp_continuousOn
      (continuousOn_const.div continuousOn_id htne))).div continuousOn_id htne).mul_const _
  have hd : ContinuousOn (fun t : ℝ => etaTwo t / t * 0.381157)
      (Icc (1 / 4 : ℝ) 1) :=
    (continuousOn_etaTwo.div continuousOn_id htne).mul_const _
  have hn : 0 ≤ mellin w * Real.posLog w :=
    mul_nonneg (mellin_sup w).1 Real.posLog_nonneg
  rw [abs_of_nonneg hn]
  calc
    _ = ∫ t in (1 / 4 : ℝ)..1, etaTwo t * phi (w / t) / t * Real.posLog w := by
      rw [intervalIntegral.integral_mul_const]
      rfl
    _ ≤ ∫ t in (1 / 4 : ℝ)..1, etaTwo t / t * 0.381157 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hc.intervalIntegrable_of_Icc (by norm_num)) (hd.intervalIntegrable_of_Icc (by norm_num))
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hmono : Real.posLog w ≤ Real.posLog (w / t) :=
        Real.posLog_le_posLog (by linarith) ((le_div_iff₀ ht0).mpr (by nlinarith [ht.2]))
      have h1 := mul_le_mul_of_nonneg_left hmono (hp (w / t))
      have h2 : phi (w / t) * Real.posLog (w / t) ≤ 0.381157 :=
        (le_abs_self _).trans (phi_posLog_sup (div_nonneg hw ht0.le))
      convert mul_le_mul_of_nonneg_left (h1.trans h2) (div_nonneg (he t) ht0.le) using 1 <;> ring
    _ = 4 * Real.log 2 ^ 2 * 0.381157 := by
      rw [intervalIntegral.integral_mul_const, etaTwo_div_moment_compact]
    _ ≤ 0.732513 :=
      (mul_le_mul_of_nonneg_right LeanLab.Helfgott2013.eta2_t_norm.1 (by norm_num)).trans
        LeanLab.Helfgott2013.eta2_t_norm.2

#print axioms mellin_posLog_sup

/-- The exact weighted Gaussian sup in square root form. -/
theorem phi_mul_sup (u : ℝ) :
    |phi u * u| ≤ Real.sqrt (27 * Real.exp (-3)) := by
  have he : (phi u * u) ^ 2 = u ^ 6 * Real.exp (-u ^ 2) := by
    unfold phi
    simp only [mul_pow]
    rw [← Real.exp_nat_mul]
    ring_nf
  have hs : |phi u * u| ^ 2 ≤ 27 * Real.exp (-3) := by
    rw [sq_abs, he]
    exact LeanLab.Helfgott2013.phi_t_sup u
  exact (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr hs

#print axioms phi_mul_sup

/-- Transfer the weighted Gaussian sup using eta2 mass one. -/
theorem mellin_mul_sup {w : ℝ} (hw : 0 ≤ w) :
    |mellin w * w| ≤ Real.sqrt (27 * Real.exp (-3)) := by
  have he (t : ℝ) : 0 ≤ etaTwo t := by
    unfold etaTwo
    split_ifs <;> positivity
  have htne : ∀ t ∈ Icc (1 / 4 : ℝ) 1, t ≠ 0 := by
    intro t ht
    linarith [ht.1]
  have hp : Continuous phi := by unfold phi; fun_prop
  have hc : ContinuousOn (fun t : ℝ => etaTwo t * phi (w / t) / t * w)
      (Icc (1 / 4 : ℝ) 1) :=
    ((continuousOn_etaTwo.mul (hp.comp_continuousOn
      (continuousOn_const.div continuousOn_id htne))).div continuousOn_id htne).mul_const _
  have hd : ContinuousOn (fun t : ℝ => etaTwo t * Real.sqrt (27 * Real.exp (-3)))
      (Icc (1 / 4 : ℝ) 1) := continuousOn_etaTwo.mul_const _
  have hmass : (∫ t in (1 / 4 : ℝ)..1, etaTwo t) = 1 := by
    have h := etaTwo_moment_compact 0
    norm_num at h
    exact h
  rw [abs_of_nonneg (mul_nonneg (mellin_sup w).1 hw)]
  calc
    _ = ∫ t in (1 / 4 : ℝ)..1, etaTwo t * phi (w / t) / t * w := by
      rw [intervalIntegral.integral_mul_const]
      rfl
    _ ≤ ∫ t in (1 / 4 : ℝ)..1, etaTwo t * Real.sqrt (27 * Real.exp (-3)) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hc.intervalIntegrable_of_Icc (by norm_num)) (hd.intervalIntegrable_of_Icc (by norm_num))
      intro t _
      have hu : phi (w / t) * (w / t) ≤ Real.sqrt (27 * Real.exp (-3)) :=
        (le_abs_self _).trans (phi_mul_sup (w / t))
      convert mul_le_mul_of_nonneg_left hu (he t) using 1 <;> ring
    _ = _ := by rw [intervalIntegral.integral_mul_const, hmass, one_mul]

#print axioms mellin_mul_sup

end LeanLab.Helfgott2013.MellinSup
