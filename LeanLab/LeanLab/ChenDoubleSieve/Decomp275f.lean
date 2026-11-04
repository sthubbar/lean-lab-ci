import LeanLab.ChenDoubleSieve.Decomp275e
import LeanLab.ChenDoubleSieve.KCertificate

/-!
A third certified scalar coefficient in Wu 2004 Theorem 2.
Source: https://arxiv.org/pdf/0705.1652, page 41 equation 10.11 and page 42.
AI wrote the Lean code. Binary Goldbach is open.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Real Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task275.Thm2Scalar

/-- The uniform partition after the substitution u equals one minus t in F10. -/
def kNodeQ (j : ℕ) : ℚ := 359 / 500 + j * (221 / 250 - 359 / 500) / 1024

/-- The existing directed K upper panel at the F10 parameters. -/
def kUpperCell (j : ℕ) : ℚ := Wu04JCertificate.up
  (Wu04KCertificate.upperPanelQ (kNodeQ j) (kNodeQ (j + 1)) (500 / 141))

/-- An exact rational certificate for the printed F10 upper bound. -/
theorem F10_certificate :
    8 * (∑ j ∈ range 1024, kUpperCell j : ℚ) ≤ 5468377 / 1000000 := by
  decide +kernel

/-- The actual transformed K integral is bounded by the rational upper cells. -/
theorem F10_K_upper :
    (∫ t in (359 / 500 : ℝ)..(221 / 250 : ℝ),
      log ((500 / 141 : ℝ) * t - 1) / (t * (1 - t))) ≤
      ((∑ j ∈ range 1024, kUpperCell j : ℚ) : ℝ) := by
  let x : ℕ → ℝ := fun j => (kNodeQ j : ℝ)
  have hx (j : ℕ) : x j = 359 / 500 + (j : ℝ) * 83 / 512000 := by
    simp [x, kNodeQ]
    ring
  have hxp (j : ℕ) (hj : j < 1024) :
      0 < x j ∧ x j ≤ x (j + 1) ∧ x (j + 1) < 1 ∧
        1 ≤ (500 / 141 : ℝ) * x j - 1 := by
    rw [hx j, hx (j + 1)]
    push_cast
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hj1 : (j : ℝ) + 1 ≤ 1024 := by exact_mod_cast Nat.succ_le_of_lt hj
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hp := (Wu04Panels.K_partition_arithmetic 16 1024 x
    (by norm_num : (0 : ℝ) < 500 / 141) hxp).2
  have hcell (j : ℕ) :
      Wu04Panels.KUpper 16 (x j) (x (j + 1)) (500 / 141) ≤ (kUpperCell j : ℝ) := by
    have h : (Wu04KCertificate.upperPanelQ (kNodeQ j) (kNodeQ (j + 1))
        (500 / 141) : ℝ) ≤ (kUpperCell j : ℝ) := by
      exact_mod_cast Wu04JCertificate.le_up
        (Wu04KCertificate.upperPanelQ (kNodeQ j) (kNodeQ (j + 1)) (500 / 141))
    simpa [kUpperCell, Wu04KCertificate.upperPanelQ, Wu04KCertificate.wLowerQ,
      Wu04KCertificate.wUpperQ, Wu04Panels.KUpper, Wu04Panels.KWLower,
      Wu04Panels.KWUpper, x] using h
  have hx0 : x 0 = (359 / 500 : ℝ) := by norm_num [x, kNodeQ]
  have hxm : x 1024 = (221 / 250 : ℝ) := by norm_num [x, kNodeQ]
  rw [hx0, hxm] at hp
  exact hp.trans (by simpa only [Rat.cast_sum] using
    (sum_le_sum (fun j (_ : j ∈ range 1024) => hcell j)))

/-- The substitution u equals one minus t connects F10 to the certified K integral. -/
theorem F10_substitution :
    (∫ t in kappa2..sigma2, log (1 / sigma2 - 1 - t / sigma2) / (t * (1 - t))) =
      ∫ u in (359 / 500 : ℝ)..(221 / 250 : ℝ),
        log ((500 / 141 : ℝ) * u - 1) / (u * (1 - u)) := by
  have hlog (t : ℝ) : 1 / sigma2 - 1 - t / sigma2 = (500 / 141 : ℝ) * (1 - t) - 1 := by
    norm_num [sigma2]
    ring
  calc
    _ = ∫ t in kappa2..sigma2,
        (fun u : ℝ => log ((500 / 141 : ℝ) * u - 1) / (u * (1 - u))) (1 - t) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp
      rw [hlog t]
      congr 1
      ring
    _ = ∫ u in (1 - sigma2)..(1 - kappa2),
        log ((500 / 141 : ℝ) * u - 1) / (u * (1 - u)) :=
      intervalIntegral.integral_comp_sub_left
        (fun u : ℝ => log ((500 / 141 : ℝ) * u - 1) / (u * (1 - u))) 1
    _ = _ := by norm_num [kappa2, sigma2]

/-- The actual F10 integral satisfies its printed upper bound without an analytic input. -/
theorem F10_upper (F f ω : ℝ → ℝ) : integralTerms F f ω 9 ≤ 5.468377 := by
  change 8 * (∫ t in kappa2..sigma2,
    log (1 / sigma2 - 1 - t / sigma2) / (t * (1 - t))) ≤ 5.468377
  rw [F10_substitution]
  have hc : 8 * ((∑ j ∈ range 1024, kUpperCell j : ℚ) : ℝ) ≤ 5.468377 := by
    have hq : ((8 * (∑ j ∈ range 1024, kUpperCell j) : ℚ) : ℝ) ≤
        ((5468377 / 1000000 : ℚ) : ℝ) := Rat.cast_le.mpr F10_certificate
    convert hq using 1 <;> push_cast <;> norm_num
  exact (mul_le_mul_of_nonneg_left F10_K_upper (by norm_num : (0 : ℝ) ≤ 8)).trans hc

end LeanLab.ChenDoubleSieve.Task275.Thm2Scalar
