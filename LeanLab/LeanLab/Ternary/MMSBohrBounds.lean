/-
P0028, arXiv 1610.02017, Lemma 4.3 items 2 and 4, pages 9 and 10.
The uniformity and restriction norm estimates for full integer smoothing.
The large frequency control of the averaging set remains an explicit hypothesis.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSMass

namespace LeanLab.Ternary.MMS

/-- The restriction norm for a finitely supported function on all integers. -/
noncomputable def intLq (f : ℤ →₀ ℝ) (q : ℝ) : ℝ :=
  (∫ γ in (0 : ℝ)..1, ‖intHat f γ‖ ^ q) ^ (1 / q)

/-- Integer transforms are continuous. -/
theorem continuous_intHat (f : ℤ →₀ ℝ) : Continuous (intHat f) := by
  unfold intHat e
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  fun_prop

/-- Pointwise Fourier domination controls the full integer restriction norm. -/
theorem intLq_mono (f g : ℤ →₀ ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hfg : ∀ γ : ℝ, ‖intHat g γ‖ ≤ ‖intHat f γ‖) : intLq g q ≤ intLq f q := by
  have hc (u : ℤ →₀ ℝ) : Continuous (fun γ : ℝ => ‖intHat u γ‖ ^ q) :=
    (continuous_intHat u).norm.rpow_const (fun _ => Or.inr hq)
  unfold intLq
  apply Real.rpow_le_rpow
  · exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun γ => Real.rpow_nonneg (norm_nonneg _) _)
  · exact intervalIntegral.integral_mono (by norm_num)
      ((hc g).intervalIntegrable 0 1) ((hc f).intervalIntegrable 0 1)
      (fun γ => Real.rpow_le_rpow (norm_nonneg _) (hfg γ) hq)
  · positivity

/-- Both smoothing multipliers lie in the unit interval. -/
theorem bohr_multiplier_bounds (B : Finset ℤ) (hB : B.Nonempty) (γ : ℝ) :
    0 ≤ ‖bohrMean B γ‖ ^ 2 ∧ ‖bohrMean B γ‖ ^ 2 ≤ 1 := by
  have h := bohrMean_norm_le_one B hB γ
  have hn := norm_nonneg (bohrMean B γ)
  constructor
  · positivity
  · nlinarith

/-- Smoothing and its complementary uniform part contract every Fourier value. -/
theorem intSmooth_fourier_contractions (B : Finset ℤ) (hB : B.Nonempty)
    (f : ℤ →₀ ℝ) (γ : ℝ) :
    ‖intHat (intSmooth B f) γ‖ ≤ ‖intHat f γ‖ ∧
    ‖intHat (f - intSmooth B f) γ‖ ≤ ‖intHat f γ‖ := by
  obtain ⟨hm0, hm1⟩ := bohr_multiplier_bounds B hB γ
  constructor
  · rw [intHat_smooth, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0]
    exact mul_le_of_le_one_right (norm_nonneg _) hm1
  · rw [intHat_uniform_part]
    have he : 1 - ((‖bohrMean B γ‖ ^ 2 : ℝ) : ℂ) =
        ((1 - ‖bohrMean B γ‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hm1)]
    exact mul_le_of_le_one_right (norm_nonneg _) (by linarith)

/-- Lemma 4.3 item 4 for every nonempty finite averaging set. -/
theorem intSmooth_restriction_bounds (B : Finset ℤ) (hB : B.Nonempty)
    (f : ℤ →₀ ℝ) {q : ℝ} (hq : 0 ≤ q) :
    intLq (intSmooth B f) q ≤ intLq f q ∧ intLq (f - intSmooth B f) q ≤ intLq f q := by
  exact ⟨intLq_mono f _ hq (fun γ => (intSmooth_fourier_contractions B hB f γ).1),
    intLq_mono f _ hq (fun γ => (intSmooth_fourier_contractions B hB f γ).2)⟩

/-- Before smoothing, the integer restriction norm is the interval restriction norm. -/
theorem intLq_intervalLift (N : ℕ) (f : ℕ → ℝ) (q : ℝ) :
    intLq (intervalLift N f) q = fhatLq N f q := by
  simp only [intLq, fhatLq, intHat_intervalLift]

/-- The elementary large frequency estimate in the proof of Lemma 4.3 item 2. -/
theorem one_sub_norm_sq_le (z : ℂ) : 1 - ‖z‖ ^ 2 ≤ 2 * ‖1 - z‖ := by
  have h := norm_sub_norm_le (1 : ℂ) z
  norm_num at h
  nlinarith [sq_nonneg (1 - ‖z‖)]

/-- Large frequency control of the mean gives the uniform bound in Lemma 4.3 item 2. -/
theorem intSmooth_uniform_bound (B : Finset ℤ) (hB : B.Nonempty)
    (f : ℤ →₀ ℝ) (N : ℕ) (δ : ℝ)
    (hf : ∀ γ : ℝ, ‖intHat f γ‖ ≤ 2 * N)
    (hlarge : ∀ γ : ℝ, δ * N ≤ ‖intHat f γ‖ → ‖1 - bohrMean B γ‖ ≤ δ / 4) :
    ∀ γ : ℝ, ‖intHat (f - intSmooth B f) γ‖ ≤ δ * N := by
  intro γ
  by_cases h : δ * N ≤ ‖intHat f γ‖
  · have hm := bohr_multiplier_bounds B hB γ
    have hfac : 1 - ‖bohrMean B γ‖ ^ 2 ≤ δ / 2 := by
      have := one_sub_norm_sq_le (bohrMean B γ)
      linarith [hlarge γ h]
    rw [intHat_uniform_part]
    have he : 1 - ((‖bohrMean B γ‖ ^ 2 : ℝ) : ℂ) =
        ((1 - ‖bohrMean B γ‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hm.2)]
    calc ‖intHat f γ‖ * (1 - ‖bohrMean B γ‖ ^ 2)
        ≤ (2 * N) * (1 - ‖bohrMean B γ‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (hf γ) (sub_nonneg.mpr hm.2)
      _ ≤ (2 * N) * (δ / 2) := mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = δ * N := by ring
  · exact (intSmooth_fourier_contractions B hB f γ).2.trans (lt_of_not_ge h).le

end LeanLab.Ternary.MMS
