/-
Weighted convolution step of the coordinate substitution on page 29 display 7.21.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Archimedean

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory Filter Topology

/-- LEAF. Page 29 display 7.21. The cutoff removes the singularity of the complex power. -/
theorem continuous_cutoff_cpow107 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    {N : ℝ} (hN : 0 < N) (ρ : ℂ) :
    Continuous (fun u : ℝ => (ϕ (u / N) : ℂ) * (u : ℂ) ^ (ρ - 1)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  by_cases hu : u = 0
  · subst u
    have hz : (fun u : ℝ => (ϕ (u / N) : ℂ) * (u : ℂ) ^ (ρ - 1)) =ᶠ[𝓝 0]
        (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds (by positivity : (0 : ℝ) < N / 5)] with u hu
      have hf : ϕ (u / N) = 0 := by
        by_contra hn
        have hs := (hϕ.supp (subset_tsupport ϕ hn)).1
        have : u / N < 1 / 5 := (div_lt_iff₀ hN).mpr (by linarith)
        linarith
      simp [hf]
    rw [continuousAt_congr hz]
    exact continuousAt_const
  · exact (Complex.continuous_ofReal.comp (hϕ.smooth.continuous.comp
      (continuous_id.div_const N))).continuousAt.mul
        (Complex.continuousAt_ofReal_cpow_const u (ρ - 1) (Or.inr hu))

/-- LEAF. Page 29 display 7.21. The cutoff complex power has compact support. -/
theorem compact_cutoff_cpow107 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    {N : ℝ} (hN : 0 < N) (ρ : ℂ) :
    HasCompactSupport (fun u : ℝ => (ϕ (u / N) : ℂ) * (u : ℂ) ^ (ρ - 1)) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := N / 5) (b := 4 * N / 5))
  intro u hu
  have hf : ϕ (u / N) = 0 := by
    by_contra hn
    have hs := hϕ.supp (subset_tsupport ϕ hn)
    apply hu
    constructor
    · have := (lt_div_iff₀ hN).mp hs.1
      linarith
    · have := (div_lt_iff₀ hN).mp hs.2
      linarith
  simp [hf]

/-- LEAF. Page 29 display 7.21. Fubini and translation give the weighted convolution identity. -/
theorem weighted_convolution107 (f g h : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ u : ℝ, ∫ w : ℝ, f u * g w * h (u + w)) =
      ∫ v : ℝ, (∫ u : ℝ, f u * g (v - u)) * h v := by
  let H : ℝ × ℝ → ℂ := fun p => f p.1 * g p.2 * h (p.1 + p.2)
  have hcont : Continuous H := by fun_prop
  have hcomp : HasCompactSupport H := by
    apply HasCompactSupport.intro (hfc.prod hgc)
    intro p hp
    change p ∉ tsupport f ×ˢ tsupport g at hp
    simp only [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · simp [H, image_eq_zero_of_notMem_tsupport hp]
    · simp [H, image_eq_zero_of_notMem_tsupport hp]
  have hi : Integrable H := hcont.integrable_of_hasCompactSupport hcomp
  have hk := (measurePreserving_prod_neg_add volume volume).integrable_comp_of_integrable hi
  have hk' : Integrable (fun p : ℝ × ℝ => f p.1 * g (p.2 - p.1) * h p.2) := by
    convert hk using 1
    ext p
    simp [H, sub_eq_add_neg, add_comm]
  calc
    _ = ∫ u : ℝ, ∫ v : ℝ, f u * g (v - u) * h v := by
      apply integral_congr_ae
      filter_upwards [] with u
      simpa using (integral_add_left_eq_self (fun v : ℝ => f u * g (v - u) * h v) u)
    _ = ∫ v : ℝ, ∫ u : ℝ, f u * g (v - u) * h v := integral_integral_swap hk'
    _ = _ := by simp only [integral_mul_const]

/-- LEAF. Page 29 display 7.21. Positive supports give the triangular integration region. -/
theorem positive_convolution107 (f g h : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf0 : ∀ u : ℝ, u ≤ 0 → f u = 0) (hg0 : ∀ u : ℝ, u ≤ 0 → g u = 0) :
    (∫ u in Set.Ioi (0 : ℝ), ∫ w in Set.Ioi (0 : ℝ), f u * g w * h (u + w)) =
      ∫ v in Set.Ioi (0 : ℝ), (∫ u in (0 : ℝ)..v, f u * g (v - u)) * h v := by
  have hinner (v : ℝ) (hv : 0 < v) :
      (∫ u : ℝ, f u * g (v - u)) = ∫ u in (0 : ℝ)..v, f u * g (v - u) := by
    rw [intervalIntegral.integral_of_le hv.le, integral_Ioc_eq_integral_Ioo,
      ← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hu : u ∈ Set.Ioo 0 v
    · simp [hu]
    · rw [Set.indicator_of_notMem hu]
      by_cases hu0 : u ≤ 0
      · simp [hf0 u hu0]
      · have hvu : v ≤ u := by simp only [Set.mem_Ioo] at hu; grind
        simp [hg0 (v - u) (sub_nonpos.mpr hvu)]
  calc
    _ = ∫ u : ℝ, ∫ w : ℝ, f u * g w * h (u + w) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · apply integral_congr_ae
        filter_upwards [] with u
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro w hw
        simp [hg0 w (by simpa using hw)]
      · intro u hu
        simp [hf0 u (by simpa using hu)]
    _ = ∫ v : ℝ, (∫ u : ℝ, f u * g (v - u)) * h v := weighted_convolution107 f g h hf hg hh hfc hgc
    _ = _ := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards [] with v
      by_cases hv : 0 < v
      · rw [Set.indicator_of_mem (show v ∈ Set.Ioi (0 : ℝ) from hv), hinner v hv]
      · rw [Set.indicator_of_notMem (show v ∉ Set.Ioi (0 : ℝ) from hv)]
        have hz : ∀ u : ℝ, f u * g (v - u) = 0 := by
          intro u
          by_cases hu : u ≤ 0
          · simp [hf0 u hu]
          · simp [hg0 (v - u) (by linarith)]
        simp [hz]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.weighted_convolution107

#print axioms LeanLab.BhowmikGrimmelt2026.continuous_cutoff_cpow107
#print axioms LeanLab.BhowmikGrimmelt2026.compact_cutoff_cpow107

#print axioms LeanLab.BhowmikGrimmelt2026.positive_convolution107
