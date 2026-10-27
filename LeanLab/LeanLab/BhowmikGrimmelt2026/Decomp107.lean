/-
Decomposition of Lemma 7.6 and its written proof on page 29 of P0029.
The original cited declaration is unchanged.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Archimedean84
import LeanLab.BhowmikGrimmelt2026.Scaling107
import LeanLab.BhowmikGrimmelt2026.Integration107

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- LEAF. Page 29 display 7.21. Substitute v = u1 + u2 and sigma = u1 / v. -/
theorem archimedean_coordinates107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) {N T : ℝ} (hT : 1 ≤ T) (hTN : T ≤ N)
    (ρ₁ ρ₂ : ℂ) (hρ₁ : 0 < ρ₁.re) (hρ₁' : ρ₁.re ≤ 1)
    (hρ₂ : 0 < ρ₂.re) (hρ₂' : ρ₂.re ≤ 1) :
    Iphi ϕ G N T ρ₁ ρ₂ = ∫ v in Set.Ioi (0 : ℝ),
      (v : ℂ) ^ (ρ₁ + ρ₂ - 1) * (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂ := by
  have hN : 0 < N := by linarith
  let f : ℝ → ℂ := fun u => (ϕ (u / N) : ℂ) * (u : ℂ) ^ (ρ₁ - 1)
  let g : ℝ → ℂ := fun u => (ϕ (u / N) : ℂ) * (u : ℂ) ^ (ρ₂ - 1)
  let h : ℝ → ℂ := fun v => (GT G T (N - v) : ℂ)
  have hz (ρ : ℂ) (u : ℝ) (hu : u ≤ 0) :
      (ϕ (u / N) : ℂ) * (u : ℂ) ^ (ρ - 1) = 0 := by
    have hzero : ϕ (u / N) = 0 := by
      by_contra hn
      have hs := (hϕ.supp (subset_tsupport ϕ hn)).1
      have : u / N ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu hN.le
      linarith
    simp [hzero]
  have hGc : Continuous G := hG.smooth.continuous
  have hh : Continuous h := by dsimp [h, GT]; fun_prop
  have hconv := positive_convolution107 f g h
    (continuous_cutoff_cpow107 hϕ hN ρ₁) (continuous_cutoff_cpow107 hϕ hN ρ₂) hh
    (compact_cutoff_cpow107 hϕ hN ρ₁) (compact_cutoff_cpow107 hϕ hN ρ₂)
    (hz ρ₁) (hz ρ₂)
  calc
    _ = ∫ u in Set.Ioi (0 : ℝ), ∫ w in Set.Ioi (0 : ℝ), f u * g w * h (u + w) := by
      unfold Iphi
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      apply setIntegral_congr_fun measurableSet_Ioi
      intro w hw
      dsimp [f, g, h]
      rw [show N - u - w = N - (u + w) by ring]
      push_cast
      ring
    _ = ∫ v in Set.Ioi (0 : ℝ), (∫ u in (0 : ℝ)..v, f u * g (v - u)) * h v := hconv
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      have hinner : (∫ u in (0 : ℝ)..v, f u * g (v - u)) =
          (v : ℂ) ^ (ρ₁ + ρ₂ - 1) * Jphi ϕ N v ρ₁ ρ₂ := by
        rw [← beta_scaling107 ϕ N hv ρ₁ ρ₂]
        apply intervalIntegral.integral_congr
        intro u hu
        dsimp [f, g]
        push_cast
        ring
      rw [hinner]
      dsimp [h]
      ring

/-- LEAF. Page 29 proof of 7.19, opposite signs.
Repeated integration by parts in sigma, followed by the outer absolute integral. -/
theorem archimedean_opposite107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ N T : ℝ, 1 ≤ T → T ≤ N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → ρ₁.im * ρ₂.im < 0 →
      ‖∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (ρ₁ + ρ₂ - 1) *
          (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂‖ ≤
        C * N ^ ((ρ₁ + ρ₂).re - 1) * (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) := by
  sorry

/-- LEAF. Page 29 proof of 7.19, equal signs including zero.
Repeated integration by parts in v gives decay at scale T / N. -/
theorem archimedean_same107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ N T : ℝ, 1 ≤ T → T ≤ N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → 0 ≤ ρ₁.im * ρ₂.im →
      ‖∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (ρ₁ + ρ₂ - 1) *
          (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂‖ ≤
        C * N ^ ((ρ₁ + ρ₂).re - 1) *
          (1 + (|ρ₁.im| + |ρ₂.im|) * T / N) ^ (-A) := by
  sorry

/-- LEAF. Page 29 proof of 7.20.
Substitute w = (N - v) / T, expand the cutoff and complex power, and use integral G = 1. -/
theorem archimedean_taylor107 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) :
    ∃ C : ℝ, ∀ N T : ℝ, 1 ≤ T → T ≤ N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → |(ρ₁ + ρ₂).im| * T ≤ N →
      ‖(∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (ρ₁ + ρ₂ - 1) *
          (GT G T (N - v) : ℂ) * Jphi ϕ N v ρ₁ ρ₂) -
          Bphi ϕ ρ₁ ρ₂ * (N : ℂ) ^ (ρ₁ + ρ₂ - 1)‖ ≤
        C * N ^ ((ρ₁ + ρ₂).re - 1) * (1 + |(ρ₁ + ρ₂).im|) * T / N := by
  sorry

/-- LEAF. Page 29 proof of 7.19. The unscaled decay is stronger since T is at most N. -/
theorem archimedean_decay_compare107 {A N T U : ℝ} (hA : 0 < A)
    (hT : 1 ≤ T) (hTN : T ≤ N) (hU : 0 ≤ U) :
    (1 + U) ^ (-A) ≤ (1 + U * T / N) ^ (-A) := by
  have hN : 0 < N := by linarith
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  have : U * T / N ≤ U := (div_le_iff₀ hN).mpr (mul_le_mul_of_nonneg_left hTN hU)
  linarith

/-- CONDITIONAL on the three remaining analytic leaves above. Exact existing Lemma76 proposition.
The assembly has no direct sorry and does not invoke the original cited lemma76. -/
theorem lemma76_decomposed107 : Lemma76 := by
  intro ϕ G hϕ hG
  constructor
  · intro A hA
    obtain ⟨C₁, hC₁⟩ := archimedean_opposite107 hϕ hG A hA
    obtain ⟨C₂, hC₂⟩ := archimedean_same107 hϕ hG A hA
    refine ⟨max (max C₁ C₂) 0, ?_⟩
    intro N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂'
    rw [archimedean_coordinates107 hϕ hG hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂']
    have hN : 0 < N := by linarith
    have hpow : 0 ≤ N ^ ((ρ₁ + ρ₂).re - 1) := Real.rpow_nonneg (by linarith) _
    by_cases hs : ρ₁.im * ρ₂.im < 0
    · have hb := hC₁ N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂' hs
      apply hb.trans
      have hc : C₁ ≤ max (max C₁ C₂) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
      calc
        C₁ * N ^ ((ρ₁ + ρ₂).re - 1) * (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) ≤
            max (max C₁ C₂) 0 * N ^ ((ρ₁ + ρ₂).re - 1) *
              (1 + (|ρ₁.im| + |ρ₂.im|)) ^ (-A) := by
          gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (archimedean_decay_compare107 hA hT hTN (by positivity))
          (mul_nonneg (le_max_right _ _) hpow)
    · exact (hC₂ N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂' (le_of_not_gt hs)).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (le_trans (le_max_right C₁ C₂) (le_max_left _ _)) hpow)
          (Real.rpow_nonneg (by positivity) _))
  · obtain ⟨C, hC⟩ := archimedean_taylor107 hϕ hG
    refine ⟨C, ?_⟩
    intro N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂' hs
    rw [archimedean_coordinates107 hϕ hG hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂']
    exact hC N T hT hTN ρ₁ ρ₂ hρ₁ hρ₁' hρ₂ hρ₂' hs

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.archimedean_coordinates107
#print axioms LeanLab.BhowmikGrimmelt2026.archimedean_opposite107
#print axioms LeanLab.BhowmikGrimmelt2026.archimedean_same107
#print axioms LeanLab.BhowmikGrimmelt2026.archimedean_taylor107
#print axioms LeanLab.BhowmikGrimmelt2026.archimedean_decay_compare107
#print axioms LeanLab.BhowmikGrimmelt2026.lemma76_decomposed107
