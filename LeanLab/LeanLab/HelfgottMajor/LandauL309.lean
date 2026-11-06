import LeanLab.HelfgottMajor.LandauDisk309
import LeanLab.HelfgottMajor.Decomp269a

/-!
The finite zero hypothesis and the Landau disk application on P0014 page 36 display 4.17.
The application retains the explicit norm budget and verified height as hypotheses.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.LandauL309
open Complex Metric Set Filter
open scoped Topology

/-- Landau after translating the disk center, as in P0014 page 36 display 4.16. -/
theorem landau_translated (f : ℂ → ℂ) (c : ℂ) (R r M : ℝ) (hR : 0 < R) (hr : r < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hn : ∀ w ∈ ball c R, f w ≠ 0)
    (hM : ‖f c‖ ≤ M) (hbound : ∀ w ∈ ball c R, ‖f w‖ ≤ M)
    (z : ℂ) (hz : ‖z - c‖ ≤ r) :
    ‖logDeriv f z‖ ≤ 2 * R * Real.log (M / ‖f c‖) / (R - r) ^ 2 := by
  let F : ℂ → ℂ := fun w => f (w + c)
  have hmaps : MapsTo (fun w : ℂ => w + c) (ball 0 R) (ball c R) := by
    intro w hw
    simpa [mem_ball, dist_eq_norm_sub] using hw
  have hFd : DifferentiableOn ℂ F (ball 0 R) := hf.comp (by fun_prop) hmaps
  have hFn : ∀ w ∈ ball 0 R, F w ≠ 0 := fun w hw => hn _ (hmaps hw)
  have hFb : ∀ w ∈ ball 0 R, ‖F w‖ ≤ M := fun w hw => hbound _ (hmaps hw)
  have h := LandauDisk309.landau_inner_disk F R r M hR hr hFd hFn
    (by simpa [F] using hM) hFb (z - c) hz
  have hzmem : z ∈ ball c R := by
    rw [mem_ball, dist_eq_norm_sub]
    exact hz.trans_lt hr
  have hdz := (hf.differentiableAt (isOpen_ball.mem_nhds hzmem)).hasDerivAt
  have hdz' : HasDerivAt f (deriv f z) ((z - c) + c) := by simpa using hdz
  have hFder : deriv F (z - c) = deriv f z := by
    simpa [F, Function.comp_def] using (hdz'.comp (z - c) ((hasDerivAt_id (z - c)).add_const c)).deriv
  simpa [logDeriv_apply, F, hFder] using h

/-- The verified low zeros exclude every L function zero from the Landau disk.
Source P0014 page 36, the disk of center one half plus H and radius H.
CONDITIONAL ON the supplied finite critical line hypothesis.
-/
theorem zero_free_landau_disk (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (H : ℝ) (hH : 1 / 2 < H)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ H → s.re = 1 / 2) :
    ∀ s ∈ ball (((1 / 2 : ℝ) + H : ℝ) : ℂ) H,
      DirichletCharacter.LFunction χ s ≠ 0 := by
  intro s hs hz
  rw [mem_ball, dist_eq_norm_sub] at hs
  have hre : |s.re - (1 / 2 + H)| < H := by
    simpa using (abs_re_le_norm (s - (((1 / 2 : ℝ) + H : ℝ) : ℂ))).trans_lt hs
  have him : |s.im| < H := by
    simpa using (abs_im_le_norm (s - (((1 / 2 : ℝ) + H : ℝ) : ℂ))).trans_lt hs
  have hleft : 1 / 2 < s.re := by linarith [(abs_lt.mp hre).1]
  by_cases hright : s.re < 1
  · have heq := hzeros s hz (by linarith) hright him.le
    linarith
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (le_of_not_gt hright) hz

/-- The Landau application at one with the exact factor eight H of display 4.17.
Source P0014 page 36. CONDITIONAL ON the finite critical line hypothesis and norm budget.
The logarithmic derivative estimate itself is proved here with clean axioms.
-/
theorem landau_at_one (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (H M : ℝ) (hH : 1 / 2 < H)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ H → s.re = 1 / 2)
    (hbound : ∀ s ∈ ball (((1 / 2 : ℝ) + H : ℝ) : ℂ) H,
      ‖DirichletCharacter.LFunction χ s‖ ≤ M) :
    ‖logDeriv (DirichletCharacter.LFunction χ) 1‖ ≤
      8 * H * Real.log (M /
        ‖DirichletCharacter.LFunction χ (((1 / 2 : ℝ) + H : ℝ) : ℂ)‖) := by
  let c : ℂ := (((1 / 2 : ℝ) + H : ℝ) : ℂ)
  have hH0 : 0 < H := by linarith
  have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (ball c H) :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  have hnon := zero_free_landau_disk q χ hχ H hH hzeros
  have hpoint : ‖(1 : ℂ) - c‖ ≤ H - 1 / 2 := by
    have he : (1 : ℂ) - c = (((1 / 2 : ℝ) - H : ℝ) : ℂ) := by
      dsimp [c]
      push_cast
      ring
    rw [he, norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have h := landau_translated (DirichletCharacter.LFunction χ) c H (H - 1 / 2) M hH0
    (by linarith) hdiff hnon (hbound c (mem_ball_self hH0)) hbound 1 hpoint
  have he : H - (H - 1 / 2) = (1 / 2 : ℝ) := by ring
  rw [he] at h
  convert h using 1 <;> dsimp [c] <;> ring

end LeanLab.HelfgottMajor.LandauL309
