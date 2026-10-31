import LeanLab.HardyLittlewood1923.GammaIntegrable
import Mathlib.Analysis.MellinInversion

/-!
AI wrote this Lean code for CODEX task52.
Paper P0004 page 8 equation 2.13 uses the inverse Mellin transform of Gamma.
This file starts with the identity on the positive real ray.
-/

open Complex Real Set Filter MeasureTheory

namespace LeanLab.HardyLittlewood1923.Task52

/-- Mellin inversion for the exponential on a positive real ray. -/
theorem gamma_mellin_inverse {σ : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2)
    {x : ℝ} (hx : 0 < x) :
    mellinInv σ Complex.Gamma x = (Real.exp (-x) : ℂ) := by
  let f : ℝ → ℂ := fun x => (Real.exp (-x) : ℂ)
  have heq : ∀ s : ℂ, 0 < s.re → mellin f s = Complex.Gamma s := by
    intro s hs
    rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral_eq_mellin]
  have hc : MellinConvergent f (σ : ℂ) := by
    have h := Complex.GammaIntegral_convergent (s := (σ : ℂ)) (by simpa using (show (0 : ℝ) < σ by linarith))
    simpa only [MellinConvergent, f, smul_eq_mul, mul_comm] using h
  have hg : Complex.VerticalIntegrable Complex.Gamma σ := by
    have h := gamma_kernel_integrable h1 h2 (z := 1) (by simp)
    simpa only [Complex.VerticalIntegrable, one_cpow, mul_one] using h
  have hv : Complex.VerticalIntegrable (mellin f) σ := by
    unfold Complex.VerticalIntegrable at hg ⊢
    have he : (fun t : ℝ => mellin f ((σ : ℂ) + t * I)) =
        (fun t : ℝ => Complex.Gamma ((σ : ℂ) + t * I)) := by
      funext t
      exact heq _ (by simpa using (show (0 : ℝ) < σ by linarith))
    rw [he]
    exact hg
  have h := mellinInv_mellin_eq σ f hx hc hv (by dsimp [f]; fun_prop)
  have he : mellinInv σ (mellin f) x = mellinInv σ Complex.Gamma x := by
    unfold mellinInv
    congr 2
    funext t
    rw [heq _ (by simpa using (show (0 : ℝ) < σ by linarith))]
  rw [he] at h
  exact h

#print axioms gamma_mellin_inverse

end LeanLab.HardyLittlewood1923.Task52
