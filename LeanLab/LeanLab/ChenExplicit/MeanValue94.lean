/-
AI wrote this Lean code. CODEX task94.
Discharges the existing MeanValueStep input of U1483SiegelQ.
Source: Bordignon arXiv 1907.08327, Section 2 eq 4, as cited in U1483SiegelQ.
The proof uses Mathlib analytic continuation and the real mean value theorem.
No analytic number theory hypothesis enters these proofs.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ChenExplicit.U1483SiegelQ
open Real Set Filter
open scoped Topology
namespace LeanLab.ChenExplicit.MeanValue94

/-- Quadratic characters give real terms on the real axis. -/
theorem term_im_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    (x : ℝ) (n : ℕ) : (LSeries.term (fun n : ℕ => χ n) (x : ℂ) n).im = 0 := by
  unfold LSeries.term
  split_ifs with hn
  · simp
  · have hp : ((n : ℂ) ^ (x : ℂ)) = ((n : ℝ) ^ x : ℝ) := by
      simpa using (Complex.ofReal_cpow (Nat.cast_nonneg n) x).symm
    rw [hp]
    rcases (MulChar.isQuadratic_iff_sq_eq_one.mpr hχ) (n : ZMod q) with h | h | h <;>
      simp [h, Complex.div_im]

/-- The Dirichlet series is real on the real axis. -/
theorem series_im_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    (x : ℝ) : (LSeries (fun n : ℕ => χ n) (x : ℂ)).im = 0 := by
  unfold LSeries
  have he : (fun n : ℕ => LSeries.term (fun n : ℕ => χ n) (x : ℂ) n) =
      fun n => (((LSeries.term (fun n : ℕ => χ n) (x : ℂ) n).re : ℝ) : ℂ) := by
    funext n
    apply Complex.ext <;> simp [term_im_zero χ hχ x n]
  rw [he, ← Complex.ofReal_tsum]
  simp

/-- Analytic continuation preserves real values for a quadratic nonprincipal character. -/
theorem LFunction_im_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hχ2 : χ ^ 2 = 1) (x : ℝ) :
    (DirichletCharacter.LFunction χ (x : ℂ)).im = 0 := by
  have hd := DirichletCharacter.differentiable_LFunction hχ
  have ha : AnalyticOnNhd ℝ (fun x : ℝ => (DirichletCharacter.LFunction χ (x : ℂ)).im) univ :=
    fun x _ => (hd.analyticAt (x : ℂ)).im_ofReal
  have hz : (fun x : ℝ => (DirichletCharacter.LFunction χ (x : ℂ)).im) =ᶠ[𝓝 (2 : ℝ)] 0 := by
    filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < 2 by norm_num)] with y hy
    rw [DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hy)]
    exact series_im_zero χ hχ2 y
  have he := ha.eq_of_eventuallyEq (analyticOnNhd_const : AnalyticOnNhd ℝ (fun _ : ℝ => (0 : ℝ)) univ) hz
  exact congrFun he x

/-- The real mean value theorem gives the norm identity at a real zero. -/
theorem norm_mean_value (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hreal : ∀ x : ℝ, (F (x : ℂ)).im = 0) (β : ℝ) (hβ : β < 1)
    (hz : F (β : ℂ) = 0) :
    ∃ σ : ℝ, β < σ ∧ σ < 1 ∧ ‖F 1‖ = (1 - β) * ‖deriv F (σ : ℂ)‖ := by
  have hc (x : ℝ) : F (x : ℂ) = ((F (x : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [hreal x]
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => (F (x : ℂ)).re)
      (deriv F (x : ℂ)).re x := (hF (x : ℂ)).hasDerivAt.real_of_complex
  have hder (x : ℝ) : deriv F (x : ℂ) = ((deriv F (x : ℂ)).re : ℂ) := by
    have hco := (hd x).ofReal_comp
    have he : (fun y : ℝ => ((F (y : ℂ)).re : ℂ)) = fun y : ℝ => F (y : ℂ) := by
      funext y; exact (hc y).symm
    rw [he] at hco
    exact (hF (x : ℂ)).hasDerivAt.comp_ofReal.unique hco
  obtain ⟨σ, hσ, he⟩ := exists_hasDerivAt_eq_slope
    (fun x : ℝ => (F (x : ℂ)).re) (fun x : ℝ => (deriv F (x : ℂ)).re) hβ
    (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
  refine ⟨σ, hσ.1, hσ.2, ?_⟩
  simp only [Complex.ofReal_one, hz, Complex.zero_re, sub_zero] at he
  have he' : (F 1).re = (1 - β) * (deriv F (σ : ℂ)).re := by
    have hh := (eq_div_iff (show 1 - β ≠ 0 by linarith)).mp he
    linarith
  have ha := congrArg abs he'
  rw [abs_mul, abs_of_pos (show 0 < 1 - β by linarith)] at ha
  calc ‖F 1‖ = |(F 1).re| := by
         conv_lhs => rw [show F 1 = ((F 1).re : ℂ) by simpa using hc 1]
         simp
       _ = (1 - β) * |(deriv F (σ : ℂ)).re| := ha
       _ = (1 - β) * ‖deriv F (σ : ℂ)‖ := by
         congr 1
         conv_rhs => rw [hder σ]
         simp

/-- The cited mean value input is a consequence of Mathlib.
Bordignon Section 2 eq 4 in the exact existing lab form. -/
theorem meanValueStep : U1483.MeanValueStep := by
  intro q _ χ hχ β hβ
  exact norm_mean_value (DirichletCharacter.LFunction χ)
    (DirichletCharacter.differentiable_LFunction hχ.2.2.1)
    (LFunction_im_zero χ hχ.2.2.1 hχ.2.2.2) β hβ.2.1 hβ.2.2

/-- Concrete mean value instance with a real zero at zero. -/
example : ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧
    ‖(1 : ℂ)‖ = (1 - (0 : ℝ)) * ‖deriv (fun z : ℂ => z) (σ : ℂ)‖ := by
  simpa using norm_mean_value (fun z : ℂ => z) differentiable_id
    (by intro x; simp) 0 (by norm_num) (by simp)

/-- Concrete quadratic character term instance. -/
example : (LSeries.term (fun n : ℕ => (1 : DirichletCharacter ℂ 3) n) (2 : ℂ) 1).im = 0 := by
  exact term_im_zero 1 (by simp) 2 1

#print axioms meanValueStep
#print axioms norm_mean_value
#print axioms term_im_zero
#print axioms series_im_zero
#print axioms LFunction_im_zero
end LeanLab.ChenExplicit.MeanValue94
