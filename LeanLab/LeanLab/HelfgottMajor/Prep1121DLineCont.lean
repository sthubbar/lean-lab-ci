import LeanLab.HelfgottMajor.Prep1121VIPointwiseA
import LeanLab.Linnik.ExplicitFormula.LeftHalf

/-!
PREP 2026-11-21 deepening pass p2, route step `MainLemma41Split123.vertical_integral_bound`.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 34, display 4.13:
the integrand L'/L(-1/2 + iτ, χ) is defined and continuous on the whole line. The parent
leaf `Prep1121VIBudget.logDeriv_line_continuous` is proved here with its exact statement:
L(s, χ) is differentiable off s = 1 by `DirichletCharacter.differentiableAt_LFunction`, so
its derivative is continuous there, and L has no zero on re s = -1/2 by the lab lemma
`LeanLab.Linnik.ExplicitFormula.no_zero_left_line`.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121DLineCont
open Complex

/-- P0014 page 34, display 4.13: exact statement of the parent leaf
`Prep1121VIBudget.logDeriv_line_continuous`. -/
theorem logDeriv_line_continuous {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    Continuous (fun τ : ℝ => deriv χ.LFunction ((-1 / 2 : ℂ) + τ * I) /
      χ.LFunction ((-1 / 2 : ℂ) + τ * I)) := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hd : DifferentiableOn ℂ χ.LFunction {1}ᶜ := fun s hs =>
    (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
  have hcd : ContinuousOn (deriv χ.LFunction) {1}ᶜ :=
    (hd.contDiffOn (n := 1) hU).continuousOn_deriv_of_isOpen hU le_rfl
  have hline : Continuous (fun τ : ℝ => (-1 / 2 : ℂ) + τ * I) := by fun_prop
  have hmem : ∀ τ : ℝ, (-1 / 2 : ℂ) + τ * I ∈ ({1}ᶜ : Set ℂ) := by
    intro τ h
    have := congrArg Complex.re (Set.mem_singleton_iff.mp h)
    simp at this
    norm_num at this
  exact Continuous.div (hcd.comp_continuous hline hmem)
    (hd.continuousOn.comp_continuous hline hmem)
    (fun τ => LeanLab.Linnik.ExplicitFormula.no_zero_left_line hχ τ)

end LeanLab.HelfgottMajor.Prep1121DLineCont
