/- AI wrote this Lean code for CODEX task148.
Recovered from recorded write commands after execution access failed.
A fresh build and gate checks are required. Goldbach is open. -/
import LeanLab.BS2022GRH.ChenThresholdGRH
import Mathlib.NumberTheory.LSeries.Nonvanishing
namespace LeanLab.BS2022GRH.RH148
open ChenThresholdGRH Complex
/-- The RH input of Lemma 1 p. 1215 follows from the lab GRH predicate.
CONDITIONAL ON GRH. Use Mathlib nonvanishing and the completed functional equation. -/
theorem rh_of_grh (hG : GRH) : RiemannHypothesis := by
  intro s hs htriv _hs1
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num [riemannZeta_zero] at hs
  have hGamma : Gammaℝ s ≠ 0 := by
    intro hzero
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hzero
    cases n with
    | zero => exact hs0 (by simpa using hn)
    | succ n =>
      apply htriv
      refine ⟨n, ?_⟩
      rw [hn]
      push_cast
      ring
  have hcompleted : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hs
    exact hs.resolve_right hGamma
  have hpos : 0 < s.re := by
    by_contra h
    have hle : s.re ≤ 0 := le_of_not_gt h
    have hre : 1 ≤ (1 - s).re := by simp only [sub_re, one_re]; linarith
    have ht0 : 1 - s ≠ 0 := by
      intro ht
      have := congrArg Complex.re ht
      simp only [sub_re, one_re, zero_re] at this
      linarith
    apply riemannZeta_ne_zero_of_one_le_re hre
    rw [riemannZeta_def_of_ne_zero ht0, completedRiemannZeta_one_sub, hcompleted, zero_div]
  have hlt : s.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hs
  apply hG 1 (1 : DirichletCharacter ℂ 1) s _ hpos hlt
  simpa only [DirichletCharacter.LFunction_modOne_eq] using hs
end LeanLab.BS2022GRH.RH148
#print axioms LeanLab.BS2022GRH.RH148.rh_of_grh
