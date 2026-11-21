import LeanLab.HelfgottMajor.PrincipalRoute669
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
The small circle in P0014 page 33 display 4.7 exists for every primitive character.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Disc669
open Complex MeasureTheory Set Filter
open MainLemma41Split123 LeanLab.Linnik.ExplicitFormula
open scoped Topology

/-- P0014 page 33 display 4.7. The actual integrand is holomorphic on some punctured
closed disc about zero. This supplies a nonempty domain for the general residue leaf. -/
theorem small_disc (x : ℝ) (hx : 1 ≤ x) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      DifferentiableOn ℂ (contourIntegrand χ δ x) (Metric.closedBall 0 r \ {0}) := by
  by_cases hq : q = 1
  · subst q
    exact PrincipalRoute669.small_disc_conductor_one x hx χ δ
  have hn : χ ≠ 1 := ne_one_of_primitive hχ hq
  have hd := DirichletCharacter.differentiable_LFunction hn
  have ha : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) univ :=
    fun s _ => hd.analyticAt s
  have hz : ∀ᶠ s in 𝓝[≠] (0 : ℂ), DirichletCharacter.LFunction χ s ≠ 0 := by
    rcases (hd.analyticAt 0).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · have hall := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (mem_univ 0) hzero
      have h1 := hall (mem_univ (1 : ℂ))
      exact False.elim ((DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
        (Or.inl hn) (by norm_num : 1 ≤ (1 : ℂ).re)) h1)
    · exact hne
  have hzn : ∀ᶠ s in 𝓝 (0 : ℂ), s ≠ 0 → DirichletCharacter.LFunction χ s ≠ 0 := by
    simpa only [mem_compl_iff, mem_singleton_iff] using eventually_nhdsWithin_iff.mp hz
  have hsmall : ∀ᶠ s : ℂ in 𝓝 (0 : ℂ), -1 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hzn.and hsmall)
  refine ⟨r, hr, ?_⟩
  intro s hs
  have hs0 : s ≠ 0 := by simpa only [mem_singleton_iff] using hs.2
  have hsr := hsub hs.1
  have hlog : DifferentiableAt ℂ (logDeriv (DirichletCharacter.LFunction χ)) s :=
    ((hd.analyticAt s).deriv.div (hd.analyticAt s) (hsr.1 hs0)).differentiableAt
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show (x : ℝ) ≠ 0 by linarith)
  have hdiff := (hlog.mul (Route669.contMellin_differentiableAt δ s hsr.2 hs0)).mul
    (differentiableAt_id.const_cpow (c := (x : ℂ)) (Or.inl hx0))
  change DifferentiableWithinAt ℂ
    (fun z => (deriv (DirichletCharacter.LFunction χ) z /
      DirichletCharacter.LFunction χ z) * contMellin δ z * (x : ℂ) ^ z) _ _
  simpa only [logDeriv_apply, Pi.mul_apply, id_eq] using!
    hdiff.differentiableWithinAt (s := Metric.closedBall 0 r \ {0})

end LeanLab.HelfgottMajor.Disc669

#print axioms LeanLab.HelfgottMajor.Disc669.small_disc
