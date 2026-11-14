import LeanLab.ExceptionalSet.UpJ200.Decomp559b
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
P0082 page 358 display 9 at cutoff two.
The nonempty selection domain follows from Mathlib zeta nonvanishing near one.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp559c
open LeanLab.ExceptionalSet.UpJ200.Decomp559b
open Filter Topology

/-- P0082 page 358 display 9. At cutoff two there is a positive real
zero free interval and the absent exceptional conductor is one. -/
theorem selected_real_zero_at_two : ∃ a : ℝ, 0 < a ∧ SelectedRealZero a 2 1 := by
  have hz : ∀ᶠ σ : ℝ in 𝓝 1, riemannZeta (σ : ℂ) ≠ 0 := by
    exact (Complex.continuous_ofReal.tendsto (1 : ℝ)).eventually
      (by simpa using riemannZeta_eventually_ne_zero_nhds_one)
  obtain ⟨ε, hε, hz⟩ := Metric.eventually_nhds_iff.mp hz
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨ε / 2 * Real.log 2, by positivity, Or.inl ⟨rfl, ?_⟩⟩
  intro q hq χ hq1 hqP hp σ hσ hσ1
  have hq2 : q ≤ 2 := by exact_mod_cast hqP
  have hqcases : q = 1 ∨ q = 2 := by omega
  rcases hqcases with rfl | rfl
  · rw [DirichletCharacter.LFunction_modOne_eq]
    apply hz
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]
    have hdiv : ε / 2 * Real.log 2 / Real.log 2 = ε / 2 := by field_simp
    rw [hdiv] at hσ
    linarith
  · have hc : χ = 1 := by
      ext x
      have hx : x = (1 : (ZMod 2)ˣ) := by
        have h : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
        exact h x
      rw [hx]
      simp
    have hp' : χ.conductor = 2 := hp
    rw [hc, DirichletCharacter.conductor_one] at hp'
    norm_num at hp'

end LeanLab.ExceptionalSet.UpJ200.Decomp559c
