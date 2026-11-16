import LeanLab.DERZ1997.GammaRatio623
import LeanLab.DERZ1997.Rademacher623
import LeanLab.DERZ1997.Decomp1529b

/-!
Concrete source-domain instances for CODEX task623.
The Rademacher strip theorem remains an explicit analytic input.
AI wrote the Lean code. Goldbach is open.
-/
open Complex
open LeanLab.DERZ1997.GammaRatio623 LeanLab.DERZ1997.Rademacher623

example : ‖Gamma (3 / 4 : ℂ) / Gamma (-1 / 4 : ℂ)‖ = 1 / 4 := by
  convert gamma_ratio_left623 (Q := 0) (by norm_num) 0 using 1 <;> norm_num

example : ‖Gamma (1 / 4 : ℂ) / Gamma (1 / 4 : ℂ)‖ = 1 := by
  convert gamma_ratio_right623 (Q := 0) (by norm_num) 0 using 1 <;> norm_num

example : ‖Gamma (3 / 4 : ℂ) / Gamma (-1 / 4 : ℂ)‖ ≤ 1 / 4 := by
  convert gamma_ratio_left_bound623 (Q := 0) (by norm_num) 0 using 1 <;> norm_num

example : ‖Gamma (1 : ℂ) / Gamma (0 : ℂ)‖ = 0 := by
  norm_num [Gamma_zero]

example : ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) (5 / 4 : ℂ)‖ ≤
    (riemannZeta (5 / 4 : ℂ)).re := by
  convert right_boundary623 (1 : DirichletCharacter ℂ 1) (η := 1 / 4) (by norm_num) 0 using 1 <;> norm_num

example : ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) (5 / 4 : ℂ)‖ ≤
    ((1 : ℝ) * ‖(5 / 4 : ℂ) + 1‖ / (2 * Real.pi)) ^
      ((1 + (1 / 4 : ℝ) - (5 / 4 : ℂ).re) / 2) *
      (riemannZeta (5 / 4 : ℂ)).re := by
  convert convexity_right_boundary623 (1 : DirichletCharacter ℂ 1)
    (η := 1 / 4) (by norm_num) (5 / 4) (by norm_num) using 1 <;> norm_num

example : ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ ≠ 1 ∧
    (0 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) ≤ 1 / 2 ∧
    -(1 / 4 : ℝ) ≤ ((5 / 4 : ℂ) + I).re ∧
    ((5 / 4 : ℂ) + I).re ≤ 1 + (1 / 4 : ℝ) := by
  obtain ⟨e⟩ := DirichletCharacter.mulEquiv_units ℂ 3
  let χ := e.symm (-1)
  have hne : χ ≠ 1 := by
    intro hh
    have hh' := congrArg e hh
    simp only [χ, MulEquiv.apply_symm_apply, map_one] at hh'
    have hc := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) hh'
    exact (by decide : (-1 : ZMod 3) ≠ 1) hc
  have hprim : χ.IsPrimitive := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp χ.conductor_dvd_level with h | h
    · exact False.elim (hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
    · exact h
  exact ⟨χ, hprim, hne, by norm_num, by norm_num, by norm_num, by norm_num⟩

open LeanLab.DERZ1997.Decomp1529a LeanLab.DERZ1997.Decomp1529b

example : ∀ n : ℕ, (n : ℝ) ≠ 5 / 2 := by
  intro n hn
  have hh := half_integer_distance197 2 n
  norm_num at hh
  rw [hn, sub_self, abs_zero] at hh
  norm_num at hh

example (hG : LeanLab.DERZ1997.GRH) : ∃ C : ℝ, 0 < C ∧
    ∀ χ : DirichletCharacter ℂ 3, χ ≠ 1 →
    ∀ hf : (LZeros χ 2).Finite,
      ‖psiChi χ 2 + ∑ ρ ∈ hf.toFinset, (LMult χ ρ : ℂ) * (2 : ℂ) ^ ρ / ρ‖ ≤
        C * (2 * Real.log (3 * 2 : ℝ) ^ 2 / 2 + Real.sqrt 2 +
          Real.log (3 * 2 : ℝ) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := character_formula623 hG
  refine ⟨C, hC, ?_⟩
  intro χ hχ hf
  exact hb 3 χ hχ 2 2 (by norm_num) (by norm_num) (by norm_num) hf
