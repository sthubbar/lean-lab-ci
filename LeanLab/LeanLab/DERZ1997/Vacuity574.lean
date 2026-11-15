import LeanLab.DERZ1997.Decomp574a
import LeanLab.DERZ1997.Decomp574b

/-!
Concrete parameter and character instances for task574.
The nonprincipal modulus-three character exists unconditionally.
GRH remains an explicit open hypothesis in the analytic examples.
These examples do not prove GRH or either sealed explicit-formula leaf.
AI wrote the Lean code. Goldbach is open.
-/
open Complex Set
open LeanLab.DERZ1997.Decomp574a LeanLab.DERZ1997.Decomp574b
open LeanLab.DERZ1997.Decomp1529a LeanLab.PNTPort.DirichletZF

example : ∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 := by
  obtain ⟨e⟩ := DirichletCharacter.mulEquiv_units ℂ 3
  let χ := e.symm (-1)
  refine ⟨χ, ?_⟩
  intro hh
  have hh' := congrArg e hh
  simp only [χ, MulEquiv.apply_symm_apply, map_one] at hh'
  have hc := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) hh'
  exact (by decide : (-1 : ZMod 3) ≠ 1) hc

example : (2 : ℝ) ≤ 2 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 2 + 1 ∧
    (1 / 8 : ℝ) < 1 ∧ (1 : ℝ) < 1 + 1 / Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · linarith [one_div_pos.mpr hl]

example : ∃ K : ℝ, 0 < K ∧ ∀ χ : DirichletCharacter ℂ 3, χ ≠ 1 →
    let f : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ ((3 : ℂ) / 2 + I * (0 : ℝ) + (3 / 2 : ℂ) * z)
    ∃ hf : (SetOfZeros (14 / 15) f).Finite,
      (hf.toFinset.card : ℝ) ≤ K * Real.log ((3 : ℝ) * (|(0 : ℝ)| + 3)) := by
  obtain ⟨K, hK, hb⟩ := character_scaled_card574
  exact ⟨K, hK, fun χ hχ => hb 3 χ hχ 0⟩

example (hG : LeanLab.DERZ1997.GRH) : ∃ C : ℝ, 0 < C ∧
    ∀ χ : DirichletCharacter ℂ 3, χ ≠ 1 → ∃ U ∈ Icc (2 : ℝ) 3,
      ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        1 / (C * Real.log ((3 : ℝ) * (2 + 4))) ≤ |(|ρ.im|) - U| := by
  obtain ⟨C, hC, hh⟩ := character_good_height_GRH574 hG
  refine ⟨C, hC, ?_⟩
  intro χ hχ
  simpa only [Nat.cast_ofNat, show (2 : ℝ) + 1 = 3 by norm_num] using hh 3 χ hχ 2 (by norm_num)

example (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1) :
    ∃ K : ℝ, 0 < K ∧ (∑ ρ ∈ (∅ : Finset ℂ), (LMult χ ρ : ℝ)) ≤
      K * Real.log ((3 : ℝ) * (|(0 : ℝ)| + 3)) := by
  obtain ⟨K, hK, hb⟩ := character_local_mass574
  exact ⟨K, hK, hb 3 χ hχ 0 ∅ (by simp)⟩

example (hG : LeanLab.DERZ1997.GRH) (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ (∑ ρ ∈ (∅ : Finset ℂ), (LMult χ ρ : ℝ)) ≤
      C * Real.log ((3 : ℝ) * (2 + 4)) := by
  obtain ⟨C, hC, hb⟩ := character_band_mass_GRH574 hG
  exact ⟨C, hC, hb 3 χ hχ 2 2 ∅ (by norm_num) (by norm_num) (by simp)⟩

example (hG : LeanLab.DERZ1997.GRH) (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧
      ‖(∑ ρ ∈ (LZeros_finite χ 2).toFinset, (LMult χ ρ : ℂ) * (2 : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ (LZeros_finite χ 2).toFinset, (LMult χ ρ : ℂ) * (2 : ℂ) ^ ρ / ρ‖ ≤
          C * Real.sqrt 2 * Real.log ((3 : ℝ) * (2 + 4)) / 2 := by
  obtain ⟨C, hC, hb⟩ := character_height_transfer_GRH574 hG
  exact ⟨C, hC, hb 3 χ hχ 2 2 2 (by norm_num) (by norm_num) le_rfl
    (by norm_num) (LZeros_finite χ 2) (LZeros_finite χ 2)⟩

example : (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) (1 / 2) = 0 ↔
    riemannZeta (1 / 2) = 0) ∧
    LMult (1 : DirichletCharacter ℂ 1) (1 / 2) = zetaMult (1 / 2) :=
  principal_zero_data574 (by norm_num) (by norm_num)

example : (∑ ρ ∈ (LZeros_finite (1 : DirichletCharacter ℂ 1) 2).toFinset,
    (LMult (1 : DirichletCharacter ℂ 1) ρ : ℂ) * (2 : ℂ) ^ ρ / ρ) =
    ∑ ρ ∈ (zetaZeros_finite 2).toFinset, (zetaMult ρ : ℂ) * (2 : ℂ) ^ ρ / ρ :=
  principal_zero_sum574 2 2 (LZeros_finite _ 2) (zetaZeros_finite 2)

example : ‖(∑ n ∈ Finset.Ioc 0 ⌊(2 : ℝ)⌋₊,
    (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (ArithmeticFunction.vonMangoldt n : ℂ)) -
      (Chebyshev.psi 2 : ℂ)‖ ≤ 0 := by
  simpa using principal_psi_error574 (q := 1) (x := 2) (by norm_num)

example (hZ : ‖(Chebyshev.psi 2 : ℂ) - 2 +
    ∑ ρ ∈ (zetaZeros_finite 2).toFinset, (zetaMult ρ : ℂ) * (2 : ℂ) ^ ρ / ρ‖ ≤
      1000 * (2 * Real.log 2 ^ 2 / 2 + Real.log 2)) :
    ‖(∑ n ∈ Finset.Ioc 0 ⌊(2 : ℝ)⌋₊,
      (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (ArithmeticFunction.vonMangoldt n : ℂ)) - 2 +
      ∑ ρ ∈ (LZeros_finite (1 : DirichletCharacter ℂ 1) 2).toFinset,
        (LMult (1 : DirichletCharacter ℂ 1) ρ : ℂ) * (2 : ℂ) ^ ρ / ρ‖ ≤
      2002 * (2 * Real.log 2 ^ 2 / 2 + Real.sqrt 2 + Real.log 2 ^ 2) := by
  simpa using principal_error_of_zeta574 (q := 1) (by norm_num : (2 : ℝ) ≤ 2)
    (by norm_num : (2 : ℝ) ≤ 2) (LZeros_finite _ 2) (zetaZeros_finite 2) hZ
