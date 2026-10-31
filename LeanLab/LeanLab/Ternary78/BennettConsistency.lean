import LeanLab.Ternary78.BennettCorollary

/-
AI wrote this Lean code. Binary Goldbach is open.
A positive modulus consistency witness for the parameterized Bennett Prop.
The artificial count below is not the count of L-function zeros.
This does not prove the cited analytic theorem for the true count.
-/

namespace LeanLab.Ternary78.Bennett
open Real

/-- An artificial integer approximation to the parity shifted main term. -/
noncomputable def modelCount (q : ℕ) (χ : DirichletCharacter ℂ q) (T : ℝ) : ℕ :=
  ⌊max 0 (T / Real.pi * log (q * T / (2 * Real.pi * exp 1)) - (χ (-1) : ℂ).re / 4)⌋₊

/-- The parameterized cited Prop is consistent at every positive modulus range.
This witness is artificial and does not discharge the analytic input for actual zeros. -/
theorem modelCount_satisfies_bennett (Q : ℕ) : BennettThm1_1 modelCount Q := by
  intro q _ hq hq1 χ hχ T hT l hl
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq1
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  let M : ℝ := T / Real.pi * log (q * T / (2 * Real.pi * exp 1)) - (χ (-1) : ℂ).re / 4
  have hpar : (χ (-1) : ℂ).re ≤ 1 :=
    (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (χ.norm_le_one _))
  have hmain := mainTerm_ge_neg_two_div hq0 hT0
  have hneg : -(1 : ℝ) ≤ -2 / q := by
    apply (le_div_iff₀ hq0).mpr
    linarith
  have hM : -(1.25 : ℝ) ≤ M := by dsimp [M]; linarith
  have hround : |(⌊max 0 M⌋₊ : ℝ) - M| ≤ 1.25 := by
    by_cases hM0 : 0 ≤ M
    · rw [max_eq_right hM0]
      have hlo := Nat.floor_le hM0
      have hhi := Nat.lt_floor_add_one M
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [max_eq_left (le_of_not_ge hM0)]
      norm_num
      rw [abs_of_neg (lt_of_not_ge hM0)]
      linarith
  have hexp : exp (0.7 : ℝ) ≤ 2.1 := by
    have h := Real.exp_bound' (x := (0.7 : ℝ)) (by norm_num) (by norm_num)
      (n := 7) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    linarith
  have hlog : (0.7 : ℝ) ≤ log (1 + l) := by
    apply (Real.le_log_iff_exp_le (by linarith)).mpr
    linarith
  have herr : (1.25 : ℝ) ≤ 0.22737 * l + 2 * log (1 + l) - 0.5 := by linarith
  exact hround.trans herr

#print axioms modelCount_satisfies_bennett

/-- An artificial consistency witness also respecting the printed zero count branch. -/
noncomputable def modelCountFull (q : ℕ) (χ : DirichletCharacter ℂ q) (T : ℝ) : ℕ :=
  if log (q * (T + 2) / (2 * Real.pi)) ≤ 1.567 then 0 else modelCount q χ T

/-- Both printed branches are consistent as an abstract count input.
This remains an artificial count and is not an analytic zero count theorem. -/
theorem modelCountFull_satisfies_bennett (Q : ℕ) : BennettThm1_1Full modelCountFull Q := by
  constructor
  · intro q _ hq hq1 χ hχ T hT l hl
    change 1.567 < log (q * (T + 2) / (2 * Real.pi)) at hl
    have h := modelCount_satisfies_bennett Q q hq hq1 χ hχ T hT hl
    have he : modelCountFull q χ T = modelCount q χ T := by
      simp only [modelCountFull, not_le.mpr hl, ite_false]
    rw [he]
    exact h
  · intro q _ hq hq1 χ hχ T hT hl
    simp only [modelCountFull, hl, ite_true]

#print axioms modelCountFull_satisfies_bennett

end LeanLab.Ternary78.Bennett
