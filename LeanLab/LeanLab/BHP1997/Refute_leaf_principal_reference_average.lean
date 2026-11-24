/-
Burst burst-20261122, session S83, OMOS FEED. P0069 Baker Harman Pintz 1997, pages 24 and 25,
the reference average of display 4.2 as split in SPLIT_leaf_auxiliary_family_supply.

The leaf `leaf_principal_reference_average` of that split is false as stated: it quantifies over
every `u0` and every family `c0` with no hypothesis tying `u0` to the density of the family. With
`c0 = 0` the reference average is `0`, and with `u0 = 1` and `A = 2` the leaf would give
`1 / log x ≤ C (log x)^(-2)` for all large `x`, which fails once `log x > C`.
This refutes only the split leaf, not the sealed parent `leaf_auxiliary_family_supply`, which
asks for some family `b` to exist and assumes `0.9953 < u0 ≤ 1`.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_auxiliary_family_supply

namespace LeanLab.BHP1997.Decomp312a
open Classical Complex DecompC165b Decomp312c Decomp132

/-- The reference average of the zero family is zero, pages 24 and 25. -/
theorem referenceAverage_section4_zero (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    referenceAverage (section4SiftedFamily (fun _ _ => (0 : ℝ))) x χ = 0 := by
  unfold referenceAverage section4SiftedFamily
  simp

/-- The statement of `leaf_principal_reference_average` is false: take `u0 = 1`, `c0 = 0`,
`A = 2`, `q = 1` and the principal character. -/
theorem leaf_principal_reference_average_false :
    ¬ (∀ (u0 : ℝ) (c0 : ℝ → ℕ → ℝ),
      ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, χ = 1 →
          ‖referenceAverage (section4SiftedFamily c0) x χ - (u0 : ℂ) / (Real.log x : ℂ)‖ ≤
            C * Real.log x ^ (-A)) := by
  intro h
  obtain ⟨C, X, hX⟩ := h 1 (fun _ _ => 0) 2 (by norm_num)
  set L : ℝ := max (|C| + 2) (Real.log (max X 1)) with hL
  have hL2 : |C| + 2 ≤ L := le_max_left _ _
  have hCabs : C ≤ |C| := le_abs_self C
  have hLpos : 0 < L := by linarith [abs_nonneg C]
  have hlog : Real.log (Real.exp L) = L := Real.log_exp L
  have hXx : X ≤ Real.exp L := by
    have h1 : Real.log (max X 1) ≤ L := le_max_right _ _
    have h2 : max X 1 ≤ Real.exp L := by
      calc max X 1 = Real.exp (Real.log (max X 1)) :=
            (Real.exp_log (lt_of_lt_of_le one_pos (le_max_right X 1))).symm
        _ ≤ Real.exp L := Real.exp_le_exp.mpr h1
    exact le_trans (le_max_left X 1) h2
  have hq : ((1 : ℕ) : ℝ) ≤ Real.log (Real.exp L) ^ (2 : ℝ) := by
    rw [hlog, Real.rpow_two]; push_cast; nlinarith [abs_nonneg C, hL2]
  have key := hX (Real.exp L) hXx 1 le_rfl hq (1 : DirichletCharacter ℂ 1) rfl
  rw [referenceAverage_section4_zero, hlog, zero_sub, norm_neg] at key
  have hnorm : ‖((1 : ℝ) : ℂ) / (L : ℂ)‖ = 1 / L := by
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hLpos.le]; simp
  rw [hnorm, Real.rpow_neg hLpos.le, Real.rpow_two] at key
  have hL2' : 0 < L ^ 2 := by positivity
  rw [div_le_iff₀ hLpos] at key
  have : C * (L ^ 2)⁻¹ * L = C / L := by field_simp
  rw [this, le_div_iff₀ hLpos] at key
  nlinarith [abs_nonneg C, hL2, hCabs]

/-- The kernel checks that the refuted proposition is exactly the type of the leaf
`leaf_principal_reference_average` of SPLIT_leaf_auxiliary_family_supply. -/
theorem leaf_principal_reference_average_statement_false :
    ¬ (type_of% @leaf_principal_reference_average) :=
  leaf_principal_reference_average_false

end LeanLab.BHP1997.Decomp312a
