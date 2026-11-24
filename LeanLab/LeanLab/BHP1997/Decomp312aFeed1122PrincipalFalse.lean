/-
P0069, Section 4, pages 24 to 27. Burst S82 feed1122 for `lower_mean_value_supply`
in LeanLab.BHP1997.Decomp312a.

The open leaf of that supply claim on main is `leaf_auxiliary_family_supply` in
LeanLab.BHP1997.SPLIT_lower_mean_value_supply. Its existing further split, in
LeanLab.BHP1997.SPLIT_leaf_auxiliary_family_supply, routes the reference density
through `leaf_principal_reference_average`, which quantifies over an ARBITRARY density
constant `u0` and an ARBITRARY coefficient family `c0`. This file proves that leaf is
false: with `c0 = 0` the window average vanishes, while the main term `u0 / log x`
with `u0 = 1` is not bounded by `C * (log x)^(-2)`.

So that split route cannot close `lower_mean_value_supply`; the density constant must
be tied to the constructed family, as on page 33 of the paper. Nothing here changes an
existing statement. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_auxiliary_family_supply

namespace LeanLab.BHP1997.Decomp312a
open Classical Complex DecompC165b Decomp312c Decomp132
open scoped BigOperators
open Filter

/-- With the zero coefficient family the sifted family vanishes, so every reference
average is zero. Pages 24 and 25, the I1 average of the repaired display 4.2. -/
theorem referenceAverage_sifted_zero (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    referenceAverage (section4SiftedFamily (fun _ _ => (0 : ℝ))) x χ = 0 := by
  simp [referenceAverage, section4SiftedFamily]

/-- The statement of `leaf_principal_reference_average` in
LeanLab.BHP1997.SPLIT_leaf_auxiliary_family_supply is false. Counterexample:
`u0 = 1`, `c0 = 0`, `A = 2`, `q = 1`, `χ = 1`, and any `x` with
`log x ≥ max 1 (|C| + 1)`. The left side is `1 / log x`, the right side is
`C / (log x)^2 < 1 / log x`. -/
theorem not_leaf_principal_reference_average :
    ¬ (∀ (u0 : ℝ) (c0 : ℝ → ℕ → ℝ),
      ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, χ = 1 →
          ‖referenceAverage (section4SiftedFamily c0) x χ - (u0 : ℂ) / (Real.log x : ℂ)‖ ≤
            C * Real.log x ^ (-A)) := by
  intro h
  obtain ⟨C, X, hC⟩ := h 1 (fun _ _ => 0) 2 (by norm_num)
  set L : ℝ := max 1 (|C| + 1) with hL
  set x : ℝ := max X (Real.exp L) with hx
  have hXx : X ≤ x := le_max_left _ _
  have hlogx : L ≤ Real.log x := by
    have : Real.exp L ≤ x := le_max_right _ _
    have hpos : 0 < x := lt_of_lt_of_le (Real.exp_pos L) this
    calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos L) this
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLC : |C| + 1 ≤ L := le_max_right _ _
  set l := Real.log x with hl
  have hl1 : 1 ≤ l := le_trans hL1 hlogx
  have hlpos : 0 < l := by linarith
  have hq : ((1 : ℕ) : ℝ) ≤ l ^ (2 : ℝ) := by
    rw [Real.rpow_two]; push_cast; nlinarith
  have key := hC x hXx 1 le_rfl hq 1 rfl
  rw [referenceAverage_sifted_zero, zero_sub, norm_neg] at key
  have hnorm : ‖((1 : ℝ) : ℂ) / (l : ℂ)‖ = 1 / l := by
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hlpos]; norm_num
  rw [hnorm] at key
  have hpow : l ^ (-(2 : ℝ)) = 1 / l ^ 2 := by
    rw [Real.rpow_neg hlpos.le, Real.rpow_two, one_div]
  rw [hpow] at key
  have hl2 : 0 < l ^ 2 := by positivity
  have : l ≤ C := by
    have h1 : 1 / l * l ^ 2 ≤ C * (1 / l ^ 2) * l ^ 2 := mul_le_mul_of_nonneg_right key hl2.le
    have e1 : 1 / l * l ^ 2 = l := by field_simp
    have e2 : C * (1 / l ^ 2) * l ^ 2 = C := by field_simp
    linarith
  have : C ≤ |C| := le_abs_self C
  linarith

end LeanLab.BHP1997.Decomp312a
