import LeanLab.HelfgottMajor.SPLIT_leaf_band_zero_count_at_top

/-!
Split of `leaf_band_zero_count_at_top_small_level`, and the shared input for
`leaf_band_zero_count_at_top_large_level`.

At the top of the band the product `q * T` is the fixed number `2 * π * exp 1 * exp 1`, so
`q * T / (2 * π * exp 1) = exp 1` and the main term `T / π * log (q T / (2 π e))` of the explicit
zero count is just `T / π = 2 * exp 1 ^ 2 / q`.  The explicit two sided count of Bennett, Martin,
O'Bryant and Rechnitzer, Math. Comp. 90 (2021), Theorem 1.1, page 1456, bounds the error by
`0.22737 ℓ + 2 log (1 + ℓ) - 0.5` with `ℓ = log (q (T + 2) / (2 π)) = log (exp 1 ^ 2 + q / π)`.
For every `2 ≤ q ≤ 23` this totals at most `10.7`, below `13`, and that arithmetic is proved
here.  The only open input is the cited theorem itself, stated as one CITED leaf.

Numerical check of the true counts: the smallest conductor with a primitive character is `3`,
height `15.476`, where the odd real character has ordinates `8.040, 11.249` below the height,
so the two sided count is `4`.  The cited bound at `q = 3` is about `7.4`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- LEAF: the explicit two sided zero count for a primitive Dirichlet `L`-function.  HARD.
CITED: Bennett, Martin, O'Bryant, Rechnitzer, Counting zeros of Dirichlet `L`-functions,
Math. Comp. 90 (2021), Theorem 1.1, page 1456, in its published form for the case
`ℓ > 1.567`.  The paper's `N (T, χ)` of page 1455 counts zeros `ρ = β + i γ` with `0 < β < 1`
and `|γ| ≤ T` with multiplicity, which is exactly the lab's `zeroCount χ T`; the conductor of a
primitive character of modulus `q` is `q`, and `χ (-1)` is `± 1`, written through its real part. -/
theorem leaf_bmor_zero_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 1 < q) (T : ℝ) (hT : 5 / 7 ≤ T)
    (hℓ : 1.567 < log ((q : ℝ) * (T + 2) / (2 * π))) :
    |zeroCount χ T - (T / π * log ((q : ℝ) * T / (2 * π * exp 1)) - (χ (-1)).re / 4)| ≤
      0.22737 * log ((q : ℝ) * (T + 2) / (2 * π)) +
        2 * log (1 + log ((q : ℝ) * (T + 2) / (2 * π))) - 0.5 := by
  sorry

/-- `exp 1 ^ 2` numerically. -/
theorem top_exp_sq_bounds : 7.38 < exp 1 * exp 1 ∧ exp 1 * exp 1 < 7.39 := by
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_one_gt_d9
  constructor <;> nlinarith

/-- At the top of the band the argument of the main logarithm is `exp 1`. -/
theorem top_main_log (q : ℕ) (hq : 0 < q) :
    log ((q : ℝ) * (2 * π * exp 1 * exp 1 / (q : ℝ)) / (2 * π * exp 1)) = 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have : (q : ℝ) * (2 * π * exp 1 * exp 1 / (q : ℝ)) / (2 * π * exp 1) = exp 1 := by
    field_simp
  rw [this, Real.log_exp]

/-- At the top of the band the argument of `ℓ` is `exp 1 ^ 2 + q / π`. -/
theorem top_ell_arg (q : ℕ) (hq : 0 < q) :
    (q : ℝ) * (2 * π * exp 1 * exp 1 / (q : ℝ) + 2) / (2 * π) =
      exp 1 * exp 1 + (q : ℝ) / π := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  field_simp

/-- `2 ≤ ℓ ≤ 3` at the top of the band for `q ≤ 23`. -/
theorem top_ell_bounds (q : ℕ) (hq : 0 < q) (hq23 : q ≤ 23) :
    2 ≤ log (exp 1 * exp 1 + (q : ℝ) / π) ∧ log (exp 1 * exp 1 + (q : ℝ) / π) ≤ 3 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hq23' : (q : ℝ) ≤ 23 := by exact_mod_cast hq23
  have hpi := Real.pi_gt_three
  have hdiv : (q : ℝ) / π ≤ 23 / 3 := by
    rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]; nlinarith
  have hdiv0 : 0 < (q : ℝ) / π := div_pos hq' Real.pi_pos
  have he := top_exp_sq_bounds
  have hexp2 : exp 1 * exp 1 = exp 2 := by rw [← Real.exp_add]; norm_num
  have hexp3 : exp 1 * exp 1 * exp 1 = exp 3 := by rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have h1 := Real.exp_one_gt_d9
  constructor
  · rw [Real.le_log_iff_exp_le (by linarith), ← hexp2]; linarith
  · rw [Real.log_le_iff_le_exp (by linarith), ← hexp3]; nlinarith

/-- `log 4 < 1.39`. -/
theorem top_log_four : log 4 < 1.39 := by
  have h := Real.log_two_lt_d9
  have : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [this]; linarith

/-- The cited count, evaluated at the top of the band, is at most `13` for `2 ≤ q ≤ 23`.
Pure arithmetic from `leaf_bmor_zero_count`. -/
theorem top_band_count_le_13 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) (hq23 : q ≤ 23) :
    zeroCount χ (2 * π * exp 1 * exp 1 / (q : ℝ)) ≤ 13 := by
  have hq0 : 0 < q := by omega
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq23' : (q : ℝ) ≤ 23 := by exact_mod_cast hq23
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  have he := top_exp_sq_bounds
  set T : ℝ := 2 * π * exp 1 * exp 1 / (q : ℝ) with hTdef
  have hT : T / π = 2 * (exp 1 * exp 1) / q := by
    rw [hTdef]; field_simp
  have hTle : T / π ≤ exp 1 * exp 1 := by
    rw [hT, div_le_iff₀ (by linarith)]; nlinarith
  have hT57 : 5 / 7 ≤ T := by
    rw [hTdef, le_div_iff₀ (by linarith)]; nlinarith
  have hℓarg := top_ell_arg q hq0
  obtain ⟨hℓ2, hℓ3⟩ := top_ell_bounds q hq0 hq23
  have hmain := top_main_log q hq0
  have key := leaf_bmor_zero_count q χ hχ (by omega) T hT57 (by rw [hℓarg]; linarith)
  rw [hmain, hℓarg] at key
  set ℓ := log (exp 1 * exp 1 + (q : ℝ) / π)
  have hlog : log (1 + ℓ) ≤ log 4 :=
    Real.log_le_log (by linarith) (by linarith)
  have h4 := top_log_four
  have hc : |(χ (-1)).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ (-1))
  have hc' := (abs_le.mp hc).1
  have hup := (abs_le.mp key).2
  nlinarith

/-- The target `leaf_band_zero_count_at_top_small_level`, with exactly its statement, from the
cited leaf `leaf_bmor_zero_count` and proved arithmetic. -/
theorem leaf_band_zero_count_at_top_small_level_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) (hq11 : q ≤ 11) :
    zeroCount χ (2 * π * exp 1 * exp 1 / (q : ℝ)) ≤ 13 :=
  top_band_count_le_13 q χ hχ hq2 (by omega)

end LeanLab.HelfgottMajor.Decomp388a
