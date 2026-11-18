import LeanLab.HelfgottMajor.ZeroCount1623

/-!
`book_main_le_half_exp` of `SPLIT_zero_multiplicity_subexponential.lean` is FALSE as stated,
and so is its smaller leaf `main_q_half_le` of `SPLIT_book_main_le_half_exp.lean`.

`book_main_le_half_exp` reads: for every natural `q` with `NeZero q` and every real `t` with
`100 ≤ t`, `ZeroCount1623.bookMain q (t + 1) ≤ exp (0.6 * t) / 2`, where
`bookMain q T = T / (2 * π) * log (q * T / (2 * π * e))`.
At a fixed height the left side grows like `log q` without bound, while the right side does not
depend on `q`. The witness at height `t` is `q = ⌈exp (exp (0.6 * t) + 10)⌉₊`: then
`log (q * (t + 1) / (2 * π * e)) ≥ exp (0.6 * t) + 10 - log (2 * π * e) > exp (0.6 * t)`, and the
coefficient `(t + 1) / (2 * π)` exceeds one.

`main_q_half_le` reads `(t + 1) / (2 * π) * log q ≤ exp (0.6 * t) / 4` for the same range, and
fails for the same modulus.

This file imports only `ZeroCount1623`, where `bookMain` is defined, so none of its theorems can
depend on an open leaf. The statements refuted below are copied word for word from the leaves.
No statement on main is changed. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real

/-- The constant `log (2 * π * e)` is below `10`, since `2 * π * e < 4 * 4 * 3 < exp 10`. -/
private theorem log_two_pi_e_lt_ten : log (2 * π * exp 1) < 10 := by
  have hpos : 0 < 2 * π * exp 1 := by positivity
  have he : exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlt : 2 * π * exp 1 < 24 := by nlinarith [Real.pi_lt_four, Real.exp_pos 1, Real.pi_pos]
  have h10 : (24 : ℝ) < exp 10 := by
    have := Real.add_one_le_exp (10 : ℝ)
    have h2 : (11 : ℝ) ≤ exp 10 := by linarith
    -- `exp 10 = exp 5 ^ 2 ≥ 6 ^ 2`
    have h5 : (6 : ℝ) ≤ exp 5 := by have := Real.add_one_le_exp (5 : ℝ); linarith
    have hsq : exp 10 = exp 5 * exp 5 := by rw [← Real.exp_add]; norm_num
    nlinarith
  calc log (2 * π * exp 1) < log (exp 10) := Real.log_lt_log hpos (hlt.trans h10)
    _ = 10 := Real.log_exp 10

/-- At every height `t ≥ 0` the modulus `q = ⌈exp (exp (0.6 * t) + 10)⌉₊` is nonzero and has
`log q ≥ exp (0.6 * t) + 10`. -/
private theorem large_modulus (t : ℝ) :
    ⌈exp (exp (0.6 * t) + 10)⌉₊ ≠ 0 ∧
      exp (0.6 * t) + 10 ≤ log ((⌈exp (exp (0.6 * t) + 10)⌉₊ : ℕ) : ℝ) := by
  have hpos : 0 < exp (exp (0.6 * t) + 10) := exp_pos _
  refine ⟨(Nat.ceil_pos.mpr hpos).ne', ?_⟩
  have hq : exp (exp (0.6 * t) + 10) ≤ ((⌈exp (exp (0.6 * t) + 10)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  calc exp (0.6 * t) + 10 = log (exp (exp (0.6 * t) + 10)) := (log_exp _).symm
    _ ≤ _ := log_le_log hpos hq

/-- At every height `t ≥ 100` there is a nonzero modulus `q` for which the main term
`bookMain q (t + 1)` is strictly larger than `exp (0.6 * t) / 2`. Standard: the logarithm is
unbounded in `q` and the right hand side carries no `q`. -/
theorem book_main_gt_half_exp_of_large_conductor (t : ℝ) (ht : 100 ≤ t) :
    ∃ q : ℕ, q ≠ 0 ∧ exp (0.6 * t) / 2 < ZeroCount1623.bookMain q (t + 1) := by
  obtain ⟨hq0, hlogq⟩ := large_modulus t
  refine ⟨⌈exp (exp (0.6 * t) + 10)⌉₊, hq0, ?_⟩
  generalize ⌈exp (exp (0.6 * t) + 10)⌉₊ = q at hq0 hlogq ⊢
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have hc : (0 : ℝ) < 2 * π * exp 1 := by positivity
  have hE : 0 < exp (0.6 * t) := exp_pos _
  have hlogt : 0 ≤ log (t + 1) := Real.log_nonneg (by linarith)
  have hsplit : log ((q : ℝ) * (t + 1) / (2 * π * exp 1))
      = log (q : ℝ) + log (t + 1) - log (2 * π * exp 1) := by
    rw [Real.log_div (mul_ne_zero hqpos.ne' ht1.ne') hc.ne', Real.log_mul hqpos.ne' ht1.ne']
  have hL : exp (0.6 * t) < log ((q : ℝ) * (t + 1) / (2 * π * exp 1)) := by
    rw [hsplit]
    have h10 := log_two_pi_e_lt_ten
    linarith
  have hcoef : 1 / 2 ≤ (t + 1) / (2 * π) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [Real.pi_lt_four]
  unfold ZeroCount1623.bookMain
  have hLpos : 0 < log ((q : ℝ) * (t + 1) / (2 * π * exp 1)) := hE.trans hL
  calc exp (0.6 * t) / 2 = 1 / 2 * exp (0.6 * t) := by ring
    _ < 1 / 2 * log ((q : ℝ) * (t + 1) / (2 * π * exp 1)) := by linarith
    _ ≤ (t + 1) / (2 * π) * log ((q : ℝ) * (t + 1) / (2 * π * exp 1)) :=
        mul_le_mul_of_nonneg_right hcoef hLpos.le

/-- The leaf `book_main_le_half_exp` is false as stated. The quantified statement is the leaf's
statement word for word; it fails at height `t = 100`. -/
theorem book_main_le_half_exp_false :
    ¬ ∀ (q : ℕ) [NeZero q] (t : ℝ), 100 ≤ t →
      ZeroCount1623.bookMain q (t + 1) ≤ exp (0.6 * t) / 2 := by
  intro h
  obtain ⟨q, hq0, hlt⟩ := book_main_gt_half_exp_of_large_conductor 100 le_rfl
  have : NeZero q := ⟨hq0⟩
  exact absurd (h q 100 le_rfl) (not_le.mpr hlt)

/-- The same failure at every admissible height, so no restriction of the height alone repairs
the leaf; a repair has to bound `q` against the height. -/
theorem book_main_le_half_exp_false_at_every_height (t : ℝ) (ht : 100 ≤ t) :
    ¬ ∀ (q : ℕ) [NeZero q], ZeroCount1623.bookMain q (t + 1) ≤ exp (0.6 * t) / 2 := by
  intro h
  obtain ⟨q, hq0, hlt⟩ := book_main_gt_half_exp_of_large_conductor t ht
  have : NeZero q := ⟨hq0⟩
  exact absurd (h q) (not_le.mpr hlt)

/-- The smaller leaf `main_q_half_le` of `SPLIT_book_main_le_half_exp.lean` is false as stated,
for the same modulus at height `t = 100`: there `log q ≥ exp 60 + 10` and the coefficient
`101 / (2 * π)` exceeds one, so the left side exceeds `exp 60`, four times the right side. -/
theorem main_q_half_le_false :
    ¬ ∀ (q : ℕ) [NeZero q] (t : ℝ), 100 ≤ t →
      (t + 1) / (2 * Real.pi) * Real.log (q : ℝ) ≤ Real.exp (0.6 * t) / 4 := by
  intro h
  obtain ⟨hq0, hlogq⟩ := large_modulus 100
  have : NeZero ⌈exp (exp (0.6 * 100) + 10)⌉₊ := ⟨hq0⟩
  have hle := h ⌈exp (exp (0.6 * 100) + 10)⌉₊ 100 le_rfl
  have hE : 0 < exp (0.6 * (100 : ℝ)) := exp_pos _
  have hcoef : (1 : ℝ) ≤ (100 + 1) / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_four]
  have hLpos : 0 ≤ Real.log ((⌈exp (exp (0.6 * 100) + 10)⌉₊ : ℕ) : ℝ) := by linarith
  have := mul_le_mul_of_nonneg_right hcoef hLpos
  linarith

end LeanLab.HelfgottMajor.Decomp269c
