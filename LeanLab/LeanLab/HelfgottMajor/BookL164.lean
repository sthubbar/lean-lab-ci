import Mathlib

/-!
# Helfgott's book, Part IV of 2020-04-01, Lemma 16.4: the elementary bounds of its proof

Unit U-6455, CLOUD 20261020T1318Z-cloud43, P0014. AI wrote this file.

Source: book page 424, copy papers/P0014-book-PartIV.pdf. On the line `s = -1/2 + it`:

* `abs_one_sub_ge`: `|1 - s| ≥ 3/2`;
* `digamma_err_le`: `1/(2|1 - s|) + 1/(4|1 - s|²) ≤ 4/9`, the `O*(4/9)` of the proof, which needs
  `|1 - s|` in the second term; with `|s|`, which can be `1/2`, the term can be `1`,
  `literal_term_one`;
* `arg_one_sub_lt`: `|arg(1 - s)| < π/2`, the term the proof's last display leaves out of
  `|log(1 - s)|`, see FINDINGS F-5038.

Ternary Goldbach is a theorem; binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-20.
-/

namespace LeanLab.HelfgottMajor.BookL164
open Complex

lemma one_sub_eq (t : ℝ) : 1 - ((-1 / 2 : ℂ) + t * I) = (3 / 2 : ℂ) + (-t) * I := by
  push_cast; ring

/-- `|1 - s| ≥ 3/2` on `ℜs = -1/2`. -/
theorem abs_one_sub_ge (t : ℝ) : (3 / 2 : ℝ) ≤ ‖1 - ((-1 / 2 : ℂ) + t * I)‖ := by
  rw [one_sub_eq, show (3 / 2 : ℂ) + (-t) * I = ⟨3 / 2, -t⟩ by apply Complex.ext <;> simp]
  rw [Complex.norm_def, Complex.normSq_mk]
  rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])

/-- **The `O*(4/9)`**: `1/(2|1 - s|) + 1/(4|1 - s|²) ≤ 4/9`. -/
theorem digamma_err_le (t : ℝ) :
    1 / (2 * ‖1 - ((-1 / 2 : ℂ) + t * I)‖) + 1 / (4 * ‖1 - ((-1 / 2 : ℂ) + t * I)‖ ^ 2) ≤ 4 / 9 := by
  have h := abs_one_sub_ge t
  set r := ‖1 - ((-1 / 2 : ℂ) + t * I)‖
  have hr : 0 < r := by linarith
  have h1 : 1 / (2 * r) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h2 : 1 / (4 * r ^ 2) ≤ 1 / 9 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith

/-- With `|s|` in place of `|1 - s|` the second term is `1` at `t = 0`. -/
theorem literal_term_one : 1 / (4 * ‖((-1 / 2 : ℂ) + (0 : ℝ) * I)‖ ^ 2) = 1 := by
  have : ((-1 / 2 : ℂ) + (0 : ℝ) * I) = ((-1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- `|arg(1 - s)| < π/2` on `ℜs = -1/2`, since `ℜ(1 - s) = 3/2 > 0`. -/
theorem arg_one_sub_lt (t : ℝ) : |arg (1 - ((-1 / 2 : ℂ) + t * I))| < Real.pi / 2 := by
  rw [abs_lt]
  have hre : 0 < (1 - ((-1 / 2 : ℂ) + t * I)).re := by simp; norm_num
  exact ⟨(neg_pi_div_two_lt_arg_iff.mpr (Or.inl hre)), arg_lt_pi_div_two_iff.mpr (Or.inl hre)⟩

end LeanLab.HelfgottMajor.BookL164
