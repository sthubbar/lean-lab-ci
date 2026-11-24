import LeanLab.HelfgottMajor.DecompF1618

/-!
# The leaf `conductor_log_le_exp_sixty_div_four` of `DecompF1618.lean` is FALSE

The leaf asks, for EVERY nonzero natural `q`, that `0.15 * log q + 3.389 ≤ exp (0.6 * 100) / 4`.
The right side is the fixed number `exp 60 / 4`, while `log q` is unbounded in `q`, so the
statement fails for every `q` with `log q ≥ 2 * exp 60`. The theorem below proves the negation
with the explicit witness `q = ⌈exp (2 * exp 60)⌉₊`: there `log q ≥ 2 * exp 60`, and
`0.15 * (2 * exp 60) = 0.3 * exp 60 > exp 60 / 4`.

Consequence, recorded as a QUESTION and not proved here: the parent statement
`conductor_log_le_quarter_exp` of `SPLIT_book_error_le_half_exp.lean`, which asks for
`0.15 * log q + 3.389 ≤ exp (0.6 * t) / 4` for every nonzero `q` and every `t ≥ 100`, fails at
`t = 100` with the same `q`, so that split needs a hypothesis tying the conductor to the height,
such as `log q ≤ c * t`, from the book's range.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real

/-- The leaf `conductor_log_le_exp_sixty_div_four` is false: its universal statement over all
nonzero moduli `q` fails at `q = ⌈exp (2 * exp 60)⌉₊`. -/
theorem conductor_log_le_exp_sixty_div_four_false :
    ¬ ∀ q : ℕ, q ≠ 0 → 0.15 * log q + 3.389 ≤ exp (0.6 * (100 : ℝ)) / 4 := by
  intro h
  set N : ℕ := ⌈exp (2 * exp 60)⌉₊ with hN
  have hpos : (0 : ℝ) < exp (2 * exp 60) := exp_pos _
  have hle : exp (2 * exp 60) ≤ (N : ℝ) := Nat.le_ceil _
  have hN0 : N ≠ 0 := by
    intro h0
    have : (N : ℝ) = 0 := by exact_mod_cast h0
    linarith
  have hlog : 2 * exp 60 ≤ log (N : ℝ) := by
    have := log_le_log hpos hle
    rwa [log_exp] at this
  have hbound := h N hN0
  have h60 : (0.6 : ℝ) * 100 = 60 := by norm_num
  rw [h60] at hbound
  have he : 0 < exp (60 : ℝ) := exp_pos _
  nlinarith

end LeanLab.HelfgottMajor.Decomp269c
