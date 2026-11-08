import LeanLab.HelfgottMajor.SPLIT_zero_count_explicit_upper

/-!
Split of the middle height range of the explicit upper count for the nontrivial zeros of a
primitive Dirichlet `L`-function.  On the range `2 * π ≤ q * t ≤ 2 * π * exp 1` the main
term `(t / π) * log (q * t / (2 * π * exp 1))` of the count is trapped between `-t / π` and
`0`, so it is dropped, at the cost of the single number `t / π ≤ 2 * exp 1`; what is then
left is a count of the zeros of the range at a height bounded by `2 * exp 1`, namely at most
`13`, together with the arithmetic that this number fits below the right side.

The four leaves below are, in order: the height bound `t / π ≤ 2 * exp 1`, the lower bound
`log (2 * π) ≤ log (q * t)` for the half-log term, the count of at most `13` zeros on this
range, and the numeric comparison that places `13` under the right side of the target.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- LEAF. Height reduction.  On the middle range the modulus is at least one and
`q * t ≤ 2 * π * exp 1`, so the height satisfies `t ≤ q * t ≤ 2 * π * exp 1` and hence
`t / π ≤ 2 * exp 1`.  This is the only place where the range bound enters the height. -/
theorem leaf_mid_t_over_pi_le (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t)
    (hlo : 2 * π ≤ q * t) (hhi : q * t ≤ 2 * π * exp 1) :
    t / π ≤ 2 * exp 1 := by
  have h1 : (q:ℝ) ≥ 1 := by exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have h_pi : 0 < π := pi_pos
  calc t / π ≤ (q * t) / π := div_le_div_of_nonneg_right (by nlinarith) (le_of_lt pi_pos)
       _ ≤ (2 * π * exp 1) / π := div_le_div_of_nonneg_right hhi (le_of_lt pi_pos)
       _ = 2 * (π * exp 1) / π := by ring
       _ = 2 * (exp 1 * π) / π := by ring
       _ = 2 * exp 1 * π / π := by ring
       _ = 2 * exp 1 := by rw [mul_div_cancel_right₀ _ h_pi.ne']

/-- LEAF. Logarithm lower bound.  The range starts at `2 * π ≤ q * t`, and `log` is
monotone on the positive reals, so the half-log term is at least `log (2 * π) / 2`.  This
is the estimate that gives the numeric margin below. -/
theorem leaf_mid_log_ge (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t)
    (hlo : 2 * π ≤ q * t) (hhi : q * t ≤ 2 * π * exp 1) :
    log (2 * π) ≤ log (q * t) := by
  apply log_le_log (by positivity) hlo

/-- LEAF. The count on the middle range is a small absolute number.  The middle range
forces `t ≤ 2 * π * exp 1`, and on this bounded height the nontrivial zeros of `L χ` in
the critical strip, counted with the analytic multiplicity, number at most `13`.  This is
the whole counting content of the middle range: no logarithm and no height term survive,
only a fixed count of zeros below height `2 * π * exp 1`. -/
theorem leaf_mid_zero_count_small (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t)
    (hlo : 2 * π ≤ q * t) (hhi : q * t ≤ 2 * π * exp 1) :
    zeroCount χ t ≤ 13 := by
  sorry

/-- LEAF. Numeric placement of the count.  If `t / π ≤ 2 * exp 1` and
`log (2 * π) ≤ log (q * t)`, then `13 ≤ log (q * t) / 2 + 17.7 - t / π`: the half-log
term is at least `0.918` and the height cost `t / π` is at most `5.437`, so the right side
is at least `13.18`.  This is the arithmetic that turns the count of the previous leaf
into the right side of the target. -/
theorem leaf_mid_constant_margin (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t)
    (htpi : t / π ≤ 2 * exp 1) (hlog : log (2 * π) ≤ log (q * t)) :
    13 ≤ 0.5 * log (q * t) + 17.7 - t / π := by
  sorry

/-- The explicit upper count on the middle height range, assembled from the height bound,
the logarithm bound, the small count on the bounded range and the numeric placement of
that count under the right side. -/
theorem zero_count_mid_height_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t)
    (hlo : 2 * π ≤ q * t) (hhi : q * t ≤ 2 * π * exp 1) :
    zeroCount χ t ≤ 0.5 * log (q * t) + 17.7 - t / π := by
  have h1 : t / π ≤ 2 * exp 1 := leaf_mid_t_over_pi_le q t ht hlo hhi
  have h2 : log (2 * π) ≤ log (q * t) := leaf_mid_log_ge q t ht hlo hhi
  have h3 : zeroCount χ t ≤ 13 := leaf_mid_zero_count_small q χ hχ t ht hlo hhi
  have h4 : 13 ≤ 0.5 * log (q * t) + 17.7 - t / π :=
    leaf_mid_constant_margin q t ht h1 h2
  linarith
