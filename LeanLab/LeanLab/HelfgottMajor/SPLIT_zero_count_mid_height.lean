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
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.one_le (n := q)
  have ht0 : 0 < t := by linarith
  have hqt : t ≤ (q : ℝ) * t := by
    have := mul_le_mul_of_nonneg_right hq1 ht0.le
    simpa using this
  have h2 : t ≤ 2 * π * exp 1 := le_trans hqt hhi
  rw [div_le_iff₀ pi_pos]
  linarith

/-- LEAF. Logarithm lower bound.  The range starts at `2 * π ≤ q * t`, and `log` is
monotone on the positive reals, so the half-log term is at least `log (2 * π) / 2`.  This
is the estimate that gives the numeric margin below. -/
theorem leaf_mid_log_ge (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t)
    (hlo : 2 * π ≤ q * t) (hhi : q * t ≤ 2 * π * exp 1) :
    log (2 * π) ≤ log (q * t) := by
  exact log_le_log (by positivity) hlo

/-- AGY task42 helper. On the middle range the height is at most `2 * π * exp 1` and the
conductor is at most `17`. -/
lemma mid_range_bounds_agy42 (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t)
    (hhi : (q : ℝ) * t ≤ 2 * π * exp 1) :
    t ≤ 2 * π * exp 1 ∧ q ≤ 17 := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.one_le (n := q)
  have ht0 : 0 ≤ t := by linarith
  have hqt : t ≤ (q : ℝ) * t := by
    simpa using mul_le_mul_of_nonneg_right hq1 ht0
  have hq0 : 0 ≤ (q : ℝ) := by linarith
  have hq_le : (q : ℝ) ≤ (q : ℝ) * t := by
    simpa using mul_le_mul_of_nonneg_left ht hq0
  have h2pi_e : 2 * π * exp 1 < 18 := by
    have hpi : π < 3.1416 := pi_lt_d4
    have he : exp 1 < 2.7182818286 := exp_one_lt_d9
    have he0 : 0 < exp 1 := exp_pos 1
    nlinarith
  have hq18 : (q : ℝ) < (18 : ℕ) := by
    push_cast
    linarith
  have hq_lt : q < 18 := Nat.cast_lt.mp hq18
  exact ⟨le_trans hqt hhi, Nat.le_of_lt_succ hq_lt⟩

/-- AGY task42 helper, CONDITIONAL ON the explicit upper count `zero_count_explicit_upper`:
in the middle range `2 * π ≤ q * t ≤ 2 * π * exp 1`, a bound of the form
`zeroCount χ t ≤ (t / π) * log (q * t / (2 * π * exp 1)) + 13` implies `zeroCount χ t ≤ 13`
because the logarithmic ratio is at most `1` and its logarithm is nonpositive. -/
lemma leaf_mid_zero_count_small_of_main_add_13_agy42 (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (ht : 1 ≤ t)
    (hlo : 2 * π ≤ (q : ℝ) * t) (hhi : (q : ℝ) * t ≤ 2 * π * exp 1)
    (hbound : zeroCount χ t ≤ (t / π) * log ((q : ℝ) * t / (2 * π * exp 1)) + 13) :
    zeroCount χ t ≤ 13 := by
  have ht0 : 0 ≤ t := by linarith
  have htp : 0 ≤ t / π := div_nonneg ht0 pi_pos.le
  have hpos : 0 < (q : ℝ) * t / (2 * π * exp 1) := by
    have : 0 < (q : ℝ) * t := lt_of_lt_of_le (by positivity) hlo
    exact div_pos this (by positivity)
  have hle1 : (q : ℝ) * t / (2 * π * exp 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr hhi
  have hlog : log ((q : ℝ) * t / (2 * π * exp 1)) ≤ 0 :=
    log_nonpos hpos.le hle1
  have hmain : (t / π) * log ((q : ℝ) * t / (2 * π * exp 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos htp hlog
  linarith

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
  have hlog2 : 0.918931 ≤ 0.5 * log (2 * π) := by
    have := LeanLab.HelfgottMajor.log_two_pi_gt
    linarith
  have he : 2 * Real.exp 1 ≤ 5.4365636572 := by
    have := Real.exp_one_lt_d9
    linarith
  have h1 : 0.5 * log (2 * π) ≤ 0.5 * log (q * t) := by linarith
  linarith

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
