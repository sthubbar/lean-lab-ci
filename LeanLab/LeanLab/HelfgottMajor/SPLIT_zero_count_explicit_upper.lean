import LeanLab.HelfgottMajor.Decomp388a

/-!
Split of the explicit upper count for the nontrivial zeros of a primitive Dirichlet
`L`-function below a height `t`.  The single inequality is cut along the three height
ranges on which the main term `(t / π) * log (q * t / (2 * π * exp 1))` behaves
differently: for `q * t` at most `2 * π` that term is bounded below by its value at
`q * t = 1`, for `q * t` between `2 * π` and `2 * π * exp 1` it is bounded below by
`-t / π`, and for larger `q * t` it is kept as it stands.  The assembly at the end of
the file is exactly that case split.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- LEAF. Short heights, `q * t ≤ 2 * π`. On this range the main term of the count
is at its worst at `q * t = 1`, so the count is bounded by the height term alone,
shifted down by the value of the main term there: the estimate is
`log (q * t) / 2 + 17.7 - (t / π) * log (2 * π * exp 1)`. -/
theorem zero_count_short_height (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (hqt : q * t ≤ 2 * π) :
    zeroCount χ t ≤ 0.5 * log (q * t) + 17.7 - (t / π) * log (2 * π * exp 1) := by
  sorry

/-- LEAF. Middle heights, `2 * π ≤ q * t ≤ 2 * π * exp 1`.  On this range the main
term of the count lies between `-t / π` and `0`, so it is dropped and the count is
bounded by `log (q * t) / 2 + 17.7 - t / π`. -/
theorem zero_count_mid_height (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t)
    (hlo : 2 * π ≤ q * t) (hhi : q * t ≤ 2 * π * exp 1) :
    zeroCount χ t ≤ 0.5 * log (q * t) + 17.7 - t / π := by
  sorry

/-- LEAF. Tall heights, `2 * π * exp 1 ≤ q * t`.  This leaf keeps the main term and
carries the counting of the zeros in the critical strip up to height `t`, including
the contribution of the archimedean factor and the halving of the height term. -/
theorem zero_count_tall_height (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (hqt : 2 * π * exp 1 ≤ q * t) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  sorry

/-- The explicit upper count, assembled from the three height ranges. -/
theorem zero_count_explicit_upper_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have ht0 : 0 < t := by linarith
  have hqt : (0 : ℝ) < q * t := mul_pos hq ht0
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hqt1 : (1 : ℝ) ≤ q * t := by nlinarith
  have htp : 0 ≤ t / π := div_nonneg ht0.le pi_pos.le
  have hsplit : log (q * t / (2 * π * exp 1)) = log (q * t) - log (2 * π * exp 1) :=
    log_div hqt.ne' (by positivity)
  have hlogqt : 0 ≤ log (q * t) := log_nonneg hqt1
  have hCm : log (2 * π * exp 1) = log (2 * π) + 1 := by
    rw [log_mul (by positivity) (exp_pos 1).ne', log_exp]
  rcases le_total (q * t) (2 * π) with hsmall | hbig
  · have h1 := zero_count_short_height q χ hχ t ht hsmall
    have hlog_ge : -log (2 * π * exp 1) ≤ log (q * t / (2 * π * exp 1)) := by
      rw [hsplit]; linarith
    have hmain : -(t / π) * log (2 * π * exp 1) ≤
        (t / π) * log (q * t / (2 * π * exp 1)) := by
      have hm := mul_le_mul_of_nonneg_left hlog_ge htp
      linarith
    linarith [h1, hmain]
  · rcases le_total (q * t) (2 * π * exp 1) with hmid | hbig2
    · have h2 := zero_count_mid_height q χ hχ t ht hbig hmid
      have hlog2 : log (2 * π) ≤ log (q * t) := log_le_log (by positivity) hbig
      have hlog_ge : -(1 : ℝ) ≤ log (q * t / (2 * π * exp 1)) := by
        rw [hsplit]; linarith
      have hmain : -(t / π) * 1 ≤ (t / π) * log (q * t / (2 * π * exp 1)) := by
        have hm := mul_le_mul_of_nonneg_left hlog_ge htp
        linarith
      linarith [h2, hmain]
    · exact zero_count_tall_height q χ hχ t ht hbig2
