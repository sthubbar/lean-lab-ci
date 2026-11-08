import LeanLab.HelfgottMajor.SPLIT_zero_count_explicit_upper

/-!
Split of the short height range of the explicit upper count for the nontrivial zeros of a
primitive Dirichlet `L`-function.

On the range `q * t ≤ 2 * π` with `t ≥ 1` the height is at most `2 * π / q`, and the
multiplicity weighted count only grows with the height, so the whole range is controlled by
the single endpoint height `t = 2 * π / q`, where the sealed right hand side is at its
smallest.  The three steps are therefore: the count is monotone in the height; the count at
the endpoint `2 * π / q` is bounded by the sealed right hand side evaluated there; and the
endpoint value of the right hand side is at most the right hand side at the interior height,
because the logarithm only gains `log (2 * π / (q * t))` while the linear main term gains
`(2 / q - t / π) * log (2 * π * exp 1)`, which is larger.  The assembly at the end of the
file is exactly that chain of three inequalities.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- LEAF. Monotonicity of the multiplicity weighted count in the height.  Raising the
height can only add nontrivial zeros to the counted set of `zeroCount`, and every weight is
a nonnegative natural number cast to a real, so the weighted sum over the plane grows.  This
is the step that carries the count from an interior height up to the endpoint `2 * π / q` of
the short range. -/
theorem zeroCount_mono_height (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    {s t : ℝ} (hst : s ≤ t) : zeroCount χ s ≤ zeroCount χ t := by
  sorry

/-- LEAF. The counting input of the short range, at the endpoint height `2 * π / q`.  This is
the multiplicity weighted count of the nontrivial zeros of a primitive character below the
single height `q * t = 2 * π`, bounded by the sealed right hand side evaluated at that height,
that is by `0.5 * log (2 * π) + 17.7 - (2 / q) * log (2 * π * exp 1)`.  It is the only step
of this split that uses primitivity, and it needs no interior height. -/
theorem zero_count_endpoint_short (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    zeroCount χ (2 * π / q) ≤ 0.5 * log (2 * π) + 17.7 - (2 / q) * log (2 * π * exp 1) := by
  sorry

/-- LEAF. The elementary endpoint comparison on the short range.  For `1 ≤ t` with
`q * t ≤ 2 * π`, the value of the sealed right hand side at the endpoint `2 * π / q` is at
most its value at the interior height `t`.  The difference is
`log (2 * π / (q * t)) / 2 + (t / π - 2 / q) * log (2 * π * exp 1)`, whose first term is at
most zero on the range and whose second term is at least zero there and dominates the first,
the case `t = 1` being the worst one. -/
lemma short_height_endpoint_le_aux (t : ℝ) (ht : 1 ≤ t) (u : ℝ) (hu : t ≤ u) :
    0.5 * log u - (u / π) * log (2 * π * exp 1) ≤
    0.5 * log t - (t / π) * log (2 * π * exp 1) := by
  have ht_pos : 0 < t := by linarith
  have hu_pos : 0 < u := by linarith
  have h1 : log (u / t) ≤ (u - t) / t := by
    have h_sub : log (u / t) ≤ u / t - 1 := log_le_sub_one_of_pos (div_pos hu_pos ht_pos)
    have h_eq : u / t - 1 = (u - t) / t := by
      rw [sub_div, div_self ht_pos.ne']
    rwa [h_eq] at h_sub
  have h2 : (u - t) / t ≤ u - t := by
    have H : 0 ≤ u - t := sub_nonneg.mpr hu
    exact div_le_self H ht
  have h4 : 0.5 * (log u - log t) ≤ 0.5 * (u - t) := by
    have hlog : log u - log t = log (u / t) := by rw [log_div hu_pos.ne' ht_pos.ne']
    linarith
  have hL : 0.5 ≤ (1 / π) * log (2 * π * exp 1) := by
    have H1 : 0 < 2 * π := by positivity
    have H2 : 0 < exp 1 := exp_pos 1
    rw [log_mul H1.ne' H2.ne', log_exp]
    have h_pi_bound : 0.5 * π - 1 ≤ 1 := by
      have : π ≤ 4 := pi_lt_four.le
      linarith
    have h_exp : exp 1 ≤ 3 := by
      have : exp 1 ≤ 2.7182818286 := exp_one_lt_d9.le
      linarith
    have h_2pi : 6 ≤ 2 * π := by
      have : 3 ≤ π := pi_gt_three.le
      linarith
    have h_exp_le_2pi : exp 1 ≤ 2 * π := by linarith
    have h_log : 1 ≤ log (2 * π) := by
      rw [← log_exp 1]
      apply (log_le_log_iff H2 H1).mpr h_exp_le_2pi
    have h_ineq : 0.5 * π ≤ (log (2 * π) + 1) := by linarith
    have h_pi_pos : 0 < π := pi_pos
    rw [div_mul_eq_mul_div, one_mul]
    exact (le_div_iff₀ h_pi_pos).mpr h_ineq
  have h5 : 0.5 * (u - t) ≤ (u - t) * (1 / π) * log (2 * π * exp 1) := by
    have H1 : 0 ≤ u - t := sub_nonneg.mpr hu
    nlinarith
  have h6 : 0.5 * log u - 0.5 * log t ≤ (u / π - t / π) * log (2 * π * exp 1) := by
    calc 0.5 * log u - 0.5 * log t
      _ = 0.5 * (log u - log t) := by ring
      _ ≤ 0.5 * (u - t) := h4
      _ ≤ (u - t) * (1 / π) * log (2 * π * exp 1) := h5
      _ = (u / π - t / π) * log (2 * π * exp 1) := by ring
  linarith

theorem short_height_endpoint_le (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t)
    (hqt : q * t ≤ 2 * π) :
    0.5 * log (2 * π) + 17.7 - (2 / q) * log (2 * π * exp 1) ≤
      0.5 * log (q * t) + 17.7 - (t / π) * log (2 * π * exp 1) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have h2pi : 0 < 2 * π := by positivity
  have hpi : 0 < π := pi_pos
  have ht_u : t ≤ 2 * π / q := by
    rw [le_div_iff₀ hq]
    linarith
  have H := short_height_endpoint_le_aux t ht (2 * π / q) ht_u
  have h_eq : 0.5 * log (2 * π) + 17.7 - (2 / q) * log (2 * π * exp 1) -
    (0.5 * log (q * t) + 17.7 - (t / π) * log (2 * π * exp 1)) =
    0.5 * log (2 * π / q) - (2 * π / q) / π * log (2 * π * exp 1) -
    (0.5 * log t - (t / π) * log (2 * π * exp 1)) := by
    have e1 : log (q * t) = log q + log t := log_mul hq.ne' (by linarith)
    have e2 : log (2 * π / q) = log (2 * π) - log q := log_div h2pi.ne' hq.ne'
    have e3 : (2 * π / q) / π = 2 / q := by
      rw [div_div]
      have : ↑q * π = π * ↑q := mul_comm _ _
      rw [this, ← div_div, mul_div_cancel_right₀ _ hpi.ne']
    calc 0.5 * log (2 * π) + 17.7 - (2 / q) * log (2 * π * exp 1) - (0.5 * log (q * t) + 17.7 - (t / π) * log (2 * π * exp 1))
      _ = 0.5 * log (2 * π) - 0.5 * log (q * t) - (2 / q) * log (2 * π * exp 1) + (t / π) * log (2 * π * exp 1) := by ring
      _ = 0.5 * log (2 * π) - 0.5 * (log q + log t) - (2 / q) * log (2 * π * exp 1) + (t / π) * log (2 * π * exp 1) := by rw [e1]
      _ = 0.5 * (log (2 * π) - log q) - 0.5 * log t - (2 / q) * log (2 * π * exp 1) + (t / π) * log (2 * π * exp 1) := by ring
      _ = 0.5 * log (2 * π / q) - 0.5 * log t - (2 / q) * log (2 * π * exp 1) + (t / π) * log (2 * π * exp 1) := by rw [e2]
      _ = 0.5 * log (2 * π / q) - (2 * π / q) / π * log (2 * π * exp 1) - (0.5 * log t - (t / π) * log (2 * π * exp 1)) := by rw [e3]; ring
  linarith

/-- The explicit upper count at short heights, assembled from the endpoint count, the
monotonicity of the count in the height and the endpoint comparison. -/
theorem zero_count_short_height_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (hqt : q * t ≤ 2 * π) :
    zeroCount χ t ≤ 0.5 * log (q * t) + 17.7 - (t / π) * log (2 * π * exp 1) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hmono : t ≤ 2 * π / q := by
    rw [le_div_iff₀ hq]
    linarith
  have h1 := zeroCount_mono_height q χ hmono
  have h2 := zero_count_endpoint_short q χ hχ
  have h3 := short_height_endpoint_le q t ht hqt
  linarith
