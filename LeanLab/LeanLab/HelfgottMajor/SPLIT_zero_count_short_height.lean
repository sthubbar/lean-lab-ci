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
theorem short_height_endpoint_le (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t)
    (hqt : q * t ≤ 2 * π) :
    0.5 * log (2 * π) + 17.7 - (2 / q) * log (2 * π * exp 1) ≤
      0.5 * log (q * t) + 17.7 - (t / π) * log (2 * π * exp 1) := by
  sorry

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
