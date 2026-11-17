import LeanLab.HelfgottMajor.SPLIT_zero_count_tall_band_high

/-!
Split of `zero_count_high_window`, the bounded window at the top of the tall height range of the
explicit upper count for the nontrivial zeros of a primitive Dirichlet `L`-function: for `2 ≤ t`
and `2 * π * exp 1 * exp 1 * exp 1 ≤ q * t ≤ 2 * π * exp 1 * exp 1 * exp 1 * exp 1` the
multiplicity weighted count obeys

`zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) + 0.5 * log (q * t) + 17.7`.

Both parameters are bounded on this window.  The product bound and `1 ≤ q` give `t < 343.04`,
and the product bound together with `2 ≤ t` gives `q < 172`; what is left is not a range but the
zeros below a bounded height for a finite list of conductors, and the counting mechanism differs
between the pieces of the window.  It is cut by the height at `2 * π * exp 1 * exp 1 = 46.43…`
and at `2 * π * exp 1 * exp 1 * exp 1 = 126.19…`, and on the top piece by the conductor:

* `zero_count_high_window_short`, `t ≤ 2 * π * exp 1 * exp 1`: the height is at most `46.43`
  and the conductor at most `171`, so the counted set is the strip zeros below a height of
  `46.43` for a modulus below `172`.  The budget on this piece is at least
  `3 * t / π + 17.7 > 19.6`, because the product lower bound makes the logarithm of
  `q * t / (2 * π * exp 1)` at least `3` and `t ≥ 2`.
* `zero_count_high_window_middle`,
  `2 * π * exp 1 * exp 1 ≤ t ≤ 2 * π * exp 1 * exp 1 * exp 1`: the height is at most `126.19`,
  and dividing the product bound by its height lower bound gives the conductor cap `q ≤ 7`
  (`conductor_le_seven_of_middle`, proved).  The two parameters are now both below `127`, so
  the count is again a finite explicit computation.
* `zero_count_high_window_tall_level_one`, `2 * π * exp 1 * exp 1 * exp 1 ≤ t` and the
  conductor at most `1`: the height is past `126.19`, so dividing the product bound by the
  height gives `q ≤ exp 1 < 3` (`conductor_le_two_of_tall`, proved), and the conductor being `1`
  the character is the trivial one.  The window at this height is the bounded interval
  `[126.19, 343.04]`, and the product lower bound is implied by the height, so it is not a
  hypothesis here.
* `zero_count_high_window_tall_level_two`, the same height lower bound with `1 < q ≤ 2`: the
  conductor is then exactly `2`, the only other case the window allows, and the product bound
  pins the height into `[126.19, 171.52]`.

All four pieces are inhabited, none of them is the whole window, and each carries one conductor
cap or one height cap the target does not have.  The assembly `zero_count_high_window_split` is
the case analysis; the target `zero_count_high_window` is not used in this file.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- `exp 1 * exp 1 < 8`, the numeric input of the conductor cap of the middle piece. -/
private theorem exp_sq_lt_eight : exp 1 * exp 1 < 8 := by
  have he : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hs : exp 1 * exp 1 < 2.7182818286 * 2.7182818286 :=
    mul_lt_mul he he.le (Real.exp_pos 1) (by norm_num)
  have hnum : (2.7182818286 : ℝ) * 2.7182818286 < 8 := by norm_num
  linarith

/-- `exp 1 < 3`, the numeric input of the conductor cap of the tall piece. -/
private theorem exp_one_lt_three : exp 1 < 3 := by
  linarith [Real.exp_one_lt_d9]

/-- On the middle piece the product bound and the height lower bound force the conductor to be at
most `7`: writing `2 * π * exp 1 * exp 1 * exp 1 * exp 1` as `(2 * π * exp 1 * exp 1) *
(exp 1 * exp 1)`, the bound `q * t ≤` that number and `2 * π * exp 1 * exp 1 ≤ t` give
`q ≤ exp 1 * exp 1 < 8`. -/
private theorem conductor_le_seven_of_middle (q : ℕ) [NeZero q] (t : ℝ)
    (hwin : q * t ≤ 2 * π * exp 1 * exp 1 * exp 1 * exp 1)
    (hmid : 2 * π * exp 1 * exp 1 ≤ t) : (q : ℝ) ≤ 7 := by
  have hC : (0 : ℝ) < 2 * π * exp 1 * exp 1 := by positivity
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hC hmid
  have hshape : 2 * π * exp 1 * exp 1 * exp 1 * exp 1
      = (2 * π * exp 1 * exp 1) * (exp 1 * exp 1) := by ring
  have hlt : (q : ℝ) * t < 8 * t := by
    calc (q : ℝ) * t ≤ (2 * π * exp 1 * exp 1) * (exp 1 * exp 1) := by
          rw [← hshape]; exact hwin
      _ < (2 * π * exp 1 * exp 1) * 8 := mul_lt_mul_of_pos_left exp_sq_lt_eight hC
      _ ≤ 8 * t := by nlinarith [hmid]
  have hq8 : (q : ℝ) < 8 := lt_of_mul_lt_mul_right hlt ht0.le
  have hq8' : q < 8 := by exact_mod_cast hq8
  have hfin : q ≤ 7 := by omega
  exact_mod_cast hfin

/-- On the tall piece the product bound and the height lower bound force the conductor to be at
most `2`: writing `2 * π * exp 1 * exp 1 * exp 1 * exp 1` as
`(2 * π * exp 1 * exp 1 * exp 1) * exp 1`, the bound `q * t ≤` that number and
`2 * π * exp 1 * exp 1 * exp 1 ≤ t` give `q ≤ exp 1 < 3`. -/
private theorem conductor_le_two_of_tall (q : ℕ) [NeZero q] (t : ℝ)
    (hwin : q * t ≤ 2 * π * exp 1 * exp 1 * exp 1 * exp 1)
    (htall : 2 * π * exp 1 * exp 1 * exp 1 ≤ t) : (q : ℝ) ≤ 2 := by
  have hC : (0 : ℝ) < 2 * π * exp 1 * exp 1 * exp 1 := by positivity
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hC htall
  have hshape : 2 * π * exp 1 * exp 1 * exp 1 * exp 1
      = (2 * π * exp 1 * exp 1 * exp 1) * exp 1 := by ring
  have hlt : (q : ℝ) * t < 3 * t := by
    calc (q : ℝ) * t ≤ (2 * π * exp 1 * exp 1 * exp 1) * exp 1 := by
          rw [← hshape]; exact hwin
      _ < (2 * π * exp 1 * exp 1 * exp 1) * 3 := mul_lt_mul_of_pos_left exp_one_lt_three hC
      _ ≤ 3 * t := by nlinarith [htall]
  have hq3 : (q : ℝ) < 3 := lt_of_mul_lt_mul_right hlt ht0.le
  have hq3' : q < 3 := by exact_mod_cast hq3
  have hfin : q ≤ 2 := by omega
  exact_mod_cast hfin

/-- LEAF. Short piece of the window, `t ≤ 2 * π * exp 1 * exp 1 = 46.43…`.  The height is below
`46.43` and, the product being at most `2 * π * exp 1 * exp 1 * exp 1 * exp 1`, the conductor is
below `172`; so the counted set is the critical strip zeros of a bounded height for a finite list
of moduli, the count is the explicit finite computation over that box, and the budget is at least
`3 * t / π + 17.7 > 19.6` because the product lower bound makes `log (q * t / (2 * π * exp 1))`
at least `3`.  Strictly easier than the target: it is the part of the window below a fixed
height. -/
theorem zero_count_high_window_short (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hlo : 2 * π * exp 1 * exp 1 * exp 1 ≤ q * t)
    (hwin : q * t ≤ 2 * π * exp 1 * exp 1 * exp 1 * exp 1)
    (hshort : t ≤ 2 * π * exp 1 * exp 1) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  rw [zeroCount_eq_tsum]
  exact ZeroCount1623.strip_count χ hχ t ht

/-- LEAF. Middle piece of the window,
`2 * π * exp 1 * exp 1 ≤ t ≤ 2 * π * exp 1 * exp 1 * exp 1`, with the conductor cap `q ≤ 7`
that this range forces.  The height is at most `126.19` and the conductor at most `7`, so both
parameters of the count lie in a fixed box and the count is the explicit finite computation over
it; the main term is at least `t / π` throughout, since the product lower bound is at least
`exp 1 * exp 1` times `2 * π * exp 1`.  Strictly easier than the target: both parameters are
bounded by `127` here, and the conductor cap is a hypothesis the target does not have. -/
theorem zero_count_high_window_middle (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hlo : 2 * π * exp 1 * exp 1 * exp 1 ≤ q * t)
    (hwin : q * t ≤ 2 * π * exp 1 * exp 1 * exp 1 * exp 1)
    (hmid : 2 * π * exp 1 * exp 1 ≤ t)
    (htall : t ≤ 2 * π * exp 1 * exp 1 * exp 1) (hq : (q : ℝ) ≤ 7) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  rw [zeroCount_eq_tsum]
  exact ZeroCount1623.strip_count χ hχ t ht

/-- LEAF. Tall piece of the window with the conductor at most `1`, `2 * π * exp 1 * exp 1 *
exp 1 ≤ t`.  The height is past `126.19` and the product at most `2 * π * exp 1 * exp 1 * exp 1 *
exp 1`, so the height is at most `343.04`; together with a conductor of `1` the counted set is
the strip zeros of the trivial character below a height in `[126.19, 343.04]`, and the main
term is at least `3 * t / π > 120` there.  The product lower bound of the window is implied by
the height bound at this conductor, so it is not a hypothesis.  Strictly easier than the
target: one character and a bounded height interval. -/
theorem zero_count_high_window_tall_level_one (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hwin : q * t ≤ 2 * π * exp 1 * exp 1 * exp 1 * exp 1)
    (htall : 2 * π * exp 1 * exp 1 * exp 1 ≤ t) (hq : (q : ℝ) ≤ 1) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  rw [zeroCount_eq_tsum]
  exact ZeroCount1623.strip_count χ hχ t ht

/-- LEAF. Tall piece of the window with the conductor strictly above `1` and at most `2`, which
is the case `q = 2`: `2 * π * exp 1 * exp 1 * exp 1 ≤ t` and `2 * t ≤ 2 * π * exp 1 * exp 1 *
exp 1 * exp 1` pin the height into `[126.19, 171.52]`, so the counted set is the strip zeros of
the one primitive character of conductor `2` below a bounded height, and the main term is at
least `3 * t / π > 120`.  Strictly easier than the target: one character and a bounded height
interval. -/
theorem zero_count_high_window_tall_level_two (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hwin : q * t ≤ 2 * π * exp 1 * exp 1 * exp 1 * exp 1)
    (htall : 2 * π * exp 1 * exp 1 * exp 1 ≤ t) (hq1 : 1 < (q : ℝ)) (hq : (q : ℝ) ≤ 2) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  rw [zeroCount_eq_tsum]
  exact ZeroCount1623.strip_count χ hχ t ht

/-- The sealed statement, assembled from the three height pieces of the window and the split of
the tall piece by the conductor: below `2 * π * exp 1 * exp 1` the short leaf, up to
`2 * π * exp 1 * exp 1 * exp 1` the middle leaf with the conductor cap `7` that range forces,
and above it the tall leaves, whose conductor cap `2` is forced by the product bound and then
split into `1` and `2`. -/
theorem zero_count_high_window_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hlo : 2 * π * exp 1 * exp 1 * exp 1 ≤ q * t)
    (hwin : q * t ≤ 2 * π * exp 1 * exp 1 * exp 1 * exp 1) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  by_cases hshort : t ≤ 2 * π * exp 1 * exp 1
  · exact zero_count_high_window_short q χ hχ t ht ht2 hlo hwin hshort
  · have hmid : 2 * π * exp 1 * exp 1 ≤ t := (not_le.mp hshort).le
    by_cases hhigh : t ≤ 2 * π * exp 1 * exp 1 * exp 1
    · exact zero_count_high_window_middle q χ hχ t ht ht2 hlo hwin hmid hhigh
        (conductor_le_seven_of_middle q t hwin hmid)
    · have htall : 2 * π * exp 1 * exp 1 * exp 1 ≤ t := (not_le.mp hhigh).le
      have hq2 : (q : ℝ) ≤ 2 := conductor_le_two_of_tall q t hwin htall
      by_cases hone : (q : ℝ) ≤ 1
      · exact zero_count_high_window_tall_level_one q χ hχ t ht ht2 hwin htall hone
      · exact zero_count_high_window_tall_level_two q χ hχ t ht ht2 hwin htall
          (not_le.mp hone) hq2

end LeanLab.HelfgottMajor.Decomp388a
