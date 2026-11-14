import LeanLab.HelfgottMajor.SPLIT_zero_count_tall_height
import LeanLab.HelfgottMajor.SPLIT_leaf_mid_zero_count_small

/-!
Split of `zero_count_tall_band_low`, the first bounded band of the tall height range of the
explicit upper count for the nontrivial zeros of a primitive Dirichlet `L`-function: on

`2 ≤ t` and `2 * π * exp 1 ≤ q * t ≤ 2 * π * exp 1 * exp 1`

the count is bounded by
`t / π * log (q * t / (2 * π * exp 1)) + 0.5 * log (q * t) + 17.7`.

On this range the product `q * t` is trapped between two absolute constants, so no quantity in
the problem grows: the main term `(t / π) * log (q * t / (2 * π * exp 1))` lies in `[0, t / π]`,
the half log term is bounded, and the count of nontrivial zeros with `|Im| ≤ t` is a bounded
number.  The way the band is used is therefore

* the product bound gives the conductor bound `q ≤ 23`, since `2 ≤ t` forces
  `2 * q ≤ q * t ≤ 2 * π * exp 1 * exp 1`;
* the same product bound gives the height bound only after division by `q`, which is the
  endpoint `2 * π * exp 1 * exp 1 / q` of the band at fixed conductor;
* the count is monotone in the height, so it is carried from `t` up to that endpoint;
* at the endpoint the product is constant and the count is a bounded number, which the fixed
  `17.7` and the two nonnegative logarithmic terms absorb.

The assembly `zero_count_tall_band_low_split` is that chain, and it has no open goal of its
own.  The target `zero_count_tall_band_low` is not used in this file.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- LEAF. Height bound at fixed conductor.  On the band `t ≥ 2 > 0` and the product
`q * t` is at most `2 * π * exp 1 * exp 1`, so division by the positive conductor bounds the
height by the endpoint `2 * π * exp 1 * exp 1 / q` of the band.  This is the step that turns the
two product bounds into a single height bound that still remembers the conductor. -/
theorem leaf_band_height_le_endpoint (q : ℕ) [NeZero q] (t : ℝ) (ht2 : 2 ≤ t)
    (hhi : q * t ≤ 2 * π * exp 1 * exp 1) :
    t ≤ 2 * π * exp 1 * exp 1 / (q : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  rw [le_div_iff₀ hq0, mul_comm]
  exact hhi

/-- LEAF. Conductor bound.  On the band the height is at least `2` and the modulus is at least
`1`, so `2 * q ≤ q * t ≤ 2 * π * exp 1 * exp 1 < 47`, hence `q ≤ 23`.  This is the only place
where the band bound enters the conductor, and it is what makes the character range finite. -/
theorem leaf_band_conductor_le (q : ℕ) [NeZero q] (t : ℝ) (ht2 : 2 ≤ t)
    (hhi : q * t ≤ 2 * π * exp 1 * exp 1) :
    q ≤ 23 := by
  have h2q : 2 * (q : ℝ) ≤ (q : ℝ) * t := by
    have h0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    nlinarith [ht2, h0]
  have hprod : (2 : ℝ) * π * exp 1 * exp 1 < 48 := by
    have hpi : π < 3.1416 := Real.pi_lt_d4
    have he : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have he0 : 0 < exp 1 := exp_pos 1
    nlinarith
  have hq24 : (q : ℝ) < 24 := by linarith
  have hq_lt : q < 24 := Nat.cast_lt.mp hq24
  omega

/-- LEAF. Monotonicity of the multiplicity weighted count in the height.  Raising the height can
only add nontrivial zeros to the counted set of `zeroCount`, and every weight is a nonnegative
natural number cast to a real, so the weighted sum over the plane grows.  This is the step that
carries the count from the ranging height `t` up to the endpoint of the band. -/
theorem leaf_band_zero_count_mono (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) {s t : ℝ}
    (hst : s ≤ t) : zeroCount χ s ≤ zeroCount χ t := by
  exact leaf_mid_zero_count_mono q χ hst

/-- LEAF. The counting content of the band.  At the top of the band, where the product
`q * t` is the fixed number `2 * π * exp 1 * exp 1` and the height is `2 * π * exp 1 * exp 1 / q`,
a primitive character of conductor at most `23` has at most `13` multiplicity weighted
nontrivial zeros in the critical strip.  The product is fixed here and the two range hypotheses
of the target are replaced by the conductor condition `q ≤ 23`, so this is a strictly smaller
statement than the target: it lives at one height per conductor and carries no budget. -/
theorem leaf_band_zero_count_at_top (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≤ 23) :
    zeroCount χ (2 * π * exp 1 * exp 1 / (q : ℝ)) ≤ 13 := by
  sorry

/-- LEAF. The budget of the band is nonnegative, so it covers the bounded count.  On the range
`t ≥ 1 ≥ 0` and `q * t ≥ 2 * π * exp 1 = 17.07…` the two logarithmic terms are
`t / π * log (q * t / (2 * π * exp 1)) ≥ 0` and `0.5 * log (q * t) ≥ 0`, hence the right side is
at least `17.7`, which is more than `13`.  This is the arithmetic that spends the fixed `17.7`. -/
theorem leaf_band_budget_nonneg (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t)
    (hqt : 2 * π * exp 1 ≤ q * t) :
    13 ≤ t / π * log (q * t / (2 * π * exp 1)) + 0.5 * log (q * t) + 17.7 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hpe : (0 : ℝ) < 2 * π * exp 1 := by positivity
  have hbig : (1 : ℝ) ≤ 2 * π * exp 1 := by
    nlinarith [Real.pi_gt_three, Real.exp_one_gt_d9, exp_pos 1]
  have hratio : (1 : ℝ) ≤ q * t / (2 * π * exp 1) := by
    rw [le_div_iff₀ hpe]
    linarith
  have hlog1 : (0 : ℝ) ≤ log (q * t / (2 * π * exp 1)) := Real.log_nonneg hratio
  have hlogqt : (0 : ℝ) ≤ log (q * t) :=
    Real.log_nonneg (by linarith)
  have hmain : (0 : ℝ) ≤ t / π * log (q * t / (2 * π * exp 1)) :=
    mul_nonneg (div_nonneg ht0 Real.pi_pos.le) hlog1
  have hhalf : (0 : ℝ) ≤ 0.5 * log (q * t) :=
    mul_nonneg (by norm_num) hlogqt
  linarith

/-- The sealed statement, assembled from the endpoint height bound, the conductor bound, the
monotonicity of the count in the height, the count at the top of the band and the nonnegativity
of the budget. -/
theorem zero_count_tall_band_low_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (ht2 : 2 ≤ t)
    (hqt : 2 * π * exp 1 ≤ q * t) (hhi : q * t ≤ 2 * π * exp 1 * exp 1) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  have hH : t ≤ 2 * π * exp 1 * exp 1 / (q : ℝ) :=
    leaf_band_height_le_endpoint q t ht2 hhi
  have hC : q ≤ 23 := leaf_band_conductor_le q t ht2 hhi
  have hM : zeroCount χ t ≤ zeroCount χ (2 * π * exp 1 * exp 1 / (q : ℝ)) :=
    leaf_band_zero_count_mono q χ (s := t) (t := 2 * π * exp 1 * exp 1 / (q : ℝ)) hH
  have hP : zeroCount χ (2 * π * exp 1 * exp 1 / (q : ℝ)) ≤ 13 :=
    leaf_band_zero_count_at_top q χ hχ hC
  have hB : 13 ≤ t / π * log (q * t / (2 * π * exp 1)) + 0.5 * log (q * t) + 17.7 :=
    leaf_band_budget_nonneg q t ht hqt
  linarith

end LeanLab.HelfgottMajor.Decomp388a
