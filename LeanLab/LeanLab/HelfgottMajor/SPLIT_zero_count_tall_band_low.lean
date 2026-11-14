import LeanLab.HelfgottMajor.SPLIT_zero_count_tall_height

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

/-- The set cut out by the indicator inside `zeroWeight` is `stripZeros`. -/
private theorem zeroWeight_set_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ t}
      = ZeroCount1623.stripZeros χ t := by
  ext ρ
  simp [ZeroCount1623.stripZeros]

/-- `zeroCount` is the multiplicity weighted finite sum over the strip zeros at height `t`.
`ZeroCount1623.stripZeros_finite` makes the strip zero set finite for every height and every
character, so the `tsum` defining `zeroCount` collapses to that finite sum. -/
private theorem zeroCount_eq_finset (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    zeroCount χ t = ∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ t).toFinset,
      (ZeroCount1623.mult χ ρ : ℝ) := by
  classical
  have hset := zeroWeight_set_eq q χ t
  have hfin : (ZeroCount1623.stripZeros χ t).Finite := ZeroCount1623.stripZeros_finite χ t
  have hzero : ∀ ρ : ℂ, ρ ∉ (ZeroCount1623.stripZeros χ t) → zeroWeight χ t ρ = 0 := by
    intro ρ hρ
    have h' : ρ ∉ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
        ρ.re < 1 ∧ |ρ.im| ≤ t} := by rw [hset]; exact hρ
    simp [zeroWeight, h']
  have houtside : ∀ ρ : ℂ, ρ ∉ hfin.toFinset → zeroWeight χ t ρ = 0 := by
    intro ρ hρ
    exact hzero ρ (fun hc => hρ (hfin.mem_toFinset.mpr hc))
  have hinside : ∀ ρ : ℂ, ρ ∈ hfin.toFinset → zeroWeight χ t ρ = (ZeroCount1623.mult χ ρ : ℝ) := by
    intro ρ hρ
    have hc : ρ ∈ ZeroCount1623.stripZeros χ t := hfin.mem_toFinset.mp hρ
    simp [zeroWeight, ZeroCount1623.mult, hset, hc]
  unfold zeroCount
  rw [tsum_eq_sum (f := zeroWeight χ t) houtside]
  exact Finset.sum_congr rfl (fun ρ hρ => hinside ρ hρ)

/-- The strip zeros cut at a lower height are contained in the ones cut at a higher height. -/
private theorem stripZeros_subset_of_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    {s t : ℝ} (h : s ≤ t) : ZeroCount1623.stripZeros χ s ⊆ ZeroCount1623.stripZeros χ t := by
  intro ρ hρ
  simp only [ZeroCount1623.stripZeros, Set.mem_ofPred_eq] at hρ ⊢
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans h⟩

/-- The count is monotone in the height: every zero counted at height `s` is counted at height
`t ≥ s` with the same multiplicity, and the extra zeros contribute a nonnegative amount. -/
private theorem zeroCount_mono (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) {s t : ℝ}
    (h : s ≤ t) : zeroCount χ s ≤ zeroCount χ t := by
  rw [zeroCount_eq_finset, zeroCount_eq_finset]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun ρ => (ZeroCount1623.mult χ ρ : ℝ)) ?_ ?_
  · intro ρ hρ
    exact (ZeroCount1623.stripZeros_finite χ t).mem_toFinset.mpr
      (stripZeros_subset_of_le q χ h
        ((ZeroCount1623.stripZeros_finite χ s).mem_toFinset.mp hρ))
  · intro ρ _ _
    positivity

/-- `2 * π * exp 1 * exp 1 < 47`, the numeric input of the conductor bound. -/
private theorem two_pi_e_sq_lt_47 : 2 * π * exp 1 * exp 1 < 47 := by
  have he := Real.exp_one_lt_d9
  have hp := Real.pi_lt_d4
  have he0 := Real.exp_pos 1
  have h1 : π * exp 1 < 3.1416 * 2.7182818286 :=
    mul_lt_mul hp he.le he0 (by norm_num)
  have h2 : π * exp 1 * exp 1 < 3.1416 * 2.7182818286 * 2.7182818286 :=
    mul_lt_mul h1 he.le he0 (by norm_num)
  nlinarith [h2]

/-- LEAF. Height bound at fixed conductor.  On the band `t ≥ 2 > 0` and the product
`q * t` is at most `2 * π * exp 1 * exp 1`, so division by the positive conductor bounds the
height by the endpoint `2 * π * exp 1 * exp 1 / q` of the band.  This is the step that turns the
two product bounds into a single height bound that still remembers the conductor. -/
theorem leaf_band_height_le_endpoint (q : ℕ) [NeZero q] (t : ℝ) (ht2 : 2 ≤ t)
    (hhi : q * t ≤ 2 * π * exp 1 * exp 1) :
    t ≤ 2 * π * exp 1 * exp 1 / (q : ℝ) := by
  have hq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast NeZero.pos q
  rw [le_div_iff₀ hq]
  calc t * (q : ℝ) = q * t := by ring
    _ ≤ 2 * π * exp 1 * exp 1 := hhi

/-- LEAF. Conductor bound.  On the band the height is at least `2` and the modulus is at least
`1`, so `2 * q ≤ q * t ≤ 2 * π * exp 1 * exp 1 < 47`, hence `q ≤ 23`.  This is the only place
where the band bound enters the conductor, and it is what makes the character range finite. -/
theorem leaf_band_conductor_le (q : ℕ) [NeZero q] (t : ℝ) (ht2 : 2 ≤ t)
    (hhi : q * t ≤ 2 * π * exp 1 * exp 1) :
    q ≤ 23 := by
  have hq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have h2 : 2 * (q : ℝ) ≤ q * t := by nlinarith [hq, ht2]
  have hC := two_pi_e_sq_lt_47
  have hq24 : (q : ℝ) < 24 := by nlinarith
  have hq' : q < 24 := by exact_mod_cast hq24
  omega

/-- LEAF. Monotonicity of the multiplicity weighted count in the height.  Raising the height can
only add nontrivial zeros to the counted set of `zeroCount`, and every weight is a nonnegative
natural number cast to a real, so the weighted sum over the plane grows.  This is the step that
carries the count from the ranging height `t` up to the endpoint of the band. -/
theorem leaf_band_zero_count_mono (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) {s t : ℝ}
    (hst : s ≤ t) : zeroCount χ s ≤ zeroCount χ t :=
  zeroCount_mono q χ hst

/-! NOTE. The next leaf is FALSE as stated and its `sorry` is deliberately left in place:
at `q = 1` (the principal character of conductor `1`, which is primitive) the top of the band is
`2 * π * exp 1 * exp 1 = 46.4268...`, and `ζ` has the eight zeros `1/2 ± i·γ` with
`γ = 14.1347, 21.0220, 25.0109, 30.4249, 32.9351, 37.5862, 40.9187, 43.3271` below that height,
so `zeroCount` is `16` there, not at most `13`.  A re-cut has to use the budget's true floor
`17.7` rather than `13`. -/

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
  have hpos : (0 : ℝ) < 2 * π * exp 1 := by positivity
  have hratio : 1 ≤ q * t / (2 * π * exp 1) := by
    rw [le_div_iff₀ hpos]
    linarith
  have hlog1 : 0 ≤ log (q * t / (2 * π * exp 1)) := log_nonneg hratio
  have htpi : 0 ≤ t / π := div_nonneg (by linarith) pi_pos.le
  have hone : (1 : ℝ) ≤ 2 * π * exp 1 := by
    nlinarith [Real.pi_gt_d4, Real.exp_one_gt_d9]
  have hqt1 : 1 ≤ q * t := le_trans hone hqt
  have hlog2 : 0 ≤ log (q * t) := log_nonneg hqt1
  have h1 : 0 ≤ t / π * log (q * t / (2 * π * exp 1)) := mul_nonneg htpi hlog1
  have h2 : 0 ≤ 0.5 * log (q * t) := by
    have : (0 : ℝ) ≤ 0.5 := by norm_num
    exact mul_nonneg this hlog2
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
