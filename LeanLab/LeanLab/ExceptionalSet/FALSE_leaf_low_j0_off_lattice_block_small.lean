import LeanLab.ExceptionalSet.SPLIT_leaf_low_j0_large_phase_localizes

/-!
The leaf `leaf_low_j0_off_lattice_block_small` of
`ExceptionalSet/SPLIT_leaf_low_j0_large_phase_localizes.lean` is FALSE as written.

That leaf asks for the pointwise bound `‖blockPhase‖ ≤ N E ^ (-(5 / 6))` at every `N`, every
positive `δ` and every positive `κ`, with no eventual threshold in `N` and no cap on `κ`. For a
fixed `N` the right side tends to zero as `κ` grows, because `E = exp (κ (log N) ^ (3 - 2 γ))`,
while the left side does not depend on `κ` at all. So any single configuration with a nonzero
block phase off the half integer strips refutes it.

The configuration: `γ = 5 / 4`, `δ = 1 / 100`, `N = 6`, `a = 1 / 2`, `b = 3 / 4`, and
`κ = 12 log 6 / (5 (log 6) ^ (1 / 2))`, which makes `E ^ (5 / 6) = 36`.

* The block `indices_low_j0 (5 / 4) 6` is the singleton `{4}`: the range is `3 < n ≤ 6`, the
  cut `n ≤ 18 / 4 = 4` leaves `n = 4`, and `ν_4 = ⌊exp ((log 4) ^ (5 / 4))⌋ = 4` is even since
  `log 4 ≤ (log 4) ^ (5 / 4) < log 5`. So the block phase has norm exactly one.
* With `X = exp ((log 6) ^ (5 / 4))` one has `X ^ (6 / 100) < 2`, so the only major arcs are
  those with `q = 1`, of radius `X ^ (6 / 100 - 1) < 1 / 4`; `1 / 2` and `3 / 4` avoid them
  and lie in `[-1, 1] ⊆ [-E ^ (2 / 3), E ^ (2 / 3)]`.
* `b - a = 1 / 4` is at distance at least `1 / 4` from every half integer, and the strip
  radius `X ^ (1 / 100 - 1)` is below `1 / 4`.
* The right side is `6 E ^ (-(5 / 6)) = 6 / 36 < 1`.

Consequence: `leaf_low_j0_large_phase_localizes_split` rests on a false leaf. The parent
`leaf_low_j0_large_phase_localizes`, which has a cap `κ₀` and a threshold `N₀`, is not shown
false by this file.

Results, all fully proved, nothing admitted:
* `indices_low_j0_five_fourths_six`, the block is `{4}`;
* `leaf_low_j0_off_lattice_block_small_false`, the negation of the leaf statement, verbatim
  in its binders.

The leaf statement itself is not changed and this file does not use it.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.Decomp553a

open Real Finset Set
open LeanLab.ExceptionalSet.U1539 (eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a

private theorem norm_eC_j0f (x : ℝ) : ‖eC x‖ = 1 := by
  unfold LeanLab.ExceptionalSet.U1539.eC
  have : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

private theorem log4_eq_j0f : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

private theorem log4_lt_j0f : Real.log 4 < 1.3863 := by
  have := Real.log_two_lt_d9
  rw [log4_eq_j0f]; linarith

private theorem log4_gt_j0f : 1.3862 < Real.log 4 := by
  have := Real.log_two_gt_d9
  rw [log4_eq_j0f]; linarith

private theorem log5_gt_j0f : 1.58 < Real.log 5 := by
  have h : Real.log 5 = Real.log 4 + Real.log (5 / 4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 : 1 - (5 / 4 : ℝ)⁻¹ ≤ Real.log (5 / 4) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have := log4_gt_j0f
  rw [h]; norm_num at h2; linarith

private theorem log6_bounds_j0f : 1.58 < Real.log 6 ∧ Real.log 6 < 1.9 := by
  have h5 := log5_gt_j0f
  have hlt : Real.log 5 < Real.log 6 := Real.log_lt_log (by norm_num) (by norm_num)
  have h : Real.log 6 = Real.log 4 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 : Real.log (3 / 2) ≤ 3 / 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have := log4_lt_j0f
  constructor
  · linarith
  · rw [h]; linarith

/-- The window facts at `δ = 1 / 100` for `X = exp s` with `1.58 ≤ s ≤ 4`. -/
private theorem window_j0f (s : ℝ) (hs1 : 1.58 ≤ s) (hs2 : s ≤ 4) :
    Real.exp s ^ (6 * (1 / 100 : ℝ)) < 2 ∧
    Real.exp s ^ (6 * (1 / 100 : ℝ)) / Real.exp s < 1 / 4 ∧
    Real.exp s ^ ((1 / 100 : ℝ) - 1) < 1 / 4 := by
  have hl2 := Real.log_two_gt_d9
  have h4 := log4_lt_j0f
  have hq : (1 / 4 : ℝ) = Real.exp (-Real.log 4) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [← Real.exp_mul]
    calc Real.exp (s * (6 * (1 / 100))) < Real.exp (Real.log 2) :=
          Real.exp_lt_exp.2 (by nlinarith)
      _ = 2 := Real.exp_log (by norm_num)
  · rw [← Real.exp_mul, ← Real.exp_sub, hq]
    exact Real.exp_lt_exp.2 (by nlinarith)
  · rw [← Real.exp_mul, hq]
    exact Real.exp_lt_exp.2 (by nlinarith)

/-- A real number at distance at least `1 / 4` from every integer is not on a major arc of
height below `2` and radius below `1 / 4`. -/
private theorem not_major_j0f (P X α : ℝ) (hP : P < 2) (hPX : P / X < 1 / 4)
    (hα : ∀ z : ℤ, 1 / 4 ≤ |α - z|) : α ∉ majorArcs P X := by
  rintro ⟨q, z, hq1, hqP, _, hclose⟩
  have hq2 : (q : ℝ) < 2 := lt_of_le_of_lt hqP hP
  have hq : q = 1 := by
    have : q < 2 := by exact_mod_cast hq2
    omega
  subst hq
  have := hα z
  simp only [Nat.cast_one, one_mul] at hclose
  linarith

private theorem dist_three_quarters_j0f (z : ℤ) : 1 / 4 ≤ |(3 / 4 : ℝ) - z| := by
  rcases le_or_gt z 0 with hz | hz
  · have : (z : ℝ) ≤ 0 := by exact_mod_cast hz
    rw [abs_of_pos (by linarith)]; linarith
  · have : (1 : ℝ) ≤ z := by exact_mod_cast hz
    rw [abs_of_neg (by linarith)]; linarith

private theorem dist_half_j0f (z : ℤ) : 1 / 4 ≤ |(1 / 2 : ℝ) - z| := by
  rcases le_or_gt z 0 with hz | hz
  · have : (z : ℝ) ≤ 0 := by exact_mod_cast hz
    rw [abs_of_pos (by linarith)]; linarith
  · have : (1 : ℝ) ≤ z := by exact_mod_cast hz
    rw [abs_of_neg (by linarith)]; linarith

private theorem dist_quarter_half_j0f (h : ℤ) : 1 / 4 ≤ |(1 / 4 : ℝ) - (h : ℝ) / 2| := by
  rcases le_or_gt h 0 with hz | hz
  · have : (h : ℝ) ≤ 0 := by exact_mod_cast hz
    rw [abs_of_pos (by linarith)]; linarith
  · have : (1 : ℝ) ≤ h := by exact_mod_cast hz
    rw [abs_of_neg (by linarith)]; linarith

/-- `ν_4 = 4` at `γ = 5 / 4`: `log 4 ≤ (log 4) ^ (5 / 4) < log 5`. -/
private theorem nu_four_j0f : nu (5 / 4) 4 = 4 := by
  have h41 : 1 ≤ Real.log 4 := by linarith [log4_gt_j0f]
  have hlo : Real.log 4 ≤ Real.log 4 ^ (5 / 4 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le h41 (show (1 : ℝ) ≤ 5 / 4 by norm_num)
    rwa [Real.rpow_one] at this
  have hy0 : 0 ≤ Real.log 4 ^ (5 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hy4 : (Real.log 4 ^ (5 / 4 : ℝ)) ^ (4 : ℕ) = Real.log 4 ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hhi : Real.log 4 ^ (5 / 4 : ℝ) < Real.log 5 := by
    have h5 := log5_gt_j0f
    have h4 := log4_lt_j0f
    have hpow : (Real.log 4 ^ (5 / 4 : ℝ)) ^ (4 : ℕ) < (1.58 : ℝ) ^ (4 : ℕ) := by
      rw [hy4]
      calc Real.log 4 ^ (5 : ℕ) < (1.3863 : ℝ) ^ (5 : ℕ) :=
            pow_lt_pow_left₀ h4 (by linarith) (by norm_num)
        _ < (1.58 : ℝ) ^ (4 : ℕ) := by norm_num
    have := lt_of_pow_lt_pow_left₀ 4 (by norm_num) hpow
    linarith
  unfold LeanLab.ExceptionalSet.U1539.nu
  rw [Int.floor_eq_iff]
  unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
  have e4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  rw [e4]
  constructor
  · have : Real.exp (Real.log 4) ≤ Real.exp (Real.log 4 ^ (5 / 4 : ℝ)) := Real.exp_le_exp.2 hlo
    rw [Real.exp_log (by norm_num)] at this
    push_cast; linarith
  · have : Real.exp (Real.log 4 ^ (5 / 4 : ℝ)) < Real.exp (Real.log 5) := Real.exp_lt_exp.2 hhi
    rw [Real.exp_log (by norm_num)] at this
    push_cast; linarith

/-- The block `indices_low_j0 (5 / 4) 6` is `{4}`. -/
theorem indices_low_j0_five_fourths_six : indices_low_j0 (5 / 4) 6 = {4} := by
  ext n
  simp only [indices_low_j0, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, _⟩, h3⟩
    omega
  · rintro rfl
    refine ⟨⟨⟨by norm_num, by norm_num⟩, ?_⟩, by norm_num⟩
    rw [nu_four_j0f]
    exact ⟨2, by norm_num⟩

/-- The negation of `leaf_low_j0_off_lattice_block_small`, with its binders verbatim. The
witness is `γ = 5 / 4`, `δ = 1 / 100`, `N = 6`, `a = 1 / 2`, `b = 3 / 4` and
`κ = 12 log 6 / (5 (log 6) ^ (1 / 2))`. -/
theorem leaf_low_j0_off_lattice_block_small_false :
    ¬ ∀ (γ δ κ : ℝ) (N : ℕ) (a b : ℝ), 1 < γ → γ < 3 / 2 → 0 < δ → 0 < κ →
      a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) →
      b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) →
      (∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
        F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) →
      ‖blockPhase (indices_low_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖ ≤
        (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  intro hall
  obtain ⟨h6lo, h6hi⟩ := log6_bounds_j0f
  have hl0 : 0 < Real.log 6 := by linarith
  set L : ℝ := Real.log 6 ^ (3 - 2 * (5 / 4 : ℝ)) with hL
  have hLpos : 0 < L := Real.rpow_pos_of_pos hl0 _
  set κ : ℝ := 12 * Real.log 6 / (5 * L) with hκ
  have hκpos : 0 < κ := by positivity
  have hκL : κ * L = 12 / 5 * Real.log 6 := by
    rw [hκ]; field_simp
  set s : ℝ := Real.log 6 ^ (5 / 4 : ℝ) with hs
  have hs1 : 1.58 ≤ s := by
    have := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ Real.log 6 by linarith)
      (show (1 : ℝ) ≤ 5 / 4 by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hs2 : s ≤ 4 := by
    have := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ Real.log 6 by linarith)
      (show (5 / 4 : ℝ) ≤ 2 by norm_num)
    rw [Real.rpow_two] at this
    nlinarith
  have hX : F (5 / 4) ((6 : ℕ) : ℝ) = Real.exp s := by
    unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
    norm_num [hs]
  have hE : calE (5 / 4) κ 6 = Real.exp (κ * L) := by
    unfold LeanLab.ExceptionalSet.U1539.calE
    norm_num [hL]
  obtain ⟨hP2, hPX, hrad⟩ := window_j0f s hs1 hs2
  have hE1 : 1 ≤ calE (5 / 4) κ 6 := by
    rw [hE]; exact Real.one_le_exp (by positivity)
  have hE23 : 1 ≤ calE (5 / 4) κ 6 ^ (2 / 3 : ℝ) := Real.one_le_rpow hE1 (by norm_num)
  have hdom : ∀ α : ℝ, (∀ z : ℤ, 1 / 4 ≤ |α - z|) → -1 ≤ α → α ≤ 1 →
      α ∈ oddDomain (F (5 / 4) ((6 : ℕ) : ℝ) ^ (6 * (1 / 100 : ℝ))) (F (5 / 4) ((6 : ℕ) : ℝ))
        (calE (5 / 4) κ 6) := by
    intro α hα h1 h2
    refine ⟨?_, ?_, ?_⟩
    · rw [hX]
      exact not_major_j0f _ _ α hP2 hPX hα
    · linarith
    · linarith
  have ha := hdom (1 / 2) dist_half_j0f (by norm_num) (by norm_num)
  have hb := hdom (3 / 4) dist_three_quarters_j0f (by norm_num) (by norm_num)
  have hoff : ∀ h : ℤ, (|h| : ℝ) ≤ calE (5 / 4) κ 6 ^ (3 / 4 : ℝ) →
      F (5 / 4) ((6 : ℕ) : ℝ) ^ ((1 / 100 : ℝ) - 1) < |((3 / 4 : ℝ) - 1 / 2) - (h : ℝ) / 2| := by
    intro h _
    rw [hX, show (3 / 4 : ℝ) - 1 / 2 = 1 / 4 by norm_num]
    exact lt_of_lt_of_le hrad (dist_quarter_half_j0f h)
  have key := hall (5 / 4) (1 / 100) κ 6 (1 / 2) (3 / 4) (by norm_num) (by norm_num)
    (by norm_num) hκpos ha hb hoff
  rw [indices_low_j0_five_fourths_six] at key
  simp only [blockPhase, Finset.sum_singleton, norm_eC_j0f] at key
  have hrhs : (((6 : ℕ) : ℝ)) * calE (5 / 4) κ 6 ^ (-(5 / 6 : ℝ)) < 1 := by
    rw [hE, ← Real.exp_mul, hκL]
    have hlt : Real.exp (12 / 5 * Real.log 6 * (-(5 / 6))) < Real.exp (-Real.log 6) :=
      Real.exp_lt_exp.2 (by nlinarith)
    rw [Real.exp_neg, Real.exp_log (by norm_num)] at hlt
    have : ((6 : ℕ) : ℝ) * (6 : ℝ)⁻¹ = 1 := by norm_num
    nlinarith
  linarith

end LeanLab.ExceptionalSet.Decomp553a
