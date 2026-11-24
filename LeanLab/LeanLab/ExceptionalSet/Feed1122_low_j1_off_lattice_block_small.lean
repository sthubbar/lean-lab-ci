import LeanLab.ExceptionalSet.SPLIT_leaf_low_j1_large_phase_localizes

/-!
FALSE finding for `Decomp553c.leaf_low_j1_off_lattice_block_small` of
`LeanLab.ExceptionalSet.SPLIT_leaf_low_j1_large_phase_localizes`.

Source of the step: J. Brudern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998), paper P0082, page 369 display (39) and the proof of Lemma 9 on
page 370. In the paper the smallness of the block phase off the half integer strips holds
only for `N` large, after a choice of `δ` and of `κ` small, through Theorem 2 on page 354.
The leaf states it pointwise for every `γ, δ, κ, N` with no threshold, and that is false.

Counterexample, kernel checked below: `γ = 5 / 4`, `N = 4`, `κ = 6`, `a = 3 / 8`,
`b = 5 / 8`, and `δ = log c / log X` with `X = F γ 4` and
`c = (1 + min (X / 4) (21 / 20)) / 2`, so that `X ^ δ = c`. Then the block
`indices_low_j1 γ 4` is `{3}`, because `⌊F γ 3⌋ = 3`, so the block phase has norm one,
while `N E ^ (-(5 / 6)) ≤ 4 exp (-5) < 1`. The points `3 / 8`, `5 / 8` lie in the window,
off the major arcs since `P = c ^ 6 < 3 / 2` forces `q = 1` and `P / X < 3 / 8`, and
`b - a = 1 / 4` is at distance at least `1 / 4 > c / X = X ^ (δ - 1)` from every half integer.

The sibling `Decomp553d.leaf_high_j1_off_lattice_block_small` carries the thresholds
`δ₀, κ₀, N₀` and is the faithful form; the assembly in the parent file uses the false
pointwise form, so the parent assembly should be rewired to a thresholded leaf.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp553c

open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (nu calE majorArcs eC)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a
open LeanLab.ExceptionalSet.Decomp553a

private theorem feed1122_norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem feed1122_one_lt_log3 : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

private theorem feed1122_log3_lt : Real.log 3 < 1.1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.quadratic_le_exp_of_nonneg (x := (0.1 : ℝ)) (by norm_num)
  have he : Real.exp 1.1 = Real.exp 1 * Real.exp 0.1 := by
    rw [← Real.exp_add]; norm_num
  rw [he]
  nlinarith

private theorem feed1122_log4_gt : 1.386 < Real.log 4 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  rw [h]; linarith

private theorem feed1122_nu3 : nu (5 / 4) 3 = 3 := by
  unfold nu
  rw [Int.floor_eq_iff]
  have hl := feed1122_one_lt_log3
  have hu := feed1122_log3_lt
  have h4 := feed1122_log4_gt
  have hF : F (5 / 4) ((3 : ℕ) : ℝ) = Real.exp (Real.log 3 ^ (5 / 4 : ℝ)) := by
    simp [F]
  constructor
  · rw [hF]
    push_cast
    have : Real.log 3 ≤ Real.log 3 ^ (5 / 4 : ℝ) := by
      calc Real.log 3 = Real.log 3 ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hl.le (by norm_num)
    calc (3 : ℝ) = Real.exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr this
  · rw [hF]
    push_cast
    have h2 : Real.log 3 ^ (5 / 4 : ℝ) ≤ Real.log 3 ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hl.le (by norm_num)
    rw [show Real.log 3 ^ (2 : ℝ) = Real.log 3 ^ (2 : ℕ) by norm_cast] at h2
    have h3 : Real.log 3 ^ (5 / 4 : ℝ) < Real.log 4 := by nlinarith
    have h5 : Real.exp (Real.log 3 ^ (5 / 4 : ℝ)) < 4 :=
      calc Real.exp (Real.log 3 ^ (5 / 4 : ℝ)) < Real.exp (Real.log 4) := Real.exp_lt_exp.mpr h3
        _ = 4 := Real.exp_log (by norm_num)
    norm_num
    linarith

private theorem feed1122_indices : indices_low_j1 (5 / 4) 4 = {3} := by
  ext n
  simp only [indices_low_j1, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, _⟩, h3⟩
    omega
  · rintro rfl
    refine ⟨⟨⟨by norm_num, by norm_num⟩, ?_⟩, by norm_num⟩
    rw [feed1122_nu3]
    decide

/-- FALSE. The pointwise statement of `leaf_low_j1_off_lattice_block_small` fails at
`γ = 5 / 4`, `N = 4`, `κ = 6`, `a = 3 / 8`, `b = 5 / 8` and a small `δ`. -/
theorem feed1122_low_j1_off_lattice_block_small_false :
    ¬ (∀ (γ δ κ : ℝ) (N : ℕ) (a b : ℝ),
      1 < γ → γ < 3 / 2 → 0 < δ → δ ≤ 1 → 0 < κ →
      a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) →
      b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) →
      (∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
        F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) →
      ‖blockPhase (indices_low_j1 γ N) (fun n => F γ n - (1 : ℤ)) (b - a)‖ ≤
        (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ))) := by
  intro H
  set X : ℝ := F (5 / 4) ((4 : ℕ) : ℝ) with hXdef
  have h4 := feed1122_log4_gt
  have hX4 : 4 < X := by
    have hL : Real.log 4 < Real.log 4 ^ (5 / 4 : ℝ) := by
      calc Real.log 4 = Real.log 4 ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ < _ := Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
    have : X = Real.exp (Real.log 4 ^ (5 / 4 : ℝ)) := by simp [hXdef, F]
    rw [this]
    calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ < _ := Real.exp_lt_exp.mpr hL
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  set m : ℝ := min (X / 4) (21 / 20) with hm
  have hm1 : 1 < m := lt_min (by linarith) (by norm_num)
  have hmX : m ≤ X / 4 := min_le_left _ _
  have hm2 : m ≤ 21 / 20 := min_le_right _ _
  set c : ℝ := (1 + m) / 2 with hc
  have hc1 : 1 < c := by rw [hc]; linarith
  have hcX : c < X / 4 := by rw [hc]; linarith
  have hc2 : c ≤ 21 / 20 := by rw [hc]; linarith
  have hc0 : 0 < c := by linarith
  have hc6 : c ^ 6 < 3 / 2 := by
    have : c ^ 6 ≤ (21 / 20 : ℝ) ^ 6 := pow_le_pow_left₀ hc0.le hc2 6
    have h' : (21 / 20 : ℝ) ^ 6 < 3 / 2 := by norm_num
    linarith
  set δ : ℝ := Real.log c / Real.log X with hδ
  have hXδ : X ^ δ = c := by
    rw [Real.rpow_def_of_pos hX0, hδ, mul_div_cancel₀ _ hlogX.ne', Real.exp_log hc0]
  have hXP : X ^ (6 * δ) = c ^ 6 := by
    rw [mul_comm, Real.rpow_mul hX0.le, hXδ]; norm_cast
  have hXs : X ^ (δ - 1) = c / X := by rw [Real.rpow_sub_one hX0.ne', hXδ]
  have hδpos : 0 < δ := div_pos (Real.log_pos hc1) hlogX
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one hlogX]
    exact Real.log_le_log hc0 (by linarith)
  -- the cost parameter
  set E : ℝ := calE (5 / 4) 6 4 with hE
  have hL1 : 1 ≤ Real.log ((4 : ℕ) : ℝ) ^ (3 - 2 * (5 / 4 : ℝ)) := by
    apply Real.one_le_rpow
    · push_cast; linarith
    · norm_num
  have hE1 : 1 ≤ E := by
    rw [hE, calE]
    exact Real.one_le_exp (by positivity)
  have hE56 : E ^ (-(5 / 6 : ℝ)) < 1 / 4 := by
    rw [hE, calE, ← Real.exp_mul]
    have h5 : Real.exp (6 * Real.log ((4 : ℕ) : ℝ) ^ (3 - 2 * (5 / 4 : ℝ)) * -(5 / 6))
        ≤ Real.exp (-5) := Real.exp_le_exp.mpr (by nlinarith)
    have h6 : Real.exp (-5) < 1 / 4 := by
      rw [Real.exp_neg]
      have := Real.add_one_le_exp (5 : ℝ)
      rw [inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith
    linarith
  have hE23 : 1 ≤ E ^ (2 / 3 : ℝ) := Real.one_le_rpow hE1 (by norm_num)
  -- membership in the window
  have hmem : ∀ y : ℝ, (∀ k : ℤ, 3 / 8 ≤ |y - k|) → 0 ≤ y → y ≤ 1 →
      y ∈ oddDomain (X ^ (6 * δ)) X E := by
    intro y hy hy0 hy1
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨q, a', hq1, hqP, _, habs⟩
      rw [hXP] at hqP habs
      have hq : q = 1 := by
        have : (q : ℝ) < 2 := by linarith
        have : q < 2 := by exact_mod_cast this
        omega
      subst hq
      have hPX : c ^ 6 / X < 3 / 8 := by
        rw [div_lt_iff₀ hX0]; nlinarith
      have := hy a'
      simp only [Nat.cast_one, one_mul] at habs
      linarith
    · linarith
    · linarith
  have ha : (3 / 8 : ℝ) ∈ oddDomain (X ^ (6 * δ)) X E := by
    refine hmem _ (fun k => ?_) (by norm_num) (by norm_num)
    rcases le_or_gt k 0 with hk | hk
    · have : (k : ℝ) ≤ 0 := by exact_mod_cast hk
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      rw [abs_of_nonpos (by linarith)]; linarith
  have hb : (5 / 8 : ℝ) ∈ oddDomain (X ^ (6 * δ)) X E := by
    refine hmem _ (fun k => ?_) (by norm_num) (by norm_num)
    rcases le_or_gt k 0 with hk | hk
    · have : (k : ℝ) ≤ 0 := by exact_mod_cast hk
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      rw [abs_of_nonpos (by linarith)]; linarith
  have hoff : ∀ h : ℤ, (|h| : ℝ) ≤ E ^ (3 / 4 : ℝ) →
      X ^ (δ - 1) < |((5 / 8 : ℝ) - 3 / 8) - (h : ℝ) / 2| := by
    intro h _
    rw [hXs]
    have hcs : c / X < 1 / 4 := by rw [div_lt_iff₀ hX0]; linarith
    rcases le_or_gt h 0 with hk | hk
    · have : (h : ℝ) ≤ 0 := by exact_mod_cast hk
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : (1 : ℝ) ≤ h := by exact_mod_cast hk
      rw [abs_of_nonpos (by linarith)]; linarith
  have key := H (5 / 4) δ 6 4 (3 / 8) (5 / 8) (by norm_num) (by norm_num) hδpos hδ1
    (by norm_num) ha hb hoff
  rw [feed1122_indices] at key
  simp only [blockPhase, Finset.sum_singleton, feed1122_norm_eC] at key
  have : ((4 : ℕ) : ℝ) * E ^ (-(5 / 6 : ℝ)) < 1 := by push_cast; linarith
  linarith

end LeanLab.ExceptionalSet.Decomp553c
