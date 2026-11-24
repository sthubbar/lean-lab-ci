import LeanLab.ExceptionalSet.SPLIT_leaf_low_j0_large_phase_localizes

/-!
Counterexample to `Decomp553a.leaf_low_j0_off_lattice_block_small` as written.

The leaf in `SPLIT_leaf_low_j0_large_phase_localizes` states a pointwise bound for every
`γ δ κ N a b` with no threshold in `κ`, `δ` or `N`. Its source is P0082,
J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences, Ann. Inst. Fourier 48
(1998), Lemma 9 page 368 with its proof on page 370, which is an estimate valid only
for `N` large and `κ` small.

At `γ = 5/4`, `N = 6`, `κ = 12`, `δ = 1/600`, `a = 2/5`, `b = 3/5` all hypotheses hold,
the block `indices_low_j0 (5/4) 6` is `{4}` since `⌊F(4)⌋ = 4`, so the block phase has
norm one, while `N ℰ^{-5/6} = 6 exp(-10 √(log 6)) < 1`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp553a

open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (Sp eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a

theorem feed1122_eC_norm (x : ℝ) : ‖eC x‖ = 1 := by
  unfold U1539.eC
  rw [Complex.norm_exp]
  simp

theorem feed1122_log6_bounds : 1 ≤ Real.log 6 ∧ Real.log 6 ≤ 5 := by
  constructor
  · rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  · have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 6 by norm_num)
    linarith

theorem feed1122_log5_le : Real.log 5 + 1 / 6 ≤ Real.log 6 := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 6 / 5 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num)] at h
  norm_num at h
  linarith

theorem feed1122_floor_F4 : ⌊F (5 / 4) ((4 : ℕ) : ℝ)⌋ = 4 := by
  unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
  set u := Real.log ((4 : ℕ) : ℝ) with hu
  have hu4 : u = 2 * Real.log 2 := by
    rw [hu]; push_cast
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  have hu1 : 1 ≤ u := by rw [hu4]; linarith
  have hu0 : 0 < u := by linarith
  have h5 : u + 1 / 5 ≤ Real.log 5 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 5 / 4 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num)] at h
    have : Real.log 4 = u := by rw [hu]; push_cast; rfl
    norm_num at h
    linarith
  have hq : u ^ (1 / 4 : ℝ) ≤ 1.1 := by
    have hu' : u ≤ (1.1 : ℝ) ^ (4 : ℕ) := by rw [hu4]; norm_num; linarith
    calc u ^ (1 / 4 : ℝ) ≤ ((1.1 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hu0.le hu' (by norm_num)
      _ = 1.1 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hsplit : u ^ (5 / 4 : ℝ) = u * u ^ (1 / 4 : ℝ) := by
    rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add hu0, Real.rpow_one]
  have hup : u ^ (5 / 4 : ℝ) < Real.log 5 := by
    rw [hsplit]
    have : u * u ^ (1 / 4 : ℝ) ≤ u * 1.1 := mul_le_mul_of_nonneg_left hq hu0.le
    rw [hu4] at this ⊢
    linarith
  have hge : u ≤ u ^ (5 / 4 : ℝ) := Real.self_le_rpow_of_one_le hu1 (by norm_num)
  rw [Int.floor_eq_iff]
  constructor
  · have : Real.exp u ≤ Real.exp (u ^ (5 / 4 : ℝ)) := Real.exp_le_exp.mpr hge
    have h4 : Real.exp u = 4 := by rw [hu]; push_cast; exact Real.exp_log (by norm_num)
    push_cast; linarith
  · have : Real.exp (u ^ (5 / 4 : ℝ)) < Real.exp (Real.log 5) := Real.exp_lt_exp.mpr hup
    rw [Real.exp_log (by norm_num)] at this
    push_cast; linarith

theorem feed1122_indices_low_j0_6 : indices_low_j0 (5 / 4) 6 = {4} := by
  ext n
  simp only [indices_low_j0, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, -⟩, h3⟩
    omega
  · rintro rfl
    refine ⟨⟨⟨by norm_num, by norm_num⟩, ?_⟩, by norm_num⟩
    unfold U1539.nu
    rw [feed1122_floor_F4]
    decide

/-- The specific counterexample, kernel checked. -/
theorem feed1122_low_j0_off_lattice_counterexample :
    (1 : ℝ) < 5 / 4 ∧ (5 / 4 : ℝ) < 3 / 2 ∧ (0 : ℝ) < 1 / 600 ∧ (0 : ℝ) < 12 ∧
    (2 / 5 : ℝ) ∈ oddDomain (F (5 / 4) (6 : ℕ) ^ (6 * (1 / 600 : ℝ))) (F (5 / 4) (6 : ℕ))
      (calE (5 / 4) 12 6) ∧
    (3 / 5 : ℝ) ∈ oddDomain (F (5 / 4) (6 : ℕ) ^ (6 * (1 / 600 : ℝ))) (F (5 / 4) (6 : ℕ))
      (calE (5 / 4) 12 6) ∧
    (∀ h : ℤ, (|h| : ℝ) ≤ calE (5 / 4) 12 6 ^ (3 / 4 : ℝ) →
      F (5 / 4) (6 : ℕ) ^ ((1 / 600 : ℝ) - 1) < |((3 / 5 : ℝ) - 2 / 5) - (h : ℝ) / 2|) ∧
    ((6 : ℕ) : ℝ) * calE (5 / 4) 12 6 ^ (-(5 / 6 : ℝ)) <
      ‖blockPhase (indices_low_j0 (5 / 4) 6) (fun n => F (5 / 4) n - (0 : ℤ))
        ((3 / 5 : ℝ) - 2 / 5)‖ := by
  obtain ⟨hl1, hl5⟩ := feed1122_log6_bounds
  have hl56 := feed1122_log5_le
  set L := Real.log ((6 : ℕ) : ℝ) ^ (5 / 4 : ℝ) with hL
  have hlog6 : Real.log ((6 : ℕ) : ℝ) = Real.log 6 := by push_cast; rfl
  have hLlo : Real.log 6 ≤ L := by
    rw [hL, hlog6]; exact Real.self_le_rpow_of_one_le hl1 (by norm_num)
  have hLhi : L ≤ 25 := by
    rw [hL, hlog6]
    calc Real.log 6 ^ (5 / 4 : ℝ) ≤ Real.log 6 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hl1 (by norm_num)
      _ = Real.log 6 ^ (2 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
      _ ≤ 25 := by nlinarith
  have hX : ∀ y : ℝ, F (5 / 4) ((6 : ℕ) : ℝ) ^ y = Real.exp (L * y) := by
    intro y
    unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
    rw [Real.exp_mul]
  have hE : 1 ≤ calE (5 / 4) 12 6 := by
    unfold U1539.calE
    exact Real.one_le_exp (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (Real.log_natCast_nonneg 6) _))
  have hE23 : 1 ≤ calE (5 / 4) 12 6 ^ (2 / 3 : ℝ) := Real.one_le_rpow hE (by norm_num)
  have hlog2 := Real.log_two_gt_d9
  -- the minor arc condition
  have hminor : ∀ α : ℝ, (∀ z : ℤ, 2 / 5 ≤ |α - z|) →
      α ∉ majorArcs (F (5 / 4) ((6 : ℕ) : ℝ) ^ (6 * (1 / 600 : ℝ))) (F (5 / 4) ((6 : ℕ) : ℝ)) := by
    rintro α hα ⟨q, z, hq1, hqP, -, hz⟩
    rw [hX] at hqP
    have hP2 : Real.exp (L * (6 * (1 / 600 : ℝ))) < 2 := by
      have : L * (6 * (1 / 600 : ℝ)) < Real.log 2 := by nlinarith
      calc Real.exp (L * (6 * (1 / 600 : ℝ))) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr this
        _ = 2 := Real.exp_log (by norm_num)
    have hq : q = 1 := by
      have : (q : ℝ) < 2 := lt_of_le_of_lt hqP hP2
      have : q < 2 := by exact_mod_cast this
      omega
    subst hq
    have hX1 : F (5 / 4) ((6 : ℕ) : ℝ) = Real.exp L := rfl
    rw [hX, hX1, ← Real.exp_sub] at hz
    have hsm : Real.exp (L * (6 * (1 / 600 : ℝ)) - L) < 2 / 5 := by
      have : L * (6 * (1 / 600 : ℝ)) - L < -Real.log 5 := by nlinarith
      calc Real.exp (L * (6 * (1 / 600 : ℝ)) - L) < Real.exp (-Real.log 5) :=
            Real.exp_lt_exp.mpr this
        _ = 1 / 5 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
        _ < 2 / 5 := by norm_num
    have := hα z
    push_cast at hz
    rw [one_mul] at hz
    linarith
  have hfar25 : ∀ z : ℤ, 2 / 5 ≤ |(2 / 5 : ℝ) - z| := by
    intro z
    rcases le_or_gt z 0 with hz | hz
    · have : (z : ℝ) ≤ 0 := by exact_mod_cast hz
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : (1 : ℝ) ≤ z := by exact_mod_cast hz
      rw [abs_of_nonpos (by linarith)]; linarith
  have hfar35 : ∀ z : ℤ, 2 / 5 ≤ |(3 / 5 : ℝ) - z| := by
    intro z
    rcases le_or_gt z 0 with hz | hz
    · have : (z : ℝ) ≤ 0 := by exact_mod_cast hz
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : (1 : ℝ) ≤ z := by exact_mod_cast hz
      rw [abs_of_nonpos (by linarith)]; linarith
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · refine ⟨hminor _ hfar25, ?_, ?_⟩ <;> linarith
  · refine ⟨hminor _ hfar35, ?_, ?_⟩ <;> linarith
  · intro h _
    rw [hX]
    have hrad : Real.exp (L * ((1 / 600 : ℝ) - 1)) < 1 / 5 := by
      have : L * ((1 / 600 : ℝ) - 1) < -Real.log 5 := by nlinarith
      calc Real.exp (L * ((1 / 600 : ℝ) - 1)) < Real.exp (-Real.log 5) :=
            Real.exp_lt_exp.mpr this
        _ = 1 / 5 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    have : 1 / 5 ≤ |((3 / 5 : ℝ) - 2 / 5) - (h : ℝ) / 2| := by
      rcases le_or_gt h 0 with hz | hz
      · have : (h : ℝ) ≤ 0 := by exact_mod_cast hz
        rw [abs_of_nonneg (by linarith)]; linarith
      · have : (1 : ℝ) ≤ h := by exact_mod_cast hz
        rw [abs_of_nonpos (by linarith)]; linarith
    linarith
  · rw [feed1122_indices_low_j0_6]
    simp only [blockPhase, Finset.sum_singleton]
    rw [feed1122_eC_norm]
    have hs : 1 ≤ Real.log ((6 : ℕ) : ℝ) ^ (3 - 2 * (5 / 4 : ℝ)) := by
      rw [hlog6]; exact Real.one_le_rpow hl1 (by norm_num)
    have hEpow : calE (5 / 4) 12 6 ^ (-(5 / 6 : ℝ)) =
        Real.exp (12 * Real.log ((6 : ℕ) : ℝ) ^ (3 - 2 * (5 / 4 : ℝ)) * (-(5 / 6 : ℝ))) := by
      unfold U1539.calE
      rw [← Real.exp_mul]
    rw [hEpow]
    have hlt : Real.exp (12 * Real.log ((6 : ℕ) : ℝ) ^ (3 - 2 * (5 / 4 : ℝ)) * (-(5 / 6 : ℝ)))
        ≤ Real.exp (-10) := Real.exp_le_exp.mpr (by nlinarith)
    have h10 : (11 : ℝ) ≤ Real.exp 10 := by
      have := Real.add_one_le_exp (10 : ℝ); linarith
    have hneg : Real.exp (-10) * Real.exp 10 = 1 := by
      rw [← Real.exp_add]; norm_num
    have : Real.exp (-10) < 1 / 6 := by
      have h0 : 0 < Real.exp (-10) := Real.exp_pos _
      nlinarith
    push_cast
    linarith

/-- The leaf `leaf_low_j0_off_lattice_block_small` is false as written. -/
theorem leaf_low_j0_off_lattice_block_small_false :
    ¬ (∀ (γ δ κ : ℝ) (N : ℕ) (a b : ℝ),
      1 < γ → γ < 3 / 2 → 0 < δ → 0 < κ →
      a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) →
      b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) →
      (∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
        F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) →
      ‖blockPhase (indices_low_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖ ≤
        (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ))) := by
  intro H
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := feed1122_low_j0_off_lattice_counterexample
  exact absurd (H _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7) (not_le.mpr h8)

end LeanLab.ExceptionalSet.Decomp553a
