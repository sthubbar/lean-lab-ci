/-
Refutation of a threshold-free lab auxiliary associated with P0082 page 369.
The paper uses eventual estimates with small parameters.
The sealed lab leaf fails at N four and kappa ten. Its statement stays unchanged.
The refutation concerns the lab auxiliary. The paper uses eventual estimates with small parameters.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_low_j1_large_phase_localizes
import LeanLab.ExceptionalSet.DQLemma9Decisions

namespace LeanLab.ExceptionalSet.Task672

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE majorArcs)
open LeanLab.ExceptionalSet.Decomp553a (blockPhase)
open LeanLab.ExceptionalSet.Decomp553c (indices_low_j1)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a (oddDomain)

/-- The low odd-shift block at N four has exactly the index three. -/
theorem low_j1_index672 : indices_low_j1 (5 / 4) 4 = {3} := by
  have hL3 : (1 : ℝ) < log 3 := by linarith [log_three_gt_d9]
  have hL3u : log 3 < (9 / 8 : ℝ) := by linarith [log_three_lt_d9]
  have hL4 : (4 / 3 : ℝ) < log 4 := by
    have he : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow]
      norm_num
    rw [he]
    linarith [log_two_gt_d9]
  have hlo : log 3 ≤ log 3 ^ (5 / 4 : ℝ) := by
    simpa using rpow_le_rpow_of_exponent_le hL3.le (by norm_num : (1 : ℝ) ≤ 5 / 4)
  have hhi : log 3 ^ (5 / 4 : ℝ) ≤ log 3 ^ (2 : ℕ) := by
    simpa using rpow_le_rpow_of_exponent_le hL3.le (by norm_num : (5 / 4 : ℝ) ≤ 2)
  have hsq : log 3 ^ (2 : ℕ) < (9 / 8 : ℝ) ^ (2 : ℕ) := by gcongr
  have hF3lo : (3 : ℝ) ≤ F (5 / 4) 3 := by
    calc (3 : ℝ) = exp (log 3) := (exp_log (by norm_num)).symm
      _ ≤ exp (log 3 ^ (5 / 4 : ℝ)) := exp_le_exp.mpr hlo
      _ = F (5 / 4) 3 := rfl
  have hF3hi : F (5 / 4) 3 < (4 : ℝ) := by
    calc F (5 / 4) 3 = exp (log 3 ^ (5 / 4 : ℝ)) := rfl
      _ < exp (log 4) := by apply exp_lt_exp.mpr; nlinarith
      _ = 4 := exp_log (by norm_num)
  have hnu : nu (5 / 4) 3 = 3 := by
    unfold nu
    apply Int.floor_eq_iff.mpr
    norm_num only [Int.cast_ofNat]
    exact ⟨hF3lo, hF3hi⟩
  change (((Ioc 2 4).filter (fun n => Even (nu (5 / 4) n + (1 : ℤ)))).filter
    (fun n => n ≤ 3)) = {3}
  ext n
  simp only [mem_filter, mem_Ioc, mem_singleton]
  constructor
  · intro hn
    omega
  · rintro rfl
    norm_num [hnu]

/-- Numerical scale inequalities for the concrete lab-leaf audit. -/
theorem low_j1_scale672 :
    F (5 / 4) 4 ^ (6 * (1 / 100 : ℝ)) < 2 ∧
    F (5 / 4) 4 ^ (6 * (1 / 100 : ℝ)) / F (5 / 4) 4 < 3 / 8 ∧
    F (5 / 4) 4 ^ ((1 / 100 : ℝ) - 1) < 1 / 4 ∧
    1 ≤ calE (5 / 4) 10 4 ^ (2 / 3 : ℝ) ∧
    4 * calE (5 / 4) 10 4 ^ (-(5 / 6 : ℝ)) < 1 := by
  let L : ℝ := log 4
  let R : ℝ := L ^ (1 / 4 : ℝ)
  let A : ℝ := L ^ (5 / 4 : ℝ)
  have hL : (4 / 3 : ℝ) < L ∧ L < 7 / 5 := by
    have he : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow]
      norm_num
    dsimp [L]
    rw [he]
    constructor <;> linarith [log_two_gt_d9, log_two_lt_d9]
  have hL0 : 0 < L := by linarith [hL.1]
  have hL1 : 1 ≤ L := by linarith [hL.1]
  have hR0 : 0 ≤ R := rpow_nonneg hL0.le _
  have hR4 : R ^ 4 = L := by
    dsimp [R]
    rw [← rpow_natCast, ← rpow_mul hL0.le]
    norm_num
  have hR : (21 / 20 : ℝ) < R := by
    by_contra h
    have hle : R ≤ 21 / 20 := le_of_not_gt h
    have hpow : R ^ 4 ≤ (21 / 20 : ℝ) ^ 4 := by gcongr
    nlinarith [hL.1]
  have hAeq : A = L * R := by
    dsimp [A, R]
    rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, rpow_add hL0, rpow_one]
  have hAR : (21 / 20 : ℝ) * L < A := by
    rw [hAeq]
    simpa [mul_comm] using mul_lt_mul_of_pos_left hR hL0
  have hAlo : (7 / 5 : ℝ) < A := by nlinarith [hL.1]
  have hA2 : A ≤ L ^ (2 : ℕ) := by
    dsimp [A]
    simpa using rpow_le_rpow_of_exponent_le hL1 (by norm_num : (5 / 4 : ℝ) ≤ 2)
  have hLsq : L ^ (2 : ℕ) < (7 / 5 : ℝ) ^ (2 : ℕ) := by
    gcongr
    exact hL.2
  have hAhi : A < 2 := by nlinarith
  have hF : F (5 / 4) 4 = exp A := rfl
  have hcal (t : ℝ) : calE (5 / 4) 10 4 ^ t = exp (10 * L ^ (1 / 2 : ℝ) * t) := by
    have h := DQLemma9.calE_rpow_l9 (5 / 4) 10 4 t
    norm_num [L] at h ⊢
    exact h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hF, ← exp_mul]
    calc exp (A * (6 * (1 / 100 : ℝ))) < exp (log 2) := by
          apply exp_lt_exp.mpr
          nlinarith [log_two_gt_d9]
      _ = 2 := exp_log (by norm_num)
  · rw [hF, ← exp_mul, ← exp_sub]
    calc exp (A * (6 * (1 / 100 : ℝ)) - A) < exp (-log 3) := by
          apply exp_lt_exp.mpr
          nlinarith [log_three_lt_d9]
      _ = 1 / 3 := by rw [exp_neg, exp_log (by norm_num)]; norm_num
      _ < 3 / 8 := by norm_num
  · rw [hF, ← exp_mul]
    calc exp (A * ((1 / 100 : ℝ) - 1)) < exp (-L) := by
          apply exp_lt_exp.mpr
          nlinarith
      _ = 1 / 4 := by rw [exp_neg]; dsimp [L]; rw [exp_log (by norm_num)]; norm_num
  · rw [hcal]
    exact one_le_exp (by positivity)
  · rw [hcal]
    have h4 : (4 : ℝ) = exp L := (exp_log (by norm_num)).symm
    rw [h4, ← exp_add]
    apply exp_lt_one_iff.mpr
    have hhalf : 1 ≤ L ^ (1 / 2 : ℝ) := one_le_rpow hL1 (by norm_num)
    nlinarith [hL.2]

/-- The hypotheses of the sealed low_j1 leaf hold at this tuple, but its conclusion fails. -/
theorem low_j1_counterexample672 :
    (3 / 8 : ℝ) ∈ oddDomain (F (5 / 4) 4 ^ (6 * (1 / 100 : ℝ)))
      (F (5 / 4) 4) (calE (5 / 4) 10 4) ∧
    (5 / 8 : ℝ) ∈ oddDomain (F (5 / 4) 4 ^ (6 * (1 / 100 : ℝ)))
      (F (5 / 4) 4) (calE (5 / 4) 10 4) ∧
    (∀ h : ℤ, (|h| : ℝ) ≤ calE (5 / 4) 10 4 ^ (3 / 4 : ℝ) →
      F (5 / 4) 4 ^ ((1 / 100 : ℝ) - 1) < |((5 / 8 : ℝ) - 3 / 8) - (h : ℝ) / 2|) ∧
    ¬ (‖blockPhase (indices_low_j1 (5 / 4) 4) (fun n => F (5 / 4) n - (1 : ℤ))
      ((5 / 8 : ℝ) - 3 / 8)‖ ≤ (4 : ℝ) * calE (5 / 4) 10 4 ^ (-(5 / 6 : ℝ))) := by
  rcases low_j1_scale672 with ⟨hP, hwidth, hrad, hE, hsmall⟩
  have hminor (x : ℝ) (hx : x = 3 / 8 ∨ x = 5 / 8) :
      x ∉ majorArcs (F (5 / 4) 4 ^ (6 * (1 / 100 : ℝ))) (F (5 / 4) 4) := by
    rintro ⟨q, z, hq1, hqP, hgcd, hnear⟩
    have hq2 : q < 2 := by exact_mod_cast hqP.trans_lt hP
    have hq : q = 1 := by omega
    subst q
    norm_num only [Nat.cast_one, one_mul] at hnear
    have hdist : (3 / 8 : ℝ) ≤ |x - (z : ℝ)| := by
      rcases hx with rfl | rfl
      · rcases le_or_gt z 0 with hz | hz
        · have hzr : (z : ℝ) ≤ 0 := by exact_mod_cast hz
          rw [abs_of_nonneg (by linarith)]
          linarith
        · have hzr : (1 : ℝ) ≤ z := by exact_mod_cast (by omega : 1 ≤ z)
          rw [abs_of_nonpos (by linarith)]
          linarith
      · rcases le_or_gt z 0 with hz | hz
        · have hzr : (z : ℝ) ≤ 0 := by exact_mod_cast hz
          rw [abs_of_nonneg (by linarith)]
          linarith
        · have hzr : (1 : ℝ) ≤ z := by exact_mod_cast (by omega : 1 ≤ z)
          rw [abs_of_nonpos (by linarith)]
          linarith
    have hnear' : |x - (z : ℝ)| ≤
        F (5 / 4) 4 ^ (6 * (1 / 100 : ℝ)) / F (5 / 4) 4 := by
      convert hnear using 1 <;> norm_num
    exact (not_lt_of_ge hdist) (hnear'.trans_lt hwidth)
  have hgap (h : ℤ) : (1 / 4 : ℝ) ≤ |((5 / 8 : ℝ) - 3 / 8) - (h : ℝ) / 2| := by
    have hne : (1 : ℤ) - 2 * h ≠ 0 := by omega
    have hab : (0 : ℤ) < |1 - 2 * h| := abs_pos.mpr hne
    have hi : (1 : ℤ) ≤ |1 - 2 * h| := by omega
    have hr : (1 : ℝ) ≤ |(1 : ℝ) - 2 * (h : ℝ)| := by exact_mod_cast hi
    have he : |((5 / 8 : ℝ) - 3 / 8) - (h : ℝ) / 2| = |(1 : ℝ) - 2 * (h : ℝ)| / 4 := by
      calc _ = |((1 : ℝ) - 2 * (h : ℝ)) / 4| := by congr 1; ring
        _ = _ := by rw [abs_div]; norm_num
    rw [he]
    exact div_le_div_of_nonneg_right hr (by norm_num)
  refine ⟨⟨hminor _ (Or.inl rfl), ?_⟩, ⟨hminor _ (Or.inr rfl), ?_⟩,
    (fun h _ => hrad.trans_le (hgap h)), ?_⟩
  · constructor <;> linarith
  · constructor <;> linarith
  · have hn : ‖blockPhase (indices_low_j1 (5 / 4) 4)
        (fun n => F (5 / 4) n - (1 : ℤ)) ((5 / 8 : ℝ) - 3 / 8)‖ = 1 := by
      rw [low_j1_index672]
      simp [blockPhase, U1539.norm_eC]
    rw [hn]
    exact not_le.mpr hsmall

/-- The full sealed threshold-free low_j1 auxiliary is false. This is a lab statement audit. -/
theorem low_j1_off_lattice_false672 :
    ¬ (∀ (γ δ κ : ℝ) (N : ℕ) (a b : ℝ), 1 < γ → γ < 3 / 2 →
      0 < δ → δ ≤ 1 → 0 < κ →
      a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) →
      b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) →
      (∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
        F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) →
      ‖blockPhase (indices_low_j1 γ N) (fun n => F γ n - (1 : ℤ)) (b - a)‖ ≤
        (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ))) := by
  intro h
  rcases low_j1_counterexample672 with ⟨ha, hb, hoff, hfail⟩
  exact hfail (h (5 / 4) (1 / 100) 10 4 (3 / 8) (5 / 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha hb hoff)

end LeanLab.ExceptionalSet.Task672

#print axioms LeanLab.ExceptionalSet.Task672.low_j1_index672
#print axioms LeanLab.ExceptionalSet.Task672.low_j1_scale672
#print axioms LeanLab.ExceptionalSet.Task672.low_j1_counterexample672

#print axioms LeanLab.ExceptionalSet.Task672.low_j1_off_lattice_false672
