/-
P0042 GvLtR 1989 ratio check, window 5, even n in [8920002, 10900000], least Goldbach prime at most 829.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_18 : wem 8919173 8920002 10900000 &&& gm (wpm 8919173 1980827) (P10k.take 145) = wem 8919173 8920002 10900000 := by
  decide +kernel

theorem bnd_18 : MinGBBound 8920002 10900000 829 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 145 829 (by decide)) chk_18

theorem lr_18 : (16 + 761/200000 : ℝ) ≤ Real.log ((8920002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((8920002 : ℕ) : ℝ)) 16 (f := (761/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_18 : (2 + 30913/40000 : ℝ) ≤ Real.log (16 + 761/200000 : ℝ) := by
  have h := le_log_of (x := (16 + 761/200000 : ℝ)) 2 (f := (30913/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_18 : ∀ n, Even n → 8920002 ≤ n → n ≤ 10900000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_18 ls_18 (by norm_num) (by norm_num) bnd_18

theorem r2_18 : ∀ n, Even n → 8920002 ≤ n → n ≤ 10900000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_18 ls_18 (by norm_num) (by norm_num) bnd_18

end LeanLab.GvLtR1989
