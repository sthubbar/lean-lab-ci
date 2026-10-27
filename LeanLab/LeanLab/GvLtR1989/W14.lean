/-
P0042 GvLtR 1989 ratio check, window 14, even n in [26740002, 28720000], least Goldbach prime at most 997.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_27 : wem 26739005 26740002 28720000 &&& gm (wpm 26739005 1980995) (P10k.take 168) = wem 26739005 26740002 28720000 := by
  decide +kernel

theorem bnd_27 : MinGBBound 26740002 28720000 997 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 168 997 (by decide)) chk_27

theorem lr_27 : (17 + 10167/100000 : ℝ) ≤ Real.log ((26740002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((26740002 : ℕ) : ℝ)) 17 (f := (10167/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_27 : (2 + 33567/40000 : ℝ) ≤ Real.log (17 + 10167/100000 : ℝ) := by
  have h := le_log_of (x := (17 + 10167/100000 : ℝ)) 2 (f := (33567/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_27 : ∀ n, Even n → 26740002 ≤ n → n ≤ 28720000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_27 ls_27 (by norm_num) (by norm_num) bnd_27

theorem r2_27 : ∀ n, Even n → 26740002 ≤ n → n ≤ 28720000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_27 ls_27 (by norm_num) (by norm_num) bnd_27

end LeanLab.GvLtR1989
