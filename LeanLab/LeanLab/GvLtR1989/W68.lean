/-
P0042 GvLtR 1989 ratio check, window 68, even n in [133660002, 135640000], least Goldbach prime at most 857.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_81 : wem 133659145 133660002 135640000 &&& gm (wpm2 133659145 1980855) (P10k.take 148) = wem 133659145 133660002 135640000 := by
  decide +kernel

theorem bnd_81 : MinGBBound 133660002 135640000 857 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 148 857 (by decide)) chk_81

theorem lr_81 : (18 + 88851/125000 : ℝ) ≤ Real.log ((133660002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((133660002 : ℕ) : ℝ)) 18 (f := (88851/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_81 : (2 + 9291/10000 : ℝ) ≤ Real.log (18 + 88851/125000 : ℝ) := by
  have h := le_log_of (x := (18 + 88851/125000 : ℝ)) 2 (f := (9291/10000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_81 : ∀ n, Even n → 133660002 ≤ n → n ≤ 135640000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_81 ls_81 (by norm_num) (by norm_num) bnd_81

theorem r2_81 : ∀ n, Even n → 133660002 ≤ n → n ≤ 135640000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_81 ls_81 (by norm_num) (by norm_num) bnd_81

end LeanLab.GvLtR1989
