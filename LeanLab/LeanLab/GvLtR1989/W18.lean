/-
P0042 GvLtR 1989 ratio check, window 18, even n in [34660002, 36640000], least Goldbach prime at most 877.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_31 : wem 34659125 34660002 36640000 &&& gm (wpm 34659125 1980875) (P10k.take 151) = wem 34659125 34660002 36640000 := by
  decide +kernel

theorem bnd_31 : MinGBBound 34660002 36640000 877 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 151 877 (by decide)) chk_31

theorem lr_31 : (17 + 72219/200000 : ℝ) ≤ Real.log ((34660002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((34660002 : ℕ) : ℝ)) 17 (f := (72219/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_31 : (2 + 85423/100000 : ℝ) ≤ Real.log (17 + 72219/200000 : ℝ) := by
  have h := le_log_of (x := (17 + 72219/200000 : ℝ)) 2 (f := (85423/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_31 : ∀ n, Even n → 34660002 ≤ n → n ≤ 36640000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_31 ls_31 (by norm_num) (by norm_num) bnd_31

theorem r2_31 : ∀ n, Even n → 34660002 ≤ n → n ≤ 36640000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_31 ls_31 (by norm_num) (by norm_num) bnd_31

end LeanLab.GvLtR1989
