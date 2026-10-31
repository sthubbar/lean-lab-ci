/-
P0042 GvLtR 1989 ratio check, window 66, even n in [129700002, 131680000], least Goldbach prime at most 881.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_79 : wem 129699121 129700002 131680000 &&& gm (wpm2 129699121 1980879) (P10k.take 152) = wem 129699121 129700002 131680000 := by
  decide +kernel

theorem bnd_79 : MinGBBound 129700002 131680000 881 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 152 881 (by decide)) chk_79

theorem lr_79 : (18 + 680733/1000000 : ℝ) ≤ Real.log ((129700002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((129700002 : ℕ) : ℝ)) 18 (f := (680733/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_79 : (2 + 927491/1000000 : ℝ) ≤ Real.log (18 + 680733/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 680733/1000000 : ℝ)) 2 (f := (927491/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_79 : ∀ n, Even n → 129700002 ≤ n → n ≤ 131680000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_79 ls_79 (by norm_num) (by norm_num) bnd_79

theorem r2_79 : ∀ n, Even n → 129700002 ≤ n → n ≤ 131680000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_79 ls_79 (by norm_num) (by norm_num) bnd_79

end LeanLab.GvLtR1989
