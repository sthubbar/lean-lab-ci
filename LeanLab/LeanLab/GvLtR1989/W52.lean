/-
P0042 GvLtR 1989 ratio check, window 52, even n in [101980002, 103960000], least Goldbach prime at most 953.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_65 : wem 101979049 101980002 103960000 &&& gm (wpm2 101979049 1980951) (P10k.take 162) = wem 101979049 101980002 103960000 := by
  decide +kernel

theorem bnd_65 : MinGBBound 101980002 103960000 953 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 162 953 (by decide)) chk_65

theorem lr_65 : (18 + 220143/500000 : ℝ) ≤ Real.log ((101980002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((101980002 : ℕ) : ℝ)) 18 (f := (220143/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_65 : (2 + 114317/125000 : ℝ) ≤ Real.log (18 + 220143/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 220143/500000 : ℝ)) 2 (f := (114317/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_65 : ∀ n, Even n → 101980002 ≤ n → n ≤ 103960000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_65 ls_65 (by norm_num) (by norm_num) bnd_65

theorem r2_65 : ∀ n, Even n → 101980002 ≤ n → n ≤ 103960000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_65 ls_65 (by norm_num) (by norm_num) bnd_65

end LeanLab.GvLtR1989
