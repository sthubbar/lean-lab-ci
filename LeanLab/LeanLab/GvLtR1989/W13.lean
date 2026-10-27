/-
P0042 GvLtR 1989 ratio check, window 13, even n in [24760002, 26740000], least Goldbach prime at most 751.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_26 : wem 24759251 24760002 26740000 &&& gm (wpm 24759251 1980749) (P10k.take 133) = wem 24759251 24760002 26740000 := by
  decide +kernel

theorem bnd_26 : MinGBBound 24760002 26740000 751 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 133 751 (by decide)) chk_26

theorem lr_26 : (17 + 24739/1000000 : ℝ) ≤ Real.log ((24760002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((24760002 : ℕ) : ℝ)) 17 (f := (24739/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_26 : (2 + 417333/500000 : ℝ) ≤ Real.log (17 + 24739/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 24739/1000000 : ℝ)) 2 (f := (417333/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_26 : ∀ n, Even n → 24760002 ≤ n → n ≤ 26740000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_26 ls_26 (by norm_num) (by norm_num) bnd_26

theorem r2_26 : ∀ n, Even n → 24760002 ≤ n → n ≤ 26740000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_26 ls_26 (by norm_num) (by norm_num) bnd_26

end LeanLab.GvLtR1989
