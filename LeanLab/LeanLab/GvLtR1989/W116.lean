/-
P0042 GvLtR 1989 ratio check, window 116, even n in [228700002, 230680000], least Goldbach prime at most 823.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_129 : wem 228699179 228700002 230680000 &&& gm (wpm2 228699179 1980821) (P10k.take 143) = wem 228699179 228700002 230680000 := by
  decide +kernel

theorem bnd_129 : MinGBBound 228700002 230680000 823 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 143 823 (by decide)) chk_129

theorem lr_129 : (19 + 3099/12500 : ℝ) ≤ Real.log ((228700002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((228700002 : ℕ) : ℝ)) 19 (f := (3099/12500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_129 : (2 + 478701/500000 : ℝ) ≤ Real.log (19 + 3099/12500 : ℝ) := by
  have h := le_log_of (x := (19 + 3099/12500 : ℝ)) 2 (f := (478701/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_129 : ∀ n, Even n → 228700002 ≤ n → n ≤ 230680000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_129 ls_129 (by norm_num) (by norm_num) bnd_129

theorem r2_129 : ∀ n, Even n → 228700002 ≤ n → n ≤ 230680000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_129 ls_129 (by norm_num) (by norm_num) bnd_129

end LeanLab.GvLtR1989
