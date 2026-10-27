/-
P0042 GvLtR 1989 ratio check, window 23, even n in [44560002, 46540000], least Goldbach prime at most 823.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_36 : wem 44559179 44560002 46540000 &&& gm (wpm 44559179 1980821) (P10k.take 143) = wem 44559179 44560002 46540000 := by
  decide +kernel

theorem bnd_36 : MinGBBound 44560002 46540000 823 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 143 823 (by decide)) chk_36

theorem lr_36 : (17 + 306173/500000 : ℝ) ≤ Real.log ((44560002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((44560002 : ℕ) : ℝ)) 17 (f := (306173/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_36 : (2 + 868599/1000000 : ℝ) ≤ Real.log (17 + 306173/500000 : ℝ) := by
  have h := le_log_of (x := (17 + 306173/500000 : ℝ)) 2 (f := (868599/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_36 : ∀ n, Even n → 44560002 ≤ n → n ≤ 46540000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_36 ls_36 (by norm_num) (by norm_num) bnd_36

theorem r2_36 : ∀ n, Even n → 44560002 ≤ n → n ≤ 46540000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_36 ls_36 (by norm_num) (by norm_num) bnd_36

end LeanLab.GvLtR1989
