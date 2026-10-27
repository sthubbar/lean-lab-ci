/-
P0042 GvLtR 1989 ratio check, window 70, even n in [137620002, 139600000], least Goldbach prime at most 839.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_83 : wem 137619163 137620002 139600000 &&& gm (wpm2 137619163 1980837) (P10k.take 146) = wem 137619163 137620002 139600000 := by
  decide +kernel

theorem bnd_83 : MinGBBound 137620002 139600000 839 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 146 839 (by decide)) chk_83

theorem lr_83 : (18 + 148001/200000 : ℝ) ≤ Real.log ((137620002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((137620002 : ℕ) : ℝ)) 18 (f := (148001/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_83 : (2 + 930659/1000000 : ℝ) ≤ Real.log (18 + 148001/200000 : ℝ) := by
  have h := le_log_of (x := (18 + 148001/200000 : ℝ)) 2 (f := (930659/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_83 : ∀ n, Even n → 137620002 ≤ n → n ≤ 139600000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_83 ls_83 (by norm_num) (by norm_num) bnd_83

theorem r2_83 : ∀ n, Even n → 137620002 ≤ n → n ≤ 139600000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_83 ls_83 (by norm_num) (by norm_num) bnd_83

end LeanLab.GvLtR1989
