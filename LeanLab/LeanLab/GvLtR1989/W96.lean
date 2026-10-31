/-
P0042 GvLtR 1989 ratio check, window 96, even n in [189100002, 191080000], least Goldbach prime at most 757.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_109 : wem 189099245 189100002 191080000 &&& gm (wpm2 189099245 1980755) (P10k.take 134) = wem 189099245 189100002 191080000 := by
  decide +kernel

theorem bnd_109 : MinGBBound 189100002 191080000 757 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 134 757 (by decide)) chk_109

theorem lr_109 : (19 + 11557/200000 : ℝ) ≤ Real.log ((189100002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((189100002 : ℕ) : ℝ)) 19 (f := (11557/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_109 : (2 + 473737/500000 : ℝ) ≤ Real.log (19 + 11557/200000 : ℝ) := by
  have h := le_log_of (x := (19 + 11557/200000 : ℝ)) 2 (f := (473737/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_109 : ∀ n, Even n → 189100002 ≤ n → n ≤ 191080000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_109 ls_109 (by norm_num) (by norm_num) bnd_109

theorem r2_109 : ∀ n, Even n → 189100002 ≤ n → n ≤ 191080000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_109 ls_109 (by norm_num) (by norm_num) bnd_109

end LeanLab.GvLtR1989
