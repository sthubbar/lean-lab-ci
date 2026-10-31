/-
P0042 GvLtR 1989 ratio check, window 72, even n in [141580002, 143560000], least Goldbach prime at most 1087.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_85 : wem 141578915 141580002 143560000 &&& gm (wpm2 141578915 1981085) (P10k.take 181) = wem 141578915 141580002 143560000 := by
  decide +kernel

theorem bnd_85 : MinGBBound 141580002 143560000 1087 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 181 1087 (by decide)) chk_85

theorem lr_85 : (18 + 384187/500000 : ℝ) ≤ Real.log ((141580002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((141580002 : ℕ) : ℝ)) 18 (f := (384187/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_85 : (2 + 233043/250000 : ℝ) ≤ Real.log (18 + 384187/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 384187/500000 : ℝ)) 2 (f := (233043/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_85 : ∀ n, Even n → 141580002 ≤ n → n ≤ 143560000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_85 ls_85 (by norm_num) (by norm_num) bnd_85

theorem r2_85 : ∀ n, Even n → 141580002 ≤ n → n ≤ 143560000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_85 ls_85 (by norm_num) (by norm_num) bnd_85

end LeanLab.GvLtR1989
