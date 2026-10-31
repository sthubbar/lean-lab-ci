/-
P0042 GvLtR 1989 ratio check, window 117, even n in [230680002, 232660000], least Goldbach prime at most 991.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_130 : wem 230679011 230680002 232660000 &&& gm (wpm2 230679011 1980989) (P10k.take 167) = wem 230679011 230680002 232660000 := by
  decide +kernel

theorem bnd_130 : MinGBBound 230680002 232660000 991 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 167 991 (by decide)) chk_130

theorem lr_130 : (19 + 256541/1000000 : ℝ) ≤ Real.log ((230680002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((230680002 : ℕ) : ℝ)) 19 (f := (256541/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_130 : (2 + 957849/1000000 : ℝ) ≤ Real.log (19 + 256541/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 256541/1000000 : ℝ)) 2 (f := (957849/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_130 : ∀ n, Even n → 230680002 ≤ n → n ≤ 232660000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_130 ls_130 (by norm_num) (by norm_num) bnd_130

theorem r2_130 : ∀ n, Even n → 230680002 ≤ n → n ≤ 232660000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_130 ls_130 (by norm_num) (by norm_num) bnd_130

end LeanLab.GvLtR1989
