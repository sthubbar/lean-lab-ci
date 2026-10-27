/-
P0042 GvLtR 1989 ratio check, window 83, even n in [163360002, 165340000], least Goldbach prime at most 797.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_96 : wem 163359205 163360002 165340000 &&& gm (wpm2 163359205 1980795) (P10k.take 139) = wem 163359205 163360002 165340000 := by
  decide +kernel

theorem bnd_96 : MinGBBound 163360002 165340000 797 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 139 797 (by decide)) chk_96

theorem lr_96 : (18 + 182293/200000 : ℝ) ≤ Real.log ((163360002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((163360002 : ℕ) : ℝ)) 18 (f := (182293/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_96 : (2 + 939767/1000000 : ℝ) ≤ Real.log (18 + 182293/200000 : ℝ) := by
  have h := le_log_of (x := (18 + 182293/200000 : ℝ)) 2 (f := (939767/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_96 : ∀ n, Even n → 163360002 ≤ n → n ≤ 165340000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_96 ls_96 (by norm_num) (by norm_num) bnd_96

theorem r2_96 : ∀ n, Even n → 163360002 ≤ n → n ≤ 165340000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_96 ls_96 (by norm_num) (by norm_num) bnd_96

end LeanLab.GvLtR1989
