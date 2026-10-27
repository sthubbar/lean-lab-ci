/-
P0042 GvLtR 1989 ratio check, window 128, even n in [252460002, 254440000], least Goldbach prime at most 877.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_141 : wem 252459125 252460002 254440000 &&& gm (wpm2 252459125 1980875) (P10k.take 151) = wem 252459125 252460002 254440000 := by
  decide +kernel

theorem bnd_141 : MinGBBound 252460002 254440000 877 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 151 877 (by decide)) chk_141

theorem lr_141 : (19 + 173381/500000 : ℝ) ≤ Real.log ((252460002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((252460002 : ℕ) : ℝ)) 19 (f := (173381/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_141 : (2 + 240631/250000 : ℝ) ≤ Real.log (19 + 173381/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 173381/500000 : ℝ)) 2 (f := (240631/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_141 : ∀ n, Even n → 252460002 ≤ n → n ≤ 254440000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_141 ls_141 (by norm_num) (by norm_num) bnd_141

theorem r2_141 : ∀ n, Even n → 252460002 ≤ n → n ≤ 254440000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_141 ls_141 (by norm_num) (by norm_num) bnd_141

end LeanLab.GvLtR1989
