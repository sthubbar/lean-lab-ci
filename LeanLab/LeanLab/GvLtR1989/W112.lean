/-
P0042 GvLtR 1989 ratio check, window 112, even n in [220780002, 222760000], least Goldbach prime at most 883.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_125 : wem 220779119 220780002 222760000 &&& gm (wpm2 220779119 1980881) (P10k.take 153) = wem 220779119 220780002 222760000 := by
  decide +kernel

theorem bnd_125 : MinGBBound 220780002 222760000 883 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 153 883 (by decide)) chk_125

theorem lr_125 : (19 + 53169/250000 : ℝ) ≤ Real.log ((220780002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((220780002 : ℕ) : ℝ)) 19 (f := (53169/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_125 : (2 + 955569/1000000 : ℝ) ≤ Real.log (19 + 53169/250000 : ℝ) := by
  have h := le_log_of (x := (19 + 53169/250000 : ℝ)) 2 (f := (955569/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_125 : ∀ n, Even n → 220780002 ≤ n → n ≤ 222760000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_125 ls_125 (by norm_num) (by norm_num) bnd_125

theorem r2_125 : ∀ n, Even n → 220780002 ≤ n → n ≤ 222760000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_125 ls_125 (by norm_num) (by norm_num) bnd_125

end LeanLab.GvLtR1989
