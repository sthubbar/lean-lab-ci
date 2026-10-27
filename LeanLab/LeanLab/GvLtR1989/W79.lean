/-
P0042 GvLtR 1989 ratio check, window 79, even n in [155440002, 157420000], least Goldbach prime at most 919.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_92 : wem 155439083 155440002 157420000 &&& gm (wpm2 155439083 1980917) (P10k.take 157) = wem 155439083 155440002 157420000 := by
  decide +kernel

theorem bnd_92 : MinGBBound 155440002 157420000 919 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 157 919 (by decide)) chk_92

theorem lr_92 : (18 + 861769/1000000 : ℝ) ≤ Real.log ((155440002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((155440002 : ℕ) : ℝ)) 18 (f := (861769/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_92 : (2 + 58571/62500 : ℝ) ≤ Real.log (18 + 861769/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 861769/1000000 : ℝ)) 2 (f := (58571/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_92 : ∀ n, Even n → 155440002 ≤ n → n ≤ 157420000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_92 ls_92 (by norm_num) (by norm_num) bnd_92

theorem r2_92 : ∀ n, Even n → 155440002 ≤ n → n ≤ 157420000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_92 ls_92 (by norm_num) (by norm_num) bnd_92

end LeanLab.GvLtR1989
