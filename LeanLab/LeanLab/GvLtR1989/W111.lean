/-
P0042 GvLtR 1989 ratio check, window 111, even n in [218800002, 220780000], least Goldbach prime at most 1033.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_124 : wem 218798969 218800002 220780000 &&& gm (wpm2 218798969 1981031) (P10k.take 174) = wem 218798969 218800002 220780000 := by
  decide +kernel

theorem bnd_124 : MinGBBound 218800002 220780000 1033 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 174 1033 (by decide)) chk_124

theorem lr_124 : (19 + 203667/1000000 : ℝ) ≤ Real.log ((218800002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((218800002 : ℕ) : ℝ)) 19 (f := (203667/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_124 : (2 + 9551/10000 : ℝ) ≤ Real.log (19 + 203667/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 203667/1000000 : ℝ)) 2 (f := (9551/10000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_124 : ∀ n, Even n → 218800002 ≤ n → n ≤ 220780000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_124 ls_124 (by norm_num) (by norm_num) bnd_124

theorem r2_124 : ∀ n, Even n → 218800002 ≤ n → n ≤ 220780000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_124 ls_124 (by norm_num) (by norm_num) bnd_124

end LeanLab.GvLtR1989
