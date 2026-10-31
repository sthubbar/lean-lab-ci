/-
P0042 GvLtR 1989 ratio check, window 30, even n in [58420002, 60400000], least Goldbach prime at most 1093.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_43 : wem 58418909 58420002 60400000 &&& gm (wpm 58418909 1981091) (P10k.take 183) = wem 58418909 58420002 60400000 := by
  decide +kernel

theorem bnd_43 : MinGBBound 58420002 60400000 1093 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 183 1093 (by decide)) chk_43

theorem lr_43 : (17 + 883167/1000000 : ℝ) ≤ Real.log ((58420002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((58420002 : ℕ) : ℝ)) 17 (f := (883167/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_43 : (2 + 441929/500000 : ℝ) ≤ Real.log (17 + 883167/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 883167/1000000 : ℝ)) 2 (f := (441929/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_43 : ∀ n, Even n → 58420002 ≤ n → n ≤ 60400000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_43 ls_43 (by norm_num) (by norm_num) bnd_43

theorem r2_43 : ∀ n, Even n → 58420002 ≤ n → n ≤ 60400000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_43 ls_43 (by norm_num) (by norm_num) bnd_43

end LeanLab.GvLtR1989
