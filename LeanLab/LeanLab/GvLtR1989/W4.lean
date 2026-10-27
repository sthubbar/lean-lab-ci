/-
P0042 GvLtR 1989 ratio check, window 4, even n in [6940002, 8920000], least Goldbach prime at most 733.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_17 : wem 6939269 6940002 8920000 &&& gm (wpm 6939269 1980731) (P10k.take 130) = wem 6939269 6940002 8920000 := by
  decide +kernel

theorem bnd_17 : MinGBBound 6940002 8920000 733 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 130 733 (by decide)) chk_17

theorem lr_17 : (15 + 752811/1000000 : ℝ) ≤ Real.log ((6940002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((6940002 : ℕ) : ℝ)) 15 (f := (752811/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_17 : (2 + 757017/1000000 : ℝ) ≤ Real.log (15 + 752811/1000000 : ℝ) := by
  have h := le_log_of (x := (15 + 752811/1000000 : ℝ)) 2 (f := (757017/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_17 : ∀ n, Even n → 6940002 ≤ n → n ≤ 8920000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_17 ls_17 (by norm_num) (by norm_num) bnd_17

theorem r2_17 : ∀ n, Even n → 6940002 ≤ n → n ≤ 8920000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_17 ls_17 (by norm_num) (by norm_num) bnd_17

end LeanLab.GvLtR1989
