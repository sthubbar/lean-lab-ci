/-
P0042 GvLtR 1989 ratio check, window 22, even n in [42580002, 44560000], least Goldbach prime at most 769.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_35 : wem 42579233 42580002 44560000 &&& gm (wpm 42579233 1980767) (P10k.take 136) = wem 42579233 42580002 44560000 := by
  decide +kernel

theorem bnd_35 : MinGBBound 42580002 44560000 769 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 136 769 (by decide)) chk_35

theorem lr_35 : (17 + 283447/500000 : ℝ) ≤ Real.log ((42580002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((42580002 : ℕ) : ℝ)) 17 (f := (283447/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_35 : (2 + 173203/200000 : ℝ) ≤ Real.log (17 + 283447/500000 : ℝ) := by
  have h := le_log_of (x := (17 + 283447/500000 : ℝ)) 2 (f := (173203/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_35 : ∀ n, Even n → 42580002 ≤ n → n ≤ 44560000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_35 ls_35 (by norm_num) (by norm_num) bnd_35

theorem r2_35 : ∀ n, Even n → 42580002 ≤ n → n ≤ 44560000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_35 ls_35 (by norm_num) (by norm_num) bnd_35

end LeanLab.GvLtR1989
