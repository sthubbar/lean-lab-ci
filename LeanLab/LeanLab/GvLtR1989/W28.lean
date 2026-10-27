/-
P0042 GvLtR 1989 ratio check, window 28, even n in [54460002, 56440000], least Goldbach prime at most 857.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_41 : wem 54459145 54460002 56440000 &&& gm (wpm 54459145 1980855) (P10k.take 148) = wem 54459145 54460002 56440000 := by
  decide +kernel

theorem bnd_41 : MinGBBound 54460002 56440000 857 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 148 857 (by decide)) chk_41

theorem lr_41 : (17 + 50811/62500 : ℝ) ≤ Real.log ((54460002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((54460002 : ℕ) : ℝ)) 17 (f := (50811/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_41 : (2 + 439963/500000 : ℝ) ≤ Real.log (17 + 50811/62500 : ℝ) := by
  have h := le_log_of (x := (17 + 50811/62500 : ℝ)) 2 (f := (439963/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_41 : ∀ n, Even n → 54460002 ≤ n → n ≤ 56440000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_41 ls_41 (by norm_num) (by norm_num) bnd_41

theorem r2_41 : ∀ n, Even n → 54460002 ≤ n → n ≤ 56440000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_41 ls_41 (by norm_num) (by norm_num) bnd_41

end LeanLab.GvLtR1989
