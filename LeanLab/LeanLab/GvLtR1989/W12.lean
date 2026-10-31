/-
P0042 GvLtR 1989 ratio check, window 12, even n in [22780002, 24760000], least Goldbach prime at most 929.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_25 : wem 22779073 22780002 24760000 &&& gm (wpm 22779073 1980927) (P10k.take 158) = wem 22779073 22780002 24760000 := by
  decide +kernel

theorem bnd_25 : MinGBBound 22780002 24760000 929 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 158 929 (by decide)) chk_25

theorem lr_25 : (16 + 58837/62500 : ℝ) ≤ Real.log ((22780002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((22780002 : ℕ) : ℝ)) 16 (f := (58837/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_25 : (2 + 414879/500000 : ℝ) ≤ Real.log (16 + 58837/62500 : ℝ) := by
  have h := le_log_of (x := (16 + 58837/62500 : ℝ)) 2 (f := (414879/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_25 : ∀ n, Even n → 22780002 ≤ n → n ≤ 24760000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_25 ls_25 (by norm_num) (by norm_num) bnd_25

theorem r2_25 : ∀ n, Even n → 22780002 ≤ n → n ≤ 24760000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_25 ls_25 (by norm_num) (by norm_num) bnd_25

end LeanLab.GvLtR1989
