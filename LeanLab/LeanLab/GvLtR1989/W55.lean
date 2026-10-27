/-
P0042 GvLtR 1989 ratio check, window 55, even n in [107920002, 109900000], least Goldbach prime at most 823.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_68 : wem 107919179 107920002 109900000 &&& gm (wpm2 107919179 1980821) (P10k.take 143) = wem 107919179 107920002 109900000 := by
  decide +kernel

theorem bnd_68 : MinGBBound 107920002 109900000 823 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 143 823 (by decide)) chk_68

theorem lr_68 : (18 + 496899/1000000 : ℝ) ≤ Real.log ((107920002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((107920002 : ℕ) : ℝ)) 18 (f := (496899/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_68 : (2 + 458801/500000 : ℝ) ≤ Real.log (18 + 496899/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 496899/1000000 : ℝ)) 2 (f := (458801/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_68 : ∀ n, Even n → 107920002 ≤ n → n ≤ 109900000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_68 ls_68 (by norm_num) (by norm_num) bnd_68

theorem r2_68 : ∀ n, Even n → 107920002 ≤ n → n ≤ 109900000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_68 ls_68 (by norm_num) (by norm_num) bnd_68

end LeanLab.GvLtR1989
