/-
P0042 GvLtR 1989 ratio check, window 110, even n in [216820002, 218800000], least Goldbach prime at most 877.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_123 : wem 216819125 216820002 218800000 &&& gm (wpm2 216819125 1980875) (P10k.take 151) = wem 216819125 216820002 218800000 := by
  decide +kernel

theorem bnd_123 : MinGBBound 216820002 218800000 877 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 151 877 (by decide)) chk_123

theorem lr_123 : (19 + 194577/1000000 : ℝ) ≤ Real.log ((216820002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((216820002 : ℕ) : ℝ)) 19 (f := (194577/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_123 : (2 + 477313/500000 : ℝ) ≤ Real.log (19 + 194577/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 194577/1000000 : ℝ)) 2 (f := (477313/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_123 : ∀ n, Even n → 216820002 ≤ n → n ≤ 218800000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_123 ls_123 (by norm_num) (by norm_num) bnd_123

theorem r2_123 : ∀ n, Even n → 216820002 ≤ n → n ≤ 218800000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_123 ls_123 (by norm_num) (by norm_num) bnd_123

end LeanLab.GvLtR1989
