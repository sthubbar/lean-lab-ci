/-
P0042 GvLtR 1989 ratio check, window 56, even n in [109900002, 111880000], least Goldbach prime at most 739.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_69 : wem 109899263 109900002 111880000 &&& gm (wpm2 109899263 1980737) (P10k.take 131) = wem 109899263 109900002 111880000 := by
  decide +kernel

theorem bnd_69 : MinGBBound 109900002 111880000 739 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 131 739 (by decide)) chk_69

theorem lr_69 : (18 + 12877/25000 : ℝ) ≤ Real.log ((109900002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((109900002 : ℕ) : ℝ)) 18 (f := (12877/25000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_69 : (2 + 114823/125000 : ℝ) ≤ Real.log (18 + 12877/25000 : ℝ) := by
  have h := le_log_of (x := (18 + 12877/25000 : ℝ)) 2 (f := (114823/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_69 : ∀ n, Even n → 109900002 ≤ n → n ≤ 111880000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_69 ls_69 (by norm_num) (by norm_num) bnd_69

theorem r2_69 : ∀ n, Even n → 109900002 ≤ n → n ≤ 111880000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_69 ls_69 (by norm_num) (by norm_num) bnd_69

end LeanLab.GvLtR1989
