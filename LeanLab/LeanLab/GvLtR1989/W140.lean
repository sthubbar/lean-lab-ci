/-
P0042 GvLtR 1989 ratio check, window 140, even n in [276220002, 278200000], least Goldbach prime at most 823.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_153 : wem 276219179 276220002 278200000 &&& gm (wpm2 276219179 1980821) (P10k.take 143) = wem 276219179 276220002 278200000 := by
  decide +kernel

theorem bnd_153 : MinGBBound 276220002 278200000 823 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 143 823 (by decide)) chk_153

theorem lr_153 : (19 + 436707/1000000 : ℝ) ≤ Real.log ((276220002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((276220002 : ℕ) : ℝ)) 19 (f := (436707/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_153 : (2 + 483581/500000 : ℝ) ≤ Real.log (19 + 436707/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 436707/1000000 : ℝ)) 2 (f := (483581/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_153 : ∀ n, Even n → 276220002 ≤ n → n ≤ 278200000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_153 ls_153 (by norm_num) (by norm_num) bnd_153

theorem r2_153 : ∀ n, Even n → 276220002 ≤ n → n ≤ 278200000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_153 ls_153 (by norm_num) (by norm_num) bnd_153

end LeanLab.GvLtR1989
