/-
P0042 GvLtR 1989 ratio check, window 32, even n in [62380002, 64360000], least Goldbach prime at most 991.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_45 : wem 62379011 62380002 64360000 &&& gm (wpm 62379011 1980989) (P10k.take 167) = wem 62379011 62380002 64360000 := by
  decide +kernel

theorem bnd_45 : MinGBBound 62380002 64360000 991 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 167 991 (by decide)) chk_45

theorem lr_45 : (17 + 474377/500000 : ℝ) ≤ Real.log ((62380002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((62380002 : ℕ) : ℝ)) 17 (f := (474377/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_45 : (2 + 887519/1000000 : ℝ) ≤ Real.log (17 + 474377/500000 : ℝ) := by
  have h := le_log_of (x := (17 + 474377/500000 : ℝ)) 2 (f := (887519/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_45 : ∀ n, Even n → 62380002 ≤ n → n ≤ 64360000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_45 ls_45 (by norm_num) (by norm_num) bnd_45

theorem r2_45 : ∀ n, Even n → 62380002 ≤ n → n ≤ 64360000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_45 ls_45 (by norm_num) (by norm_num) bnd_45

end LeanLab.GvLtR1989
