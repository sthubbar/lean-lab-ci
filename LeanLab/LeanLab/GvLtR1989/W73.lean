/-
P0042 GvLtR 1989 ratio check, window 73, even n in [143560002, 145540000], least Goldbach prime at most 991.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_86 : wem 143559011 143560002 145540000 &&& gm (wpm2 143559011 1980989) (P10k.take 167) = wem 143559011 143560002 145540000 := by
  decide +kernel

theorem bnd_86 : MinGBBound 143560002 145540000 991 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 167 991 (by decide)) chk_86

theorem lr_86 : (18 + 391131/500000 : ℝ) ≤ Real.log ((143560002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((143560002 : ℕ) : ℝ)) 18 (f := (391131/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_86 : (2 + 932911/1000000 : ℝ) ≤ Real.log (18 + 391131/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 391131/500000 : ℝ)) 2 (f := (932911/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_86 : ∀ n, Even n → 143560002 ≤ n → n ≤ 145540000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_86 ls_86 (by norm_num) (by norm_num) bnd_86

theorem r2_86 : ∀ n, Even n → 143560002 ≤ n → n ≤ 145540000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_86 ls_86 (by norm_num) (by norm_num) bnd_86

end LeanLab.GvLtR1989
