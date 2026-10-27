/-
P0042 GvLtR 1989 ratio check, window 50, even n in [98020002, 100000000], least Goldbach prime at most 829.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_63 : wem 98019173 98020002 100000000 &&& gm (wpm 98019173 1980827) (P10k.take 145) = wem 98019173 98020002 100000000 := by
  decide +kernel

theorem bnd_63 : MinGBBound 98020002 100000000 829 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 145 829 (by decide)) chk_63

theorem lr_63 : (18 + 400681/1000000 : ℝ) ≤ Real.log ((98020002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((98020002 : ℕ) : ℝ)) 18 (f := (400681/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_63 : (2 + 456193/500000 : ℝ) ≤ Real.log (18 + 400681/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 400681/1000000 : ℝ)) 2 (f := (456193/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_63 : ∀ n, Even n → 98020002 ≤ n → n ≤ 100000000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_63 ls_63 (by norm_num) (by norm_num) bnd_63

theorem r2_63 : ∀ n, Even n → 98020002 ≤ n → n ≤ 100000000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_63 ls_63 (by norm_num) (by norm_num) bnd_63

end LeanLab.GvLtR1989
