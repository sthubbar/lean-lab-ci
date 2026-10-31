/-
P0042 GvLtR 1989 ratio check, window 6, even n in [10900002, 12880000], least Goldbach prime at most 751.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_19 : wem 10899251 10900002 12880000 &&& gm (wpm 10899251 1980749) (P10k.take 133) = wem 10899251 10900002 12880000 := by
  decide +kernel

theorem bnd_19 : MinGBBound 10900002 12880000 751 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 133 751 (by decide)) chk_19

theorem lr_19 : (16 + 12767/62500 : ℝ) ≤ Real.log ((10900002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((10900002 : ℕ) : ℝ)) 16 (f := (12767/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_19 : (2 + 785273/1000000 : ℝ) ≤ Real.log (16 + 12767/62500 : ℝ) := by
  have h := le_log_of (x := (16 + 12767/62500 : ℝ)) 2 (f := (785273/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_19 : ∀ n, Even n → 10900002 ≤ n → n ≤ 12880000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_19 ls_19 (by norm_num) (by norm_num) bnd_19

theorem r2_19 : ∀ n, Even n → 10900002 ≤ n → n ≤ 12880000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_19 ls_19 (by norm_num) (by norm_num) bnd_19

end LeanLab.GvLtR1989
