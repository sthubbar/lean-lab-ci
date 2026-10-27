/-
P0042 GvLtR 1989 ratio check, window 36, even n in [70300002, 72280000], least Goldbach prime at most 983.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_49 : wem 70299019 70300002 72280000 &&& gm (wpm 70299019 1980981) (P10k.take 166) = wem 70299019 70300002 72280000 := by
  decide +kernel

theorem bnd_49 : MinGBBound 70300002 72280000 983 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 166 983 (by decide)) chk_49

theorem lr_49 : (18 + 68281/1000000 : ℝ) ≤ Real.log ((70300002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((70300002 : ℕ) : ℝ)) 18 (f := (68281/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_49 : (2 + 223539/250000 : ℝ) ≤ Real.log (18 + 68281/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 68281/1000000 : ℝ)) 2 (f := (223539/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_49 : ∀ n, Even n → 70300002 ≤ n → n ≤ 72280000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_49 ls_49 (by norm_num) (by norm_num) bnd_49

theorem r2_49 : ∀ n, Even n → 70300002 ≤ n → n ≤ 72280000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_49 ls_49 (by norm_num) (by norm_num) bnd_49

end LeanLab.GvLtR1989
