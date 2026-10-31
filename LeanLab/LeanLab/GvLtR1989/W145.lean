/-
P0042 GvLtR 1989 ratio check, window 145, even n in [286120002, 288100000], least Goldbach prime at most 997.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_158 : wem 286119005 286120002 288100000 &&& gm (wpm2 286119005 1980995) (P10k.take 168) = wem 286119005 286120002 288100000 := by
  decide +kernel

theorem bnd_158 : MinGBBound 286120002 288100000 997 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 168 997 (by decide)) chk_158

theorem lr_158 : (19 + 5899/12500 : ℝ) ≤ Real.log ((286120002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((286120002 : ℕ) : ℝ)) 19 (f := (5899/12500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_158 : (2 + 242243/250000 : ℝ) ≤ Real.log (19 + 5899/12500 : ℝ) := by
  have h := le_log_of (x := (19 + 5899/12500 : ℝ)) 2 (f := (242243/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_158 : ∀ n, Even n → 286120002 ≤ n → n ≤ 288100000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_158 ls_158 (by norm_num) (by norm_num) bnd_158

theorem r2_158 : ∀ n, Even n → 286120002 ≤ n → n ≤ 288100000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_158 ls_158 (by norm_num) (by norm_num) bnd_158

end LeanLab.GvLtR1989
