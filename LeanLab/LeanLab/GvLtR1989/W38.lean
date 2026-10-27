/-
P0042 GvLtR 1989 ratio check, window 38, even n in [74260002, 76240000], least Goldbach prime at most 883.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_51 : wem 74259119 74260002 76240000 &&& gm (wpm 74259119 1980881) (P10k.take 153) = wem 74259119 74260002 76240000 := by
  decide +kernel

theorem bnd_51 : MinGBBound 74260002 76240000 883 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 153 883 (by decide)) chk_51

theorem lr_51 : (18 + 61541/500000 : ℝ) ≤ Real.log ((74260002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((74260002 : ℕ) : ℝ)) 18 (f := (61541/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_51 : (2 + 179437/200000 : ℝ) ≤ Real.log (18 + 61541/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 61541/500000 : ℝ)) 2 (f := (179437/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_51 : ∀ n, Even n → 74260002 ≤ n → n ≤ 76240000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_51 ls_51 (by norm_num) (by norm_num) bnd_51

theorem r2_51 : ∀ n, Even n → 74260002 ≤ n → n ≤ 76240000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_51 ls_51 (by norm_num) (by norm_num) bnd_51

end LeanLab.GvLtR1989
