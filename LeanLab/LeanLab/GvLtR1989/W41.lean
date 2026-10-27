/-
P0042 GvLtR 1989 ratio check, window 41, even n in [80200002, 82180000], least Goldbach prime at most 739.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_54 : wem 80199263 80200002 82180000 &&& gm (wpm 80199263 1980737) (P10k.take 131) = wem 80199263 80200002 82180000 := by
  decide +kernel

theorem bnd_54 : MinGBBound 80200002 82180000 739 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 131 739 (by decide)) chk_54

theorem lr_54 : (18 + 200033/1000000 : ℝ) ≤ Real.log ((80200002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((80200002 : ℕ) : ℝ)) 18 (f := (200033/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_54 : (2 + 450711/500000 : ℝ) ≤ Real.log (18 + 200033/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 200033/1000000 : ℝ)) 2 (f := (450711/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_54 : ∀ n, Even n → 80200002 ≤ n → n ≤ 82180000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_54 ls_54 (by norm_num) (by norm_num) bnd_54

theorem r2_54 : ∀ n, Even n → 80200002 ≤ n → n ≤ 82180000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_54 ls_54 (by norm_num) (by norm_num) bnd_54

end LeanLab.GvLtR1989
