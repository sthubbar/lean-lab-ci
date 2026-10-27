/-
P0042 GvLtR 1989 ratio check, window 19, even n in [36640002, 38620000], least Goldbach prime at most 1039.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_32 : wem 36638963 36640002 38620000 &&& gm (wpm 36638963 1981037) (P10k.take 175) = wem 36638963 36640002 38620000 := by
  decide +kernel

theorem bnd_32 : MinGBBound 36640002 38620000 1039 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 175 1039 (by decide)) chk_32

theorem lr_32 : (17 + 8333/20000 : ℝ) ≤ Real.log ((36640002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((36640002 : ℕ) : ℝ)) 17 (f := (8333/20000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_32 : (2 + 34297/40000 : ℝ) ≤ Real.log (17 + 8333/20000 : ℝ) := by
  have h := le_log_of (x := (17 + 8333/20000 : ℝ)) 2 (f := (34297/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_32 : ∀ n, Even n → 36640002 ≤ n → n ≤ 38620000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_32 ls_32 (by norm_num) (by norm_num) bnd_32

theorem r2_32 : ∀ n, Even n → 36640002 ≤ n → n ≤ 38620000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_32 ls_32 (by norm_num) (by norm_num) bnd_32

end LeanLab.GvLtR1989
