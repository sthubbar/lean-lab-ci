/-
P0042 GvLtR 1989 ratio check, window 40, even n in [78220002, 80200000], least Goldbach prime at most 1009.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_53 : wem 78218993 78220002 80200000 &&& gm (wpm 78218993 1981007) (P10k.take 169) = wem 78218993 78220002 80200000 := by
  decide +kernel

theorem bnd_53 : MinGBBound 78220002 80200000 1009 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 169 1009 (by decide)) chk_53

theorem lr_53 : (18 + 87517/500000 : ℝ) ≤ Real.log ((78220002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((78220002 : ℕ) : ℝ)) 18 (f := (87517/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_53 : (2 + 900047/1000000 : ℝ) ≤ Real.log (18 + 87517/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 87517/500000 : ℝ)) 2 (f := (900047/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_53 : ∀ n, Even n → 78220002 ≤ n → n ≤ 80200000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_53 ls_53 (by norm_num) (by norm_num) bnd_53

theorem r2_53 : ∀ n, Even n → 78220002 ≤ n → n ≤ 80200000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_53 ls_53 (by norm_num) (by norm_num) bnd_53

end LeanLab.GvLtR1989
