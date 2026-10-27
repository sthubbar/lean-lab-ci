/-
P0042 GvLtR 1989 ratio check, window 44, even n in [86140002, 88120000], least Goldbach prime at most 907.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_57 : wem 86139095 86140002 88120000 &&& gm (wpm 86139095 1980905) (P10k.take 155) = wem 86139095 86140002 88120000 := by
  decide +kernel

theorem bnd_57 : MinGBBound 86140002 88120000 907 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 155 907 (by decide)) chk_57

theorem lr_57 : (18 + 271483/1000000 : ℝ) ≤ Real.log ((86140002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((86140002 : ℕ) : ℝ)) 18 (f := (271483/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_57 : (2 + 45267/50000 : ℝ) ≤ Real.log (18 + 271483/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 271483/1000000 : ℝ)) 2 (f := (45267/50000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_57 : ∀ n, Even n → 86140002 ≤ n → n ≤ 88120000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_57 ls_57 (by norm_num) (by norm_num) bnd_57

theorem r2_57 : ∀ n, Even n → 86140002 ≤ n → n ≤ 88120000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_57 ls_57 (by norm_num) (by norm_num) bnd_57

end LeanLab.GvLtR1989
