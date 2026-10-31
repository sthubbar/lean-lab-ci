/-
P0042 GvLtR 1989 ratio check, window 43, even n in [84160002, 86140000], least Goldbach prime at most 929.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_56 : wem 84159073 84160002 86140000 &&& gm (wpm 84159073 1980927) (P10k.take 158) = wem 84159073 84160002 86140000 := by
  decide +kernel

theorem bnd_56 : MinGBBound 84160002 86140000 929 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 158 929 (by decide)) chk_56

theorem lr_56 : (18 + 248229/1000000 : ℝ) ≤ Real.log ((84160002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((84160002 : ℕ) : ℝ)) 18 (f := (248229/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_56 : (2 + 904067/1000000 : ℝ) ≤ Real.log (18 + 248229/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 248229/1000000 : ℝ)) 2 (f := (904067/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_56 : ∀ n, Even n → 84160002 ≤ n → n ≤ 86140000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_56 ls_56 (by norm_num) (by norm_num) bnd_56

theorem r2_56 : ∀ n, Even n → 84160002 ≤ n → n ≤ 86140000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_56 ls_56 (by norm_num) (by norm_num) bnd_56

end LeanLab.GvLtR1989
