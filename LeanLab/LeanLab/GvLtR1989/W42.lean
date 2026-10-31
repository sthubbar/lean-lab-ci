/-
P0042 GvLtR 1989 ratio check, window 42, even n in [82180002, 84160000], least Goldbach prime at most 811.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_55 : wem 82179191 82180002 84160000 &&& gm (wpm 82179191 1980809) (P10k.take 141) = wem 82179191 82180002 84160000 := by
  decide +kernel

theorem bnd_55 : MinGBBound 82180002 84160000 811 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 141 811 (by decide)) chk_55

theorem lr_55 : (18 + 224421/1000000 : ℝ) ≤ Real.log ((82180002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((82180002 : ℕ) : ℝ)) 18 (f := (224421/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_55 : (2 + 902761/1000000 : ℝ) ≤ Real.log (18 + 224421/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 224421/1000000 : ℝ)) 2 (f := (902761/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_55 : ∀ n, Even n → 82180002 ≤ n → n ≤ 84160000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_55 ls_55 (by norm_num) (by norm_num) bnd_55

theorem r2_55 : ∀ n, Even n → 82180002 ≤ n → n ≤ 84160000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_55 ls_55 (by norm_num) (by norm_num) bnd_55

end LeanLab.GvLtR1989
