/-
P0042 GvLtR 1989 ratio check, window 84, even n in [165340002, 167320000], least Goldbach prime at most 859.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_97 : wem 165339143 165340002 167320000 &&& gm (wpm2 165339143 1980857) (P10k.take 149) = wem 165339143 165340002 167320000 := by
  decide +kernel

theorem bnd_97 : MinGBBound 165340002 167320000 859 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 149 859 (by decide)) chk_97

theorem lr_97 : (18 + 923513/1000000 : ℝ) ≤ Real.log ((165340002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((165340002 : ℕ) : ℝ)) 18 (f := (923513/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_97 : (2 + 235101/250000 : ℝ) ≤ Real.log (18 + 923513/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 923513/1000000 : ℝ)) 2 (f := (235101/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_97 : ∀ n, Even n → 165340002 ≤ n → n ≤ 167320000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_97 ls_97 (by norm_num) (by norm_num) bnd_97

theorem r2_97 : ∀ n, Even n → 165340002 ≤ n → n ≤ 167320000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_97 ls_97 (by norm_num) (by norm_num) bnd_97

end LeanLab.GvLtR1989
