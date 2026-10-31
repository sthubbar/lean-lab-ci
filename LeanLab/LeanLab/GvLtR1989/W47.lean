/-
P0042 GvLtR 1989 ratio check, window 47, even n in [92080002, 94060000], least Goldbach prime at most 827.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_60 : wem 92079175 92080002 94060000 &&& gm (wpm 92079175 1980825) (P10k.take 144) = wem 92079175 92080002 94060000 := by
  decide +kernel

theorem bnd_60 : MinGBBound 92080002 94060000 827 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 144 827 (by decide)) chk_60

theorem lr_60 : (18 + 338167/1000000 : ℝ) ≤ Real.log ((92080002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((92080002 : ℕ) : ℝ)) 18 (f := (338167/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_60 : (2 + 908983/1000000 : ℝ) ≤ Real.log (18 + 338167/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 338167/1000000 : ℝ)) 2 (f := (908983/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_60 : ∀ n, Even n → 92080002 ≤ n → n ≤ 94060000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_60 ls_60 (by norm_num) (by norm_num) bnd_60

theorem r2_60 : ∀ n, Even n → 92080002 ≤ n → n ≤ 94060000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_60 ls_60 (by norm_num) (by norm_num) bnd_60

end LeanLab.GvLtR1989
