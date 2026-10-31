/-
P0042 GvLtR 1989 ratio check, window 130, even n in [256420002, 258400000], least Goldbach prime at most 937.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_143 : wem 256419065 256420002 258400000 &&& gm (wpm2 256419065 1980935) (P10k.take 159) = wem 256419065 256420002 258400000 := by
  decide +kernel

theorem bnd_143 : MinGBBound 256420002 258400000 937 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 159 937 (by decide)) chk_143

theorem lr_143 : (19 + 181163/500000 : ℝ) ≤ Real.log ((256420002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((256420002 : ℕ) : ℝ)) 19 (f := (181163/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_143 : (2 + 15052/15625 : ℝ) ≤ Real.log (19 + 181163/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 181163/500000 : ℝ)) 2 (f := (15052/15625 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_143 : ∀ n, Even n → 256420002 ≤ n → n ≤ 258400000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_143 ls_143 (by norm_num) (by norm_num) bnd_143

theorem r2_143 : ∀ n, Even n → 256420002 ≤ n → n ≤ 258400000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_143 ls_143 (by norm_num) (by norm_num) bnd_143

end LeanLab.GvLtR1989
