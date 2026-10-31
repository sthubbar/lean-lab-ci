/-
P0042 GvLtR 1989 ratio check, window 154, even n in [303940002, 305920000], least Goldbach prime at most 883.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_167 : wem 303939119 303940002 305920000 &&& gm (wpm2 303939119 1980881) (P10k.take 153) = wem 303939119 303940002 305920000 := by
  decide +kernel

theorem bnd_167 : MinGBBound 303940002 305920000 883 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 153 883 (by decide)) chk_167

theorem lr_167 : (19 + 532339/1000000 : ℝ) ≤ Real.log ((303940002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((303940002 : ℕ) : ℝ)) 19 (f := (532339/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_167 : (2 + 97207/100000 : ℝ) ≤ Real.log (19 + 532339/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 532339/1000000 : ℝ)) 2 (f := (97207/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_167 : ∀ n, Even n → 303940002 ≤ n → n ≤ 305920000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_167 ls_167 (by norm_num) (by norm_num) bnd_167

theorem r2_167 : ∀ n, Even n → 303940002 ≤ n → n ≤ 305920000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_167 ls_167 (by norm_num) (by norm_num) bnd_167

end LeanLab.GvLtR1989
