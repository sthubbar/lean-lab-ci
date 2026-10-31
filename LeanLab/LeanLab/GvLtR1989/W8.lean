/-
P0042 GvLtR 1989 ratio check, window 8, even n in [14860002, 16840000], least Goldbach prime at most 673.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_21 : wem 14859329 14860002 16840000 &&& gm (wpm 14859329 1980671) (P10k.take 122) = wem 14859329 14860002 16840000 := by
  decide +kernel

theorem bnd_21 : MinGBBound 14860002 16840000 673 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 122 673 (by decide)) chk_21

theorem lr_21 : (16 + 257091/500000 : ℝ) ≤ Real.log ((14860002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((14860002 : ℕ) : ℝ)) 16 (f := (257091/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_21 : (2 + 402109/500000 : ℝ) ≤ Real.log (16 + 257091/500000 : ℝ) := by
  have h := le_log_of (x := (16 + 257091/500000 : ℝ)) 2 (f := (402109/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_21 : ∀ n, Even n → 14860002 ≤ n → n ≤ 16840000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_21 ls_21 (by norm_num) (by norm_num) bnd_21

theorem r2_21 : ∀ n, Even n → 14860002 ≤ n → n ≤ 16840000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_21 ls_21 (by norm_num) (by norm_num) bnd_21

end LeanLab.GvLtR1989
