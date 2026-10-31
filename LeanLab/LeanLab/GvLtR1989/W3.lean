/-
P0042 GvLtR 1989 ratio check, window 3, even n in [4960002, 6940000], least Goldbach prime at most 641.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_16 : wem 4959361 4960002 6940000 &&& gm (wpm 4959361 1980639) (P10k.take 116) = wem 4959361 4960002 6940000 := by
  decide +kernel

theorem bnd_16 : MinGBBound 4960002 6940000 641 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 116 641 (by decide)) chk_16

theorem lr_16 : (15 + 83383/200000 : ℝ) ≤ Real.log ((4960002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((4960002 : ℕ) : ℝ)) 15 (f := (83383/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_16 : (2 + 91933/125000 : ℝ) ≤ Real.log (15 + 83383/200000 : ℝ) := by
  have h := le_log_of (x := (15 + 83383/200000 : ℝ)) 2 (f := (91933/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_16 : ∀ n, Even n → 4960002 ≤ n → n ≤ 6940000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_16 ls_16 (by norm_num) (by norm_num) bnd_16

theorem r2_16 : ∀ n, Even n → 4960002 ≤ n → n ≤ 6940000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_16 ls_16 (by norm_num) (by norm_num) bnd_16

end LeanLab.GvLtR1989
