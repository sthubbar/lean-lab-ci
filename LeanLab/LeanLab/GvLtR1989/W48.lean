/-
P0042 GvLtR 1989 ratio check, window 48, even n in [94060002, 96040000], least Goldbach prime at most 859.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_61 : wem 94059143 94060002 96040000 &&& gm (wpm 94059143 1980857) (P10k.take 149) = wem 94059143 94060002 96040000 := by
  decide +kernel

theorem bnd_61 : MinGBBound 94060002 96040000 859 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 149 859 (by decide)) chk_61

theorem lr_61 : (18 + 179721/500000 : ℝ) ≤ Real.log ((94060002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((94060002 : ℕ) : ℝ)) 18 (f := (179721/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_61 : (2 + 455071/500000 : ℝ) ≤ Real.log (18 + 179721/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 179721/500000 : ℝ)) 2 (f := (455071/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_61 : ∀ n, Even n → 94060002 ≤ n → n ≤ 96040000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_61 ls_61 (by norm_num) (by norm_num) bnd_61

theorem r2_61 : ∀ n, Even n → 94060002 ≤ n → n ≤ 96040000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_61 ls_61 (by norm_num) (by norm_num) bnd_61

end LeanLab.GvLtR1989
