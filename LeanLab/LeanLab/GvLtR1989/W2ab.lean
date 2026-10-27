/-
P0042 GvLtR 1989 ratio check, window 2ab, even n in [3475002, 3970000], least Goldbach prime at most 751.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_14 : wem 3474251 3475002 3970000 &&& gm (wpm 3474251 495749) (P10k.take 133) = wem 3474251 3475002 3970000 := by
  decide +kernel

theorem bnd_14 : MinGBBound 3475002 3970000 751 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 133 751 (by decide)) chk_14

theorem lr_14 : (15 + 3819/62500 : ℝ) ≤ Real.log ((3475002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((3475002 : ℕ) : ℝ)) 15 (f := (3819/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_14 : (2 + 356057/500000 : ℝ) ≤ Real.log (15 + 3819/62500 : ℝ) := by
  have h := le_log_of (x := (15 + 3819/62500 : ℝ)) 2 (f := (356057/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_14 : ∀ n, Even n → 3475002 ≤ n → n ≤ 3970000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_14 ls_14 (by norm_num) (by norm_num) bnd_14

theorem r2_14 : ∀ n, Even n → 3475002 ≤ n → n ≤ 3970000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_14 ls_14 (by norm_num) (by norm_num) bnd_14

end LeanLab.GvLtR1989
