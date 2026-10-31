/-
P0042 GvLtR 1989 ratio check, window 37, even n in [72280002, 74260000], least Goldbach prime at most 937.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_50 : wem 72279065 72280002 74260000 &&& gm (wpm 72279065 1980935) (P10k.take 159) = wem 72279065 72280002 74260000 := by
  decide +kernel

theorem bnd_50 : MinGBBound 72280002 74260000 937 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 159 937 (by decide)) chk_50

theorem lr_50 : (18 + 96057/1000000 : ℝ) ≤ Real.log ((72280002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((72280002 : ℕ) : ℝ)) 18 (f := (96057/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_50 : (2 + 895693/1000000 : ℝ) ≤ Real.log (18 + 96057/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 96057/1000000 : ℝ)) 2 (f := (895693/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_50 : ∀ n, Even n → 72280002 ≤ n → n ≤ 74260000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_50 ls_50 (by norm_num) (by norm_num) bnd_50

theorem r2_50 : ∀ n, Even n → 72280002 ≤ n → n ≤ 74260000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_50 ls_50 (by norm_num) (by norm_num) bnd_50

end LeanLab.GvLtR1989
