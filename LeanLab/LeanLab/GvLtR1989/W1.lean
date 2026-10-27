/-
P0042 GvLtR 1989 ratio check, window 1, even n in [1000002, 2980000], least Goldbach prime at most 601.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_12 : wem 999401 1000002 2980000 &&& gm (wpm 999401 1980599) (P10k.take 110) = wem 999401 1000002 2980000 := by
  decide +kernel

theorem bnd_12 : MinGBBound 1000002 2980000 601 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 110 601 (by decide)) chk_12

theorem lr_12 : (13 + 815511/1000000 : ℝ) ≤ Real.log ((1000002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((1000002 : ℕ) : ℝ)) 13 (f := (815511/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_12 : (2 + 62579/100000 : ℝ) ≤ Real.log (13 + 815511/1000000 : ℝ) := by
  have h := le_log_of (x := (13 + 815511/1000000 : ℝ)) 2 (f := (62579/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_12 : ∀ n, Even n → 1000002 ≤ n → n ≤ 2980000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_12 ls_12 (by norm_num) (by norm_num) bnd_12

theorem r2_12 : ∀ n, Even n → 1000002 ≤ n → n ≤ 2980000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_12 ls_12 (by norm_num) (by norm_num) bnd_12

end LeanLab.GvLtR1989
