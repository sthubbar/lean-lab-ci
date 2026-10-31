/-
P0042 GvLtR 1989 ratio check, window 16, even n in [30700002, 32680000], least Goldbach prime at most 811.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_29 : wem 30699191 30700002 32680000 &&& gm (wpm 30699191 1980809) (P10k.take 141) = wem 30699191 30700002 32680000 := by
  decide +kernel

theorem bnd_29 : MinGBBound 30700002 32680000 811 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 141 811 (by decide)) chk_29

theorem lr_29 : (17 + 59943/250000 : ℝ) ≤ Real.log ((30700002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((30700002 : ℕ) : ℝ)) 17 (f := (59943/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_29 : (2 + 423609/500000 : ℝ) ≤ Real.log (17 + 59943/250000 : ℝ) := by
  have h := le_log_of (x := (17 + 59943/250000 : ℝ)) 2 (f := (423609/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_29 : ∀ n, Even n → 30700002 ≤ n → n ≤ 32680000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_29 ls_29 (by norm_num) (by norm_num) bnd_29

theorem r2_29 : ∀ n, Even n → 30700002 ≤ n → n ≤ 32680000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_29 ls_29 (by norm_num) (by norm_num) bnd_29

end LeanLab.GvLtR1989
