/-
P0042 GvLtR 1989 ratio check, window 105, even n in [206920002, 208900000], least Goldbach prime at most 929.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_118 : wem 206919073 206920002 208900000 &&& gm (wpm2 206919073 1980927) (P10k.take 158) = wem 206919073 206920002 208900000 := by
  decide +kernel

theorem bnd_118 : MinGBBound 206920002 208900000 929 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 158 929 (by decide)) chk_118

theorem lr_118 : (19 + 147841/1000000 : ℝ) ≤ Real.log ((206920002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((206920002 : ℕ) : ℝ)) 19 (f := (147841/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_118 : (2 + 238047/250000 : ℝ) ≤ Real.log (19 + 147841/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 147841/1000000 : ℝ)) 2 (f := (238047/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_118 : ∀ n, Even n → 206920002 ≤ n → n ≤ 208900000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_118 ls_118 (by norm_num) (by norm_num) bnd_118

theorem r2_118 : ∀ n, Even n → 206920002 ≤ n → n ≤ 208900000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_118 ls_118 (by norm_num) (by norm_num) bnd_118

end LeanLab.GvLtR1989
