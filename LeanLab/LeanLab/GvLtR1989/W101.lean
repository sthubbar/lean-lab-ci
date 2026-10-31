/-
P0042 GvLtR 1989 ratio check, window 101, even n in [199000002, 200980000], least Goldbach prime at most 863.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_114 : wem 198999139 199000002 200980000 &&& gm (wpm2 198999139 1980861) (P10k.take 150) = wem 198999139 199000002 200980000 := by
  decide +kernel

theorem bnd_114 : MinGBBound 199000002 200980000 863 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 150 863 (by decide)) chk_114

theorem lr_114 : (19 + 54407/500000 : ℝ) ≤ Real.log ((199000002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((199000002 : ℕ) : ℝ)) 19 (f := (54407/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_114 : (2 + 237537/250000 : ℝ) ≤ Real.log (19 + 54407/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 54407/500000 : ℝ)) 2 (f := (237537/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_114 : ∀ n, Even n → 199000002 ≤ n → n ≤ 200980000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_114 ls_114 (by norm_num) (by norm_num) bnd_114

theorem r2_114 : ∀ n, Even n → 199000002 ≤ n → n ≤ 200980000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_114 ls_114 (by norm_num) (by norm_num) bnd_114

end LeanLab.GvLtR1989
