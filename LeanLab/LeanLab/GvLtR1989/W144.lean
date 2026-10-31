/-
P0042 GvLtR 1989 ratio check, window 144, even n in [284140002, 286120000], least Goldbach prime at most 907.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_157 : wem 284139095 284140002 286120000 &&& gm (wpm2 284139095 1980905) (P10k.take 155) = wem 284139095 284140002 286120000 := by
  decide +kernel

theorem bnd_157 : MinGBBound 284140002 286120000 907 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 155 907 (by decide)) chk_157

theorem lr_157 : (19 + 29061/62500 : ℝ) ≤ Real.log ((284140002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((284140002 : ℕ) : ℝ)) 19 (f := (29061/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_157 : (2 + 193723/200000 : ℝ) ≤ Real.log (19 + 29061/62500 : ℝ) := by
  have h := le_log_of (x := (19 + 29061/62500 : ℝ)) 2 (f := (193723/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_157 : ∀ n, Even n → 284140002 ≤ n → n ≤ 286120000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_157 ls_157 (by norm_num) (by norm_num) bnd_157

theorem r2_157 : ∀ n, Even n → 284140002 ≤ n → n ≤ 286120000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_157 ls_157 (by norm_num) (by norm_num) bnd_157

end LeanLab.GvLtR1989
