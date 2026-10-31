/-
P0042 GvLtR 1989 ratio check, window 80, even n in [157420002, 159400000], least Goldbach prime at most 919.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_93 : wem 157419083 157420002 159400000 &&& gm (wpm2 157419083 1980917) (P10k.take 157) = wem 157419083 157420002 159400000 := by
  decide +kernel

theorem bnd_93 : MinGBBound 157420002 159400000 919 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 157 919 (by decide)) chk_93

theorem lr_93 : (18 + 437213/500000 : ℝ) ≤ Real.log ((157420002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((157420002 : ℕ) : ℝ)) 18 (f := (437213/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_93 : (2 + 468903/500000 : ℝ) ≤ Real.log (18 + 437213/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 437213/500000 : ℝ)) 2 (f := (468903/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_93 : ∀ n, Even n → 157420002 ≤ n → n ≤ 159400000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_93 ls_93 (by norm_num) (by norm_num) bnd_93

theorem r2_93 : ∀ n, Even n → 157420002 ≤ n → n ≤ 159400000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_93 ls_93 (by norm_num) (by norm_num) bnd_93

end LeanLab.GvLtR1989
