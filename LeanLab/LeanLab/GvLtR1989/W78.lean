/-
P0042 GvLtR 1989 ratio check, window 78, even n in [153460002, 155440000], least Goldbach prime at most 883.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_91 : wem 153459119 153460002 155440000 &&& gm (wpm2 153459119 1980881) (P10k.take 153) = wem 153459119 153460002 155440000 := by
  decide +kernel

theorem bnd_91 : MinGBBound 153460002 155440000 883 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 153 883 (by decide)) chk_91

theorem lr_91 : (18 + 848949/1000000 : ℝ) ≤ Real.log ((153460002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((153460002 : ℕ) : ℝ)) 18 (f := (848949/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_91 : (2 + 117057/125000 : ℝ) ≤ Real.log (18 + 848949/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 848949/1000000 : ℝ)) 2 (f := (117057/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_91 : ∀ n, Even n → 153460002 ≤ n → n ≤ 155440000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_91 ls_91 (by norm_num) (by norm_num) bnd_91

theorem r2_91 : ∀ n, Even n → 153460002 ≤ n → n ≤ 155440000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_91 ls_91 (by norm_num) (by norm_num) bnd_91

end LeanLab.GvLtR1989
