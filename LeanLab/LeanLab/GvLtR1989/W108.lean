/-
P0042 GvLtR 1989 ratio check, window 108, even n in [212860002, 214840000], least Goldbach prime at most 997.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_121 : wem 212859005 212860002 214840000 &&& gm (wpm2 212859005 1980995) (P10k.take 168) = wem 212859005 212860002 214840000 := by
  decide +kernel

theorem bnd_121 : MinGBBound 212860002 214840000 997 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 168 997 (by decide)) chk_121

theorem lr_121 : (19 + 11009/62500 : ℝ) ≤ Real.log ((212860002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((212860002 : ℕ) : ℝ)) 19 (f := (11009/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_121 : (2 + 476833/500000 : ℝ) ≤ Real.log (19 + 11009/62500 : ℝ) := by
  have h := le_log_of (x := (19 + 11009/62500 : ℝ)) 2 (f := (476833/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_121 : ∀ n, Even n → 212860002 ≤ n → n ≤ 214840000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_121 ls_121 (by norm_num) (by norm_num) bnd_121

theorem r2_121 : ∀ n, Even n → 212860002 ≤ n → n ≤ 214840000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_121 ls_121 (by norm_num) (by norm_num) bnd_121

end LeanLab.GvLtR1989
