/-
P0042 GvLtR 1989 ratio check, window 141, even n in [278200002, 280180000], least Goldbach prime at most 997.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_154 : wem 278199005 278200002 280180000 &&& gm (wpm2 278199005 1980995) (P10k.take 168) = wem 278199005 278200002 280180000 := by
  decide +kernel

theorem bnd_154 : MinGBBound 278200002 280180000 997 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 168 997 (by decide)) chk_154

theorem lr_154 : (19 + 443849/1000000 : ℝ) ≤ Real.log ((278200002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((278200002 : ℕ) : ℝ)) 19 (f := (443849/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_154 : (2 + 967529/1000000 : ℝ) ≤ Real.log (19 + 443849/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 443849/1000000 : ℝ)) 2 (f := (967529/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_154 : ∀ n, Even n → 278200002 ≤ n → n ≤ 280180000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_154 ls_154 (by norm_num) (by norm_num) bnd_154

theorem r2_154 : ∀ n, Even n → 278200002 ≤ n → n ≤ 280180000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_154 ls_154 (by norm_num) (by norm_num) bnd_154

end LeanLab.GvLtR1989
