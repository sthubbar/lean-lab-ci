/-
P0042 GvLtR 1989 ratio check, window 131, even n in [258400002, 260380000], least Goldbach prime at most 997.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_144 : wem 258399005 258400002 260380000 &&& gm (wpm2 258399005 1980995) (P10k.take 168) = wem 258399005 258400002 260380000 := by
  decide +kernel

theorem bnd_144 : MinGBBound 258400002 260380000 997 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 168 997 (by decide)) chk_144

theorem lr_144 : (19 + 185009/500000 : ℝ) ≤ Real.log ((258400002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((258400002 : ℕ) : ℝ)) 19 (f := (185009/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_144 : (2 + 38549/40000 : ℝ) ≤ Real.log (19 + 185009/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 185009/500000 : ℝ)) 2 (f := (38549/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_144 : ∀ n, Even n → 258400002 ≤ n → n ≤ 260380000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_144 ls_144 (by norm_num) (by norm_num) bnd_144

theorem r2_144 : ∀ n, Even n → 258400002 ≤ n → n ≤ 260380000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_144 ls_144 (by norm_num) (by norm_num) bnd_144

end LeanLab.GvLtR1989
