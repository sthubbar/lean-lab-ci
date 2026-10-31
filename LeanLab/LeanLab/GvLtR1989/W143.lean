/-
P0042 GvLtR 1989 ratio check, window 143, even n in [282160002, 284140000], least Goldbach prime at most 877.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_156 : wem 282159125 282160002 284140000 &&& gm (wpm2 282159125 1980875) (P10k.take 151) = wem 282159125 282160002 284140000 := by
  decide +kernel

theorem bnd_156 : MinGBBound 282160002 284140000 877 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 151 877 (by decide)) chk_156

theorem lr_156 : (19 + 457983/1000000 : ℝ) ≤ Real.log ((282160002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((282160002 : ℕ) : ℝ)) 19 (f := (457983/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_156 : (2 + 15129/15625 : ℝ) ≤ Real.log (19 + 457983/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 457983/1000000 : ℝ)) 2 (f := (15129/15625 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_156 : ∀ n, Even n → 282160002 ≤ n → n ≤ 284140000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_156 ls_156 (by norm_num) (by norm_num) bnd_156

theorem r2_156 : ∀ n, Even n → 282160002 ≤ n → n ≤ 284140000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_156 ls_156 (by norm_num) (by norm_num) bnd_156

end LeanLab.GvLtR1989
