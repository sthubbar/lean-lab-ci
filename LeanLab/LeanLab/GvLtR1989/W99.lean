/-
P0042 GvLtR 1989 ratio check, window 99, even n in [195040002, 197020000], least Goldbach prime at most 773.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_112 : wem 195039229 195040002 197020000 &&& gm (wpm2 195039229 1980771) (P10k.take 137) = wem 195039229 195040002 197020000 := by
  decide +kernel

theorem bnd_112 : MinGBBound 195040002 197020000 773 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 137 773 (by decide)) chk_112

theorem lr_112 : (19 + 44357/500000 : ℝ) ≤ Real.log ((195040002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((195040002 : ℕ) : ℝ)) 19 (f := (44357/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_112 : (2 + 118637/125000 : ℝ) ≤ Real.log (19 + 44357/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 44357/500000 : ℝ)) 2 (f := (118637/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_112 : ∀ n, Even n → 195040002 ≤ n → n ≤ 197020000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_112 ls_112 (by norm_num) (by norm_num) bnd_112

theorem r2_112 : ∀ n, Even n → 195040002 ≤ n → n ≤ 197020000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_112 ls_112 (by norm_num) (by norm_num) bnd_112

end LeanLab.GvLtR1989
