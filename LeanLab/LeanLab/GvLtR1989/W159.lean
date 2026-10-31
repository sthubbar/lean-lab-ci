/-
P0042 GvLtR 1989 ratio check, window 159, even n in [313840002, 315820000], least Goldbach prime at most 877.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_172 : wem 313839125 313840002 315820000 &&& gm (wpm2 313839125 1980875) (P10k.take 151) = wem 313839125 313840002 315820000 := by
  decide +kernel

theorem bnd_172 : MinGBBound 313840002 315820000 877 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 151 877 (by decide)) chk_172

theorem lr_172 : (19 + 70549/125000 : ℝ) ≤ Real.log ((313840002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((313840002 : ℕ) : ℝ)) 19 (f := (70549/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_172 : (2 + 97371/100000 : ℝ) ≤ Real.log (19 + 70549/125000 : ℝ) := by
  have h := le_log_of (x := (19 + 70549/125000 : ℝ)) 2 (f := (97371/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_172 : ∀ n, Even n → 313840002 ≤ n → n ≤ 315820000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_172 ls_172 (by norm_num) (by norm_num) bnd_172

theorem r2_172 : ∀ n, Even n → 313840002 ≤ n → n ≤ 315820000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_172 ls_172 (by norm_num) (by norm_num) bnd_172

end LeanLab.GvLtR1989
