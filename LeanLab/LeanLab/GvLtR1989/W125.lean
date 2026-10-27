/-
P0042 GvLtR 1989 ratio check, window 125, even n in [246520002, 248500000], least Goldbach prime at most 1123.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_138 : wem 246518879 246520002 248500000 &&& gm (wpm2 246518879 1981121) (P10k.take 188) = wem 246518879 246520002 248500000 := by
  decide +kernel

theorem bnd_138 : MinGBBound 246520002 248500000 1123 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 188 1123 (by decide)) chk_138

theorem lr_138 : (19 + 40369/125000 : ℝ) ≤ Real.log ((246520002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((246520002 : ℕ) : ℝ)) 19 (f := (40369/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_138 : (2 + 240323/250000 : ℝ) ≤ Real.log (19 + 40369/125000 : ℝ) := by
  have h := le_log_of (x := (19 + 40369/125000 : ℝ)) 2 (f := (240323/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_138 : ∀ n, Even n → 246520002 ≤ n → n ≤ 248500000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_138 ls_138 (by norm_num) (by norm_num) bnd_138

theorem r2_138 : ∀ n, Even n → 246520002 ≤ n → n ≤ 248500000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_138 ls_138 (by norm_num) (by norm_num) bnd_138

end LeanLab.GvLtR1989
