/-
P0042 GvLtR 1989 ratio check, window 124, even n in [244540002, 246520000], least Goldbach prime at most 1019.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_137 : wem 244538983 244540002 246520000 &&& gm (wpm2 244538983 1981017) (P10k.take 171) = wem 244538983 244540002 246520000 := by
  decide +kernel

theorem bnd_137 : MinGBBound 244540002 246520000 1019 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 171 1019 (by decide)) chk_137

theorem lr_137 : (19 + 39361/125000 : ℝ) ≤ Real.log ((244540002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((244540002 : ℕ) : ℝ)) 19 (f := (39361/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_137 : (2 + 7687/8000 : ℝ) ≤ Real.log (19 + 39361/125000 : ℝ) := by
  have h := le_log_of (x := (19 + 39361/125000 : ℝ)) 2 (f := (7687/8000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_137 : ∀ n, Even n → 244540002 ≤ n → n ≤ 246520000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_137 ls_137 (by norm_num) (by norm_num) bnd_137

theorem r2_137 : ∀ n, Even n → 244540002 ≤ n → n ≤ 246520000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_137 ls_137 (by norm_num) (by norm_num) bnd_137

end LeanLab.GvLtR1989
