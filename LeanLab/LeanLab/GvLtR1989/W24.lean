/-
P0042 GvLtR 1989 ratio check, window 24, even n in [46540002, 48520000], least Goldbach prime at most 811.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_37 : wem 46539191 46540002 48520000 &&& gm (wpm 46539191 1980809) (P10k.take 141) = wem 46539191 46540002 48520000 := by
  decide +kernel

theorem bnd_37 : MinGBBound 46540002 48520000 811 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 141 811 (by decide)) chk_37

theorem lr_37 : (17 + 655821/1000000 : ℝ) ≤ Real.log ((46540002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((46540002 : ℕ) : ℝ)) 17 (f := (655821/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_37 : (2 + 108883/125000 : ℝ) ≤ Real.log (17 + 655821/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 655821/1000000 : ℝ)) 2 (f := (108883/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_37 : ∀ n, Even n → 46540002 ≤ n → n ≤ 48520000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_37 ls_37 (by norm_num) (by norm_num) bnd_37

theorem r2_37 : ∀ n, Even n → 46540002 ≤ n → n ≤ 48520000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_37 ls_37 (by norm_num) (by norm_num) bnd_37

end LeanLab.GvLtR1989
