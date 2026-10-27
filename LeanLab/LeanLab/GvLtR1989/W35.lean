/-
P0042 GvLtR 1989 ratio check, window 35, even n in [68320002, 70300000], least Goldbach prime at most 953.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_48 : wem 68319049 68320002 70300000 &&& gm (wpm 68319049 1980951) (P10k.take 162) = wem 68319049 68320002 70300000 := by
  decide +kernel

theorem bnd_48 : MinGBBound 68320002 70300000 953 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 162 953 (by decide)) chk_48

theorem lr_48 : (18 + 1241/31250 : ℝ) ≤ Real.log ((68320002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((68320002 : ℕ) : ℝ)) 18 (f := (1241/31250 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_48 : (2 + 446287/500000 : ℝ) ≤ Real.log (18 + 1241/31250 : ℝ) := by
  have h := le_log_of (x := (18 + 1241/31250 : ℝ)) 2 (f := (446287/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_48 : ∀ n, Even n → 68320002 ≤ n → n ≤ 70300000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_48 ls_48 (by norm_num) (by norm_num) bnd_48

theorem r2_48 : ∀ n, Even n → 68320002 ≤ n → n ≤ 70300000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_48 ls_48 (by norm_num) (by norm_num) bnd_48

end LeanLab.GvLtR1989
