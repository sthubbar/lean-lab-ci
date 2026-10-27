/-
P0042 GvLtR 1989 ratio check, window 61, even n in [119800002, 121780000], least Goldbach prime at most 1051.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_74 : wem 119798951 119800002 121780000 &&& gm (wpm2 119798951 1981049) (P10k.take 177) = wem 119798951 119800002 121780000 := by
  decide +kernel

theorem bnd_74 : MinGBBound 119800002 121780000 1051 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 177 1051 (by decide)) chk_74

theorem lr_74 : (18 + 601333/1000000 : ℝ) ≤ Real.log ((119800002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((119800002 : ℕ) : ℝ)) 18 (f := (601333/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_74 : (2 + 28851/31250 : ℝ) ≤ Real.log (18 + 601333/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 601333/1000000 : ℝ)) 2 (f := (28851/31250 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_74 : ∀ n, Even n → 119800002 ≤ n → n ≤ 121780000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_74 ls_74 (by norm_num) (by norm_num) bnd_74

theorem r2_74 : ∀ n, Even n → 119800002 ≤ n → n ≤ 121780000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_74 ls_74 (by norm_num) (by norm_num) bnd_74

end LeanLab.GvLtR1989
