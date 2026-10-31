/-
P0042 GvLtR 1989 ratio check, window 98, even n in [193060002, 195040000], least Goldbach prime at most 991.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_111 : wem 193059011 193060002 195040000 &&& gm (wpm2 193059011 1980989) (P10k.take 167) = wem 193059011 193060002 195040000 := by
  decide +kernel

theorem bnd_111 : MinGBBound 193060002 195040000 991 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 167 991 (by decide)) chk_111

theorem lr_111 : (19 + 7851/100000 : ℝ) ≤ Real.log ((193060002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((193060002 : ℕ) : ℝ)) 19 (f := (7851/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_111 : (2 + 948561/1000000 : ℝ) ≤ Real.log (19 + 7851/100000 : ℝ) := by
  have h := le_log_of (x := (19 + 7851/100000 : ℝ)) 2 (f := (948561/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_111 : ∀ n, Even n → 193060002 ≤ n → n ≤ 195040000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_111 ls_111 (by norm_num) (by norm_num) bnd_111

theorem r2_111 : ∀ n, Even n → 193060002 ≤ n → n ≤ 195040000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_111 ls_111 (by norm_num) (by norm_num) bnd_111

end LeanLab.GvLtR1989
