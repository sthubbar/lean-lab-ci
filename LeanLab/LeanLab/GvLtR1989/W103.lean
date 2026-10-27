/-
P0042 GvLtR 1989 ratio check, window 103, even n in [202960002, 204940000], least Goldbach prime at most 1021.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_116 : wem 202958981 202960002 204940000 &&& gm (wpm2 202958981 1981019) (P10k.take 172) = wem 202958981 202960002 204940000 := by
  decide +kernel

theorem bnd_116 : MinGBBound 202960002 204940000 1021 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 172 1021 (by decide)) chk_116

theorem lr_116 : (19 + 64259/500000 : ℝ) ≤ Real.log ((202960002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((202960002 : ℕ) : ℝ)) 19 (f := (64259/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_116 : (2 + 951179/1000000 : ℝ) ≤ Real.log (19 + 64259/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 64259/500000 : ℝ)) 2 (f := (951179/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_116 : ∀ n, Even n → 202960002 ≤ n → n ≤ 204940000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_116 ls_116 (by norm_num) (by norm_num) bnd_116

theorem r2_116 : ∀ n, Even n → 202960002 ≤ n → n ≤ 204940000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_116 ls_116 (by norm_num) (by norm_num) bnd_116

end LeanLab.GvLtR1989
