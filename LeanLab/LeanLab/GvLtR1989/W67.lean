/-
P0042 GvLtR 1989 ratio check, window 67, even n in [131680002, 133660000], least Goldbach prime at most 883.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_80 : wem 131679119 131680002 133660000 &&& gm (wpm2 131679119 1980881) (P10k.take 153) = wem 131679119 131680002 133660000 := by
  decide +kernel

theorem bnd_80 : MinGBBound 131680002 133660000 883 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 153 883 (by decide)) chk_80

theorem lr_80 : (18 + 173971/250000 : ℝ) ≤ Real.log ((131680002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((131680002 : ℕ) : ℝ)) 18 (f := (173971/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_80 : (2 + 464151/500000 : ℝ) ≤ Real.log (18 + 173971/250000 : ℝ) := by
  have h := le_log_of (x := (18 + 173971/250000 : ℝ)) 2 (f := (464151/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_80 : ∀ n, Even n → 131680002 ≤ n → n ≤ 133660000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_80 ls_80 (by norm_num) (by norm_num) bnd_80

theorem r2_80 : ∀ n, Even n → 131680002 ≤ n → n ≤ 133660000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_80 ls_80 (by norm_num) (by norm_num) bnd_80

end LeanLab.GvLtR1989
