/-
P0042 GvLtR 1989 ratio check, window 123, even n in [242560002, 244540000], least Goldbach prime at most 859.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_136 : wem 242559143 242560002 244540000 &&& gm (wpm2 242559143 1980857) (P10k.take 149) = wem 242559143 242560002 244540000 := by
  decide +kernel

theorem bnd_136 : MinGBBound 242560002 244540000 859 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 149 859 (by decide)) chk_136

theorem lr_136 : (19 + 153379/500000 : ℝ) ≤ Real.log ((242560002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((242560002 : ℕ) : ℝ)) 19 (f := (153379/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_136 : (2 + 480227/500000 : ℝ) ≤ Real.log (19 + 153379/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 153379/500000 : ℝ)) 2 (f := (480227/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_136 : ∀ n, Even n → 242560002 ≤ n → n ≤ 244540000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_136 ls_136 (by norm_num) (by norm_num) bnd_136

theorem r2_136 : ∀ n, Even n → 242560002 ≤ n → n ≤ 244540000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_136 ls_136 (by norm_num) (by norm_num) bnd_136

end LeanLab.GvLtR1989
