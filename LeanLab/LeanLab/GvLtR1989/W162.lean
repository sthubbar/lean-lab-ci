/-
P0042 GvLtR 1989 ratio check, window 162, even n in [319780002, 321760000], least Goldbach prime at most 1009.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_175 : wem 319778993 319780002 321760000 &&& gm (wpm2 319778993 1981007) (P10k.take 169) = wem 319778993 319780002 321760000 := by
  decide +kernel

theorem bnd_175 : MinGBBound 319780002 321760000 1009 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 169 1009 (by decide)) chk_175

theorem lr_175 : (19 + 291571/500000 : ℝ) ≤ Real.log ((319780002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((319780002 : ℕ) : ℝ)) 19 (f := (291571/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_175 : (2 + 243667/250000 : ℝ) ≤ Real.log (19 + 291571/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 291571/500000 : ℝ)) 2 (f := (243667/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_175 : ∀ n, Even n → 319780002 ≤ n → n ≤ 321760000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_175 ls_175 (by norm_num) (by norm_num) bnd_175

theorem r2_175 : ∀ n, Even n → 319780002 ≤ n → n ≤ 321760000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_175 ls_175 (by norm_num) (by norm_num) bnd_175

end LeanLab.GvLtR1989
