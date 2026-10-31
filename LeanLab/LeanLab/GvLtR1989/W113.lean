/-
P0042 GvLtR 1989 ratio check, window 113, even n in [222760002, 224740000], least Goldbach prime at most 1009.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_126 : wem 222758993 222760002 224740000 &&& gm (wpm2 222758993 1981007) (P10k.take 169) = wem 222758993 222760002 224740000 := by
  decide +kernel

theorem bnd_126 : MinGBBound 222760002 224740000 1009 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 169 1009 (by decide)) chk_126

theorem lr_126 : (19 + 55401/250000 : ℝ) ≤ Real.log ((222760002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((222760002 : ℕ) : ℝ)) 19 (f := (55401/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_126 : (2 + 956033/1000000 : ℝ) ≤ Real.log (19 + 55401/250000 : ℝ) := by
  have h := le_log_of (x := (19 + 55401/250000 : ℝ)) 2 (f := (956033/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_126 : ∀ n, Even n → 222760002 ≤ n → n ≤ 224740000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_126 ls_126 (by norm_num) (by norm_num) bnd_126

theorem r2_126 : ∀ n, Even n → 222760002 ≤ n → n ≤ 224740000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_126 ls_126 (by norm_num) (by norm_num) bnd_126

end LeanLab.GvLtR1989
