/-
P0042 GvLtR 1989 ratio check, window 156, even n in [307900002, 309880000], least Goldbach prime at most 797.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_169 : wem 307899205 307900002 309880000 &&& gm (wpm2 307899205 1980795) (P10k.take 139) = wem 307899205 307900002 309880000 := by
  decide +kernel

theorem bnd_169 : MinGBBound 307900002 309880000 797 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 139 797 (by decide)) chk_169

theorem lr_169 : (19 + 136321/250000 : ℝ) ≤ Real.log ((307900002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((307900002 : ℕ) : ℝ)) 19 (f := (136321/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_169 : (2 + 972733/1000000 : ℝ) ≤ Real.log (19 + 136321/250000 : ℝ) := by
  have h := le_log_of (x := (19 + 136321/250000 : ℝ)) 2 (f := (972733/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_169 : ∀ n, Even n → 307900002 ≤ n → n ≤ 309880000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_169 ls_169 (by norm_num) (by norm_num) bnd_169

theorem r2_169 : ∀ n, Even n → 307900002 ≤ n → n ≤ 309880000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_169 ls_169 (by norm_num) (by norm_num) bnd_169

end LeanLab.GvLtR1989
