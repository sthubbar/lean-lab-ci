/-
P0042 GvLtR 1989 ratio check, window 115, even n in [226720002, 228700000], least Goldbach prime at most 941.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_128 : wem 226719061 226720002 228700000 &&& gm (wpm2 226719061 1980939) (P10k.take 160) = wem 226719061 226720002 228700000 := by
  decide +kernel

theorem bnd_128 : MinGBBound 226720002 228700000 941 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 160 941 (by decide)) chk_128

theorem lr_128 : (19 + 9569/40000 : ℝ) ≤ Real.log ((226720002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((226720002 : ℕ) : ℝ)) 19 (f := (9569/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_128 : (2 + 19139/20000 : ℝ) ≤ Real.log (19 + 9569/40000 : ℝ) := by
  have h := le_log_of (x := (19 + 9569/40000 : ℝ)) 2 (f := (19139/20000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_128 : ∀ n, Even n → 226720002 ≤ n → n ≤ 228700000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_128 ls_128 (by norm_num) (by norm_num) bnd_128

theorem r2_128 : ∀ n, Even n → 226720002 ≤ n → n ≤ 228700000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_128 ls_128 (by norm_num) (by norm_num) bnd_128

end LeanLab.GvLtR1989
