import LeanLab.HelfgottMajor.SPLIT_psi_le_rosser_schoenfeld
import LeanLab.HelfgottMajor.SPLIT_S3_psi_le_mid_range
import LeanLab.HelfgottMajor.SPLIT_S3_psi_le_large_range

/-!
# Split of `psi_le_of_two_thousand_le` (`HelfgottMajor/SPLIT_psi_le_rosser_schoenfeld`)

The target is the range `2000 ≤ x` of Rosser and Schoenfeld 1962, Theorem 12:
`ψ(x) ≤ 1.03882 x`.  Page 77 of the paper splits it into three ranges, checked on the page
images of `papers/RosserSchoenfeld1962.pdf`, pages 77 and 78:

* `2000 ≤ x < 50653`, "by Theorem 18 and Table III"; here the part `x < 20000` is a finite
  check, proved below as
  `psi_le_of_two_thousand_le_of_lt` by a kernel check of `lcm(1, ..., N) · 5^N ≤ 14^N` and
  `2.8 ≤ e^{1.03882}`;
* `50653 ≤ x ≤ 10^8`, "by Theorem 18 and (4.12)"; with the rest `20000 ≤ x < 50653` of the
  first range this is leaf `psi_le_mid_range` on `20000 ≤ x ≤ 10^8`;
* `10^8 < x`, "by Table I as soon as we have justified the values in this table", leaf
  `psi_le_large_range`, resting on the explicit zeros of `ζ`.

AI wrote this Lean code.  Binary Goldbach is OPEN.
-/

namespace LeanLab.HelfgottMajor.SplitPsiTwoThousand

open Real LeanLab.HelfgottMajor.SplitPsiRosserSchoenfeld

/-- The kernel checker for `lcm(1, ..., n) · 5^n ≤ 14^n`, with accumulators, run from `n` on for
`k` steps; sound by `chkMid_sound`.  Helper for the range `2000 ≤ x < 20000` of Rosser and
Schoenfeld 1962 Theorem 12, page 77, where `ψ(x)/x ≤ 1.0099` leaves room for the ratio `2.8`. -/
def chkMid : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _ => true
  | k + 1, n, l, a, b => decide (l * a ≤ b) &&
      chkMid k (n + 1) (Nat.lcm l (n + 1)) (a * 5) (b * 14)

/-- Soundness of `chkMid`, by induction on the number of steps. -/
theorem chkMid_sound : ∀ k n, chkMid k n (lcmRec n) (5 ^ n) (14 ^ n) = true →
    ∀ j < k, lcmRec (n + j) * 5 ^ (n + j) ≤ 14 ^ (n + j) := by
  intro k
  induction k with
  | zero => intro n _ j hj; omega
  | succ k ih =>
    intro n h j hj
    simp only [chkMid, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases j with _ | j
    · simpa using h.1
    · have h2 : chkMid k (n + 1) (lcmRec (n + 1)) (5 ^ (n + 1)) (14 ^ (n + 1)) = true := by
        simpa [lcmRec, pow_succ] using h.2
      have := ih (n + 1) h2 j (by omega)
      rwa [show n + 1 + j = n + (j + 1) by omega] at this

/-- The kernel check for `2000 ≤ n < 20000` by `decide +kernel`, kept below `50653` to stay under
8 GB of memory. -/
theorem chkMid_run : chkMid 18000 2000 (lcmRec 2000) (5 ^ 2000) (14 ^ 2000) = true := by
  decide +kernel

/-- `2.8 ≤ e^{1.03882}`, from `e > 2.7182818283` and `1 + x ≤ e^x`. -/
theorem exp_ge_two_point_eight : (2.8 : ℝ) ≤ Real.exp 1.03882 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.add_one_le_exp (0.03882 : ℝ)
  have h3 : Real.exp 1.03882 = Real.exp 1 * Real.exp 0.03882 := by
    rw [← Real.exp_add]; norm_num
  rw [h3]
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.03882]

/-- Rosser and Schoenfeld 1962, page 77, the part `2000 ≤ x < 20000` of the range
`2000 ≤ x < 50653` of Theorem 12, proved:
`ψ(x) = log lcm(1, ..., ⌊x⌋) ≤ ⌊x⌋ log 2.8 ≤ 1.03882 x`. -/
theorem psi_le_of_two_thousand_le_of_lt (x : ℝ) (hx : 2000 ≤ x) (hx' : x < 20000) :
    Chebyshev.psi x ≤ 1.03882 * x := by
  set N := ⌊x⌋₊ with hNdef
  have hN1 : 2000 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN2 : N < 20000 := (Nat.floor_lt (by linarith)).mpr (by exact_mod_cast hx')
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hcheck : lcmRec N * 5 ^ N ≤ 14 ^ N := by
    have := chkMid_sound 18000 2000 chkMid_run (N - 2000) (by omega)
    rwa [show 2000 + (N - 2000) = N by omega] at this
  rw [psi_eq_psi_floor, ← hNdef, Chebyshev.psi_eq_log_lcmUpto]
  have hpos : (0 : ℝ) < (Nat.lcmUpto N : ℝ) := by exact_mod_cast Nat.lcmUpto_pos N
  rw [Real.log_le_iff_le_exp hpos]
  have key : (Nat.lcmUpto N : ℝ) ≤ (2.8 : ℝ) ^ N := by
    rw [lcmRec_eq_lcmUpto] at hcheck
    have h' : (Nat.lcmUpto N : ℝ) * 5 ^ N ≤ 14 ^ N := by exact_mod_cast hcheck
    have hp : (0 : ℝ) < 5 ^ N := by positivity
    rw [show (2.8 : ℝ) = 14 / 5 by norm_num, div_pow, le_div_iff₀ hp]
    exact h'
  refine key.trans ?_
  calc (2.8 : ℝ) ^ N ≤ Real.exp 1.03882 ^ N :=
        pow_le_pow_left₀ (by norm_num) exp_ge_two_point_eight N
    _ = Real.exp (1.03882 * N) := by rw [mul_comm, Real.exp_nat_mul]
    _ ≤ Real.exp (1.03882 * x) := Real.exp_le_exp.mpr (by nlinarith)

/-- LEAF: Rosser and Schoenfeld 1962, page 77, the range `20000 ≤ x ≤ 10^8` of Theorem 12:
below `50653` "by Theorem 18 and Table III", from `50653` on "by Theorem 18 and (4.12)".  HARD:
Theorem 18 is their explicit formula bound; a direct computation of `ψ` up to `10^8`, for
instance by the kernel check used here below `20000` in chunks, would also do. -/
theorem psi_le_mid_range (x : ℝ) (hx : 20000 ≤ x) (hx' : x ≤ 10 ^ 8) :
    Chebyshev.psi x ≤ 1.03882 * x := by
  exact LeanLab.HelfgottMajor.SplitS3PsiMid.psi_le_mid_range_split x hx hx'

/-- LEAF: Rosser and Schoenfeld 1962, pages 77 and 78, the range `10^8 < x` of Theorem 12, "by
Table I as soon as we have justified the values in this table", resting on the explicit zeros of
`ζ` and an explicit zero free region.  HARD. -/
theorem psi_le_large_range (x : ℝ) (hx : 10 ^ 8 < x) :
    Chebyshev.psi x ≤ 1.03882 * x := by
  exact LeanLab.HelfgottMajor.SplitS3PsiLarge.psi_le_large_range_split x hx

/-- The parent leaf `psi_le_of_two_thousand_le`, verbatim, from the proved range and the two
range leaves. -/
theorem psi_le_of_two_thousand_le_split (x : ℝ) (hx : 2000 ≤ x) :
    Chebyshev.psi x ≤ 1.03882 * x := by
  rcases lt_or_ge x 20000 with h1 | h1
  · exact psi_le_of_two_thousand_le_of_lt x hx h1
  · rcases le_or_gt x (10 ^ 8) with h2 | h2
    · exact psi_le_mid_range x h1 h2
    · exact psi_le_large_range x h2

end LeanLab.HelfgottMajor.SplitPsiTwoThousand

#print axioms LeanLab.HelfgottMajor.SplitPsiTwoThousand.psi_le_mid_range
#print axioms LeanLab.HelfgottMajor.SplitPsiTwoThousand.psi_le_large_range
