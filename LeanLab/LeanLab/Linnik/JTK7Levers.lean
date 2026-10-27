/-
AI-written Lean code, Claude, 2026-10-19, run 20261019T1309Z-443, unit U-1061, T2 FRONTIER, I-0073.
P0025 Johnston, Trudgian 2026, arXiv 2605.17825 v2, criterion (23) of Theorem 2 at
K = 7 = 4 + 3, unconditional inputs: A(4) ≤ 0.003992, A(3) ≤ 0.013598, R₀ ≤ 1.93656,
c₁ = 0.7894009, log P / log N = 4/9 - ε, C₁ = 6.7814 of Proposition 2 from Lichtman.
With these the left side of (23) is about 1.0038, so K = 7 is just out of reach.

This file maps the four levers, each a CONDITIONAL target: any ONE of the improvements below,
with every other input as printed, makes (23) hold at K = 7, so every large even N would be a
sum of two primes and exactly 7 powers of 2, unconditionally, against the published 8.
- `k7_of_C1`: a Goldbach upper sieve constant C₁ ≤ 6.76, in place of 6.7814.
- `k7_of_c1`: a large values constant c₁ ≤ 0.7887, in place of 0.7894009, a 0.09 percent cut.
- `k7_of_lp`: a major arc range log P / log N ≥ 0.482, in place of 4/9.
- `k7_MPR`: c₁ = 0.77779, the value JT derive from the announced, unpublished
  Maynard-Pandey-Radziwiłł minor arc bound N^{19/24+ε}; the left side is below 0.935,
  the paper prints 0.934.
C₀ enters only through its upper bound; the twin prime constant is 0.66016 18158...,
and the first three theorems take C₀ ≤ 0.66017 as a hypothesis, `k7_MPR` needs only the
lab's proved `twinC_le_06614`. Theorem 2 itself, Pintz-Ruzsa's criterion, stays cited.
Python: Linnik/numerics/k7_levers_U1061.py; exact thresholds C₁ 6.76193, c₁ 0.788795,
log P / log N 0.48036. Goldbach is open.
-/
import LeanLab.Linnik.JTNumeric

open Real

noncomputable section
namespace LeanLab.Linnik.JT

/-- Monotone bound for the K = 7 left side of (23) from upper bounds on every input. -/
lemma crit43_le {A3 A4 C2 c1 A3m A4m C2m c1m : ℝ} (hA30 : 0 ≤ A3) (hA3 : A3 ≤ A3m)
    (hA40 : 0 ≤ A4) (hA4 : A4 ≤ A4m) (hC20 : 0 ≤ C2) (hC2 : C2 ≤ C2m) (hc10 : 0 ≤ c1)
    (hc1 : c1 ≤ c1m) :
    crit A4 A3 C2 c1 4 3 ≤ √((A4m + C2m * c1m ^ 6) * (A3m + C2m * c1m ^ 4)) := by
  unfold crit
  norm_num
  have ha : 0 ≤ A4 + C2 * c1 ^ 6 := by positivity
  rw [← sqrt_mul ha]
  apply sqrt_le_sqrt
  have p6 : c1 ^ 6 ≤ c1m ^ 6 := pow_le_pow_left₀ hc10 hc1 6
  have p4 : c1 ^ 4 ≤ c1m ^ 4 := pow_le_pow_left₀ hc10 hc1 4
  have hC2m : 0 ≤ C2m := hC20.trans hC2
  have a1 : A4 + C2 * c1 ^ 6 ≤ A4m + C2m * c1m ^ 6 := by
    have := mul_le_mul hC2 p6 (by positivity) hC2m; linarith
  have b1 : A3 + C2 * c1 ^ 4 ≤ A3m + C2m * c1m ^ 4 := by
    have := mul_le_mul hC2 p4 (by positivity) hC2m; linarith
  exact mul_le_mul a1 b1 (by positivity) (by linarith [mul_nonneg hC2m (pow_nonneg (hc10.trans hc1) 6)])

lemma C2p_nonneg {C1 ε R0 C0 lp : ℝ} (h : 0 ≤ C1 + ε - 2) (hR0 : 0 ≤ R0) (hC0 : 0 ≤ C0)
    (hl1 : lp ≤ 1) : 0 ≤ C2p C1 ε R0 C0 lp := by
  unfold C2p
  have := log_pos (show (1 : ℝ) < 2 by norm_num)
  have : 0 ≤ (1 - lp) * log 2 / 2 := by nlinarith
  have : 0 ≤ 1 / 2 * (C1 + ε - 2) * R0 * C0 := mul_nonneg (mul_nonneg (by linarith) hR0) hC0
  linarith

/-- **Lever 1, C₁.** Any Goldbach upper sieve constant C₁ ≤ 6.76 gives (23) at K = 7. -/
theorem k7_of_C1 {C1 A3 A4 R0 C0 ε lp c1 : ℝ} (hC1a : 2 ≤ C1) (hC1 : C1 ≤ 6.76)
    (hA30 : 0 ≤ A3) (hA3 : A3 ≤ 0.013598) (hA40 : 0 ≤ A4) (hA4 : A4 ≤ 0.003992)
    (hR0 : 0 ≤ R0) (hR : R0 ≤ 1.93656) (hC00 : 0 ≤ C0) (hC0 : C0 ≤ 0.66017)
    (he0 : 0 ≤ ε) (he : ε ≤ 1e-6) (hl : 0.4444 ≤ lp) (hl1 : lp ≤ 1)
    (hc10 : 0 ≤ c1) (hc1 : c1 ≤ 0.7894009) :
    crit A4 A3 (C2p C1 ε R0 C0 lp) c1 4 3 < 1 := by
  have hC := C2p_le (C1m := 6.76) (εm := 1e-6) (R0m := 1.93656) (C0m := 0.66017)
    (lpm := 0.4444) hC1 he (by linarith) hR0 hR hC00 hC0 hl
  have hmax : C2p 6.76 1e-6 1.93656 0.66017 0.4444 ≤ 3.23529 := by
    unfold C2p; have := log_two_lt_d9; norm_num at this ⊢; linarith
  refine lt_of_le_of_lt (crit43_le hA30 hA3 hA40 hA4 (C2p_nonneg (by linarith) hR0 hC00 hl1)
    (hC.trans hmax) hc10 hc1) ?_
  rw [sqrt_lt' (by norm_num)]; norm_num

/-- **Lever 2, c₁.** With JT's C₁ = 6.7814, any large values constant c₁ ≤ 0.7887 gives (23)
at K = 7. -/
theorem k7_of_c1 {A3 A4 R0 C0 ε lp c1 : ℝ}
    (hA30 : 0 ≤ A3) (hA3 : A3 ≤ 0.013598) (hA40 : 0 ≤ A4) (hA4 : A4 ≤ 0.003992)
    (hR0 : 0 ≤ R0) (hR : R0 ≤ 1.93656) (hC00 : 0 ≤ C0) (hC0 : C0 ≤ 0.66017)
    (he0 : 0 ≤ ε) (he : ε ≤ 1e-6) (hl : 0.4444 ≤ lp) (hl1 : lp ≤ 1)
    (hc10 : 0 ≤ c1) (hc1 : c1 ≤ 0.7887) :
    crit A4 A3 (C2p 6.7814 ε R0 C0 lp) c1 4 3 < 1 := by
  have hC := C2p_le (C1 := 6.7814) (C1m := 6.7814) (εm := 1e-6) (R0m := 1.93656)
    (C0m := 0.66017) (lpm := 0.4444) le_rfl he (by linarith) hR0 hR hC00 hC0 hl
  have hmax : C2p 6.7814 1e-6 1.93656 0.66017 0.4444 ≤ 3.24897 := by
    unfold C2p; have := log_two_lt_d9; norm_num at this ⊢; linarith
  refine lt_of_le_of_lt (crit43_le hA30 hA3 hA40 hA4 (C2p_nonneg (by linarith) hR0 hC00 hl1)
    (hC.trans hmax) hc10 hc1) ?_
  rw [sqrt_lt' (by norm_num)]; norm_num

/-- **Lever 3, the major arc range.** With C₁ = 6.7814 and c₁ = 0.7894009, any
log P / log N ≥ 0.482 gives (23) at K = 7. -/
theorem k7_of_lp {A3 A4 R0 C0 ε lp c1 : ℝ}
    (hA30 : 0 ≤ A3) (hA3 : A3 ≤ 0.013598) (hA40 : 0 ≤ A4) (hA4 : A4 ≤ 0.003992)
    (hR0 : 0 ≤ R0) (hR : R0 ≤ 1.93656) (hC00 : 0 ≤ C0) (hC0 : C0 ≤ 0.66017)
    (he0 : 0 ≤ ε) (he : ε ≤ 1e-6) (hl : 0.482 ≤ lp) (hl1 : lp ≤ 1)
    (hc10 : 0 ≤ c1) (hc1 : c1 ≤ 0.7894009) :
    crit A4 A3 (C2p 6.7814 ε R0 C0 lp) c1 4 3 < 1 := by
  have hC := C2p_le (C1 := 6.7814) (C1m := 6.7814) (εm := 1e-6) (R0m := 1.93656)
    (C0m := 0.66017) (lpm := 0.482) le_rfl he (by linarith) hR0 hR hC00 hC0 hl
  have hmax : C2p 6.7814 1e-6 1.93656 0.66017 0.482 ≤ 3.23594 := by
    unfold C2p; have := log_two_lt_d9; norm_num at this ⊢; linarith
  refine lt_of_le_of_lt (crit43_le hA30 hA3 hA40 hA4 (C2p_nonneg (by linarith) hR0 hC00 hl1)
    (hC.trans hmax) hc10 hc1) ?_
  rw [sqrt_lt' (by norm_num)]; norm_num

/-- **Lever 2 at the MPR value**, c₁ = 0.77779 as JT derive from the announced
Maynard-Pandey-Radziwiłł minor arc exponent 19/24: the left side of (23) at K = 7 is below
0.935, with C₀ the twin prime constant through the proved `twinC_le_06614`. -/
theorem k7_MPR {A3 A4 R0 ε lp c1 : ℝ}
    (hA30 : 0 ≤ A3) (hA3 : A3 ≤ 0.013598) (hA40 : 0 ≤ A4) (hA4 : A4 ≤ 0.003992)
    (hR0 : 0 ≤ R0) (hR : R0 ≤ 1.93656) (he0 : 0 ≤ ε) (he : ε ≤ 1e-4) (hl : 0.444 ≤ lp)
    (hl1 : lp ≤ 1) (hc10 : 0 ≤ c1) (hc1 : c1 ≤ 0.77779) :
    crit A4 A3 (C2p 6.7814 ε R0 LeanLab.ChenExplicit.twinC lp) c1 4 3 < 0.935 := by
  have hC0 : LeanLab.ChenExplicit.twinC ≤ 0.6614 := by
    have := LeanLab.ChenExplicit.twinC_le_06614; norm_num at this ⊢; linarith
  have hC00 := LeanLab.ChenExplicit.twinC_pos.le
  have hC := C2p_le (C1 := 6.7814) (C1m := 6.7814) (εm := 1e-4) (R0m := 1.93656)
    (C0m := 0.6614) (lpm := 0.444) le_rfl he (by linarith) hR0 hR hC00 hC0 hl
  have hmax : C2p 6.7814 1e-4 1.93656 0.6614 0.444 ≤ 3.25487 := by
    unfold C2p; have := log_two_lt_d9; norm_num at this ⊢; linarith
  refine lt_of_le_of_lt (crit43_le hA30 hA3 hA40 hA4 (C2p_nonneg (by linarith) hR0 hC00 hl1)
    (hC.trans hmax) hc10 hc1) ?_
  rw [sqrt_lt' (by norm_num)]; norm_num

/-- Vacuity check: the printed inputs themselves satisfy every hypothesis of `k7_of_lp`
except the range, at lp = 1/2, the GRH range; so the hypotheses can hold. -/
example : crit 0.003992 0.013598 (C2p 6.7814 0 1.93656 0.66017 (1 / 2)) 0.7894009 4 3 < 1 :=
  k7_of_lp (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num) le_rfl
    le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl

#print axioms k7_of_C1
#print axioms k7_of_c1
#print axioms k7_of_lp
#print axioms k7_MPR

end LeanLab.Linnik.JT
