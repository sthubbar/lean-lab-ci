import Mathlib
import LeanLab.HelfgottMajor.BookT143

/-!
# Helfgott's book, Part IV of 2020-04-01, Theorem 14.3: falsifier check and repaired statement

Unit U-6721, CLOUD 20261020T1914Z-cloud49, P0014, independent falsifier of the two U-6719
QUESTION items. AI wrote this file.

Source: book pp. 377, 435, 444, 448 to 451 of papers/P0014-book-PartIV.pdf, page images read.

QA, p. 450: `(1.8019·10⁻¹⁸ + 3.9953·10⁻⁸⁶)·log(1.35·10⁸/2π) ≤ 1.802·10⁻¹⁸` is false.
`qa_gap` proves the product exceeds `1.81·10⁻¹⁸ = ε'₊` with an independent lower bound
`log(1.35·10⁸/2π) > 16` from `exp 16`; `qa_fix` proves `≤ 3.05·10⁻¹⁷` from `exp 16.9`.

QB, pp. 449 and 450: (16.60) carries `√T`, `T = T₀ + H`; the proofs use `√T₀`.
`qb_gap_p1`, `qb_gap_p2`: at `max(|δ|,4) = 4` the term `c√T + 22.5`, resp. `+ 22.3`, exceeds
the stated `78·2 + 23`, resp. `95·2 + 23`, with independent log lower bounds.
`qb_alt_p1`, `qb_alt_p2`: keeping the coefficients 78 and 95, the constant 23 becomes 68 and 99.
`thm143_p1_fixed`, `thm143_p2_fixed`: the last assembly step of each part with `√T`, in both
repaired forms, for `x ≥ 10⁶`, using `final_p1`, `final_p2`, `logq_p1`, `logq_p2` and the upper
bounds `logA_lt`, `logB_lt` of BookT143, and `kappa_fix_p1`, `kappa_fix_p2` for the `98`, `127.4`
forms.

Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN. AI-written Lean code, Claude,
2026-10-20.
-/

namespace LeanLab.HelfgottMajor.BookT143Fix
open Real
open LeanLab.HelfgottMajor.BookT143

/-- `exp 16 < 8.9·10⁶`, from `e < 2.7182818286`. -/
lemma exp16_lt : exp 16 < 8.9e6 := by
  have h := exp_one_lt_d9
  have h0 := exp_pos (1 : ℝ)
  have e : exp (16 : ℝ) = exp 1 ^ 16 := by rw [← exp_nat_mul]; norm_num
  rw [e]
  calc exp 1 ^ 16 < (2.7182818286 : ℝ) ^ 16 := pow_lt_pow_left₀ h h0.le (by norm_num)
    _ < 8.9e6 := by norm_num

/-- `exp 18 < 6.6·10⁷`. -/
lemma exp18_lt : exp 18 < 6.6e7 := by
  have h := exp_one_lt_d9
  have h0 := exp_pos (1 : ℝ)
  have e : exp (18 : ℝ) = exp 1 ^ 18 := by rw [← exp_nat_mul]; norm_num
  rw [e]
  calc exp 1 ^ 18 < (2.7182818286 : ℝ) ^ 18 := pow_lt_pow_left₀ h h0.le (by norm_num)
    _ < 6.6e7 := by norm_num

/-- `exp 16.9 > 2.18·10⁷`, from `e > 2.7182818283` and four Taylor terms of `exp 0.9`. -/
lemma exp169_gt : 2.18e7 < exp 16.9 := by
  have h := exp_one_gt_d9
  have e : exp (16.9 : ℝ) = exp 1 ^ 16 * exp 0.9 := by
    rw [← exp_nat_mul, ← exp_add]; norm_num
  have t : (1 + 0.9 + 0.9 ^ 2 / 2 + 0.9 ^ 3 / 6 + 0.9 ^ 4 / 24 : ℝ) ≤ exp 0.9 := by
    have := Real.sum_le_exp_of_nonneg (x := (0.9 : ℝ)) (by norm_num) 5
    simpa [Finset.sum_range_succ, Nat.factorial] using this
  have p : (2.7182818283 : ℝ) ^ 16 < exp 1 ^ 16 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  rw [e]
  have hp : (0 : ℝ) < 2.7182818283 ^ 16 := by norm_num
  calc (2.18e7 : ℝ) < 2.7182818283 ^ 16 * (1 + 0.9 + 0.9 ^ 2 / 2 + 0.9 ^ 3 / 6 + 0.9 ^ 4 / 24) := by
        norm_num
    _ ≤ exp 1 ^ 16 * exp 0.9 := by
        apply mul_le_mul p.le t (by norm_num) (by positivity)

/-- `16 < log(1.35·10⁸/2π) < 16.9`, independent of BookT143. -/
lemma LB_indep : 16 < log (1.35e8 / (2 * π)) ∧ log (1.35e8 / (2 * π)) < 16.9 := by
  have hp1 := pi_lt_d2; have hp0 := pi_gt_three
  have hpos : (0 : ℝ) < 1.35e8 / (2 * π) := by positivity
  constructor
  · rw [lt_log_iff_exp_lt hpos, lt_div_iff₀ (by positivity)]
    have := exp16_lt; nlinarith [exp_pos (16 : ℝ)]
  · rw [log_lt_iff_lt_exp hpos, div_lt_iff₀ (by positivity)]
    have := exp169_gt; have hp2 := pi_gt_d2; nlinarith [exp_pos (16.9 : ℝ)]

/-- **QA gap, p. 450**: the product with the factor `log(1.35·10⁸/2π)` exceeds `16·1.8019·10⁻¹⁸`,
so it exceeds both the printed `1.802·10⁻¹⁸` and the stated `ε'₊ = 1.81·10⁻¹⁸`. -/
theorem qa_gap :
    (2.88e-17 : ℝ) < (1.8019e-18 + 3.9953e-86) * log (1.35e8 / (2 * π)) ∧
    (1.81e-18 : ℝ) < (1.8019e-18 + 3.9953e-86) * log (1.35e8 / (2 * π)) := by
  have h := LB_indep.1
  have : (1.8019e-18 + 3.9953e-86 : ℝ) * 16 < (1.8019e-18 + 3.9953e-86) *
      log (1.35e8 / (2 * π)) := mul_lt_mul_of_pos_left h (by norm_num)
  constructor <;> norm_num at this ⊢ <;> linarith

/-- **QA repair**: `ε'₊ = 3.05·10⁻¹⁷` follows. -/
theorem qa_fix : (1.8019e-18 + 3.9953e-86) * log (1.35e8 / (2 * π)) ≤ 3.05e-17 := by
  have h := LB_indep.2
  have : (1.8019e-18 + 3.9953e-86 : ℝ) * log (1.35e8 / (2 * π)) <
      (1.8019e-18 + 3.9953e-86) * 16.9 := mul_lt_mul_of_pos_left h (by norm_num)
  norm_num at this ⊢; linarith

/-- `18 < log 108750000`, independent. -/
lemma logA_gt18 : 18 < log 108750000 := by
  rw [lt_log_iff_exp_lt (by norm_num)]; have := exp18_lt; linarith

lemma logB_gt18 : 18 < log 1.35e8 := by
  rw [lt_log_iff_exp_lt (by norm_num)]; have := exp18_lt; linarith

/-- **QB gap, part 1**: at `D = 4`, `T = (1375/32)·4 + 100`, the `√T` term of (16.60) plus the
`22.5` exceeds the stated `78√4 + 23`. -/
theorem qb_gap_p1 :
    (78 : ℝ) * √4 + 23 < (0.566 * log 108750000 + 1.41) * √(1375 / 32 * 4 + 100) + 22.5 := by
  have e4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
  have s : 16.4 < √(1375 / 32 * 4 + 100 : ℝ) := by rw [lt_sqrt (by norm_num)]; norm_num
  have := logA_gt18
  rw [e4]; nlinarith

/-- **QB gap, part 2**: at `D = 4`, `T = (125/2)·4 + 200`, against the stated `95√4 + 23`. -/
theorem qb_gap_p2 :
    (95 : ℝ) * √4 + 23 < (0.566 * log 1.35e8 + 1.41) * √(125 / 2 * 4 + 200) + 22.3 := by
  have e4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
  have s : 21.2 < √(125 / 2 * 4 + 200 : ℝ) := by rw [lt_sqrt (by norm_num)]; norm_num
  have := logB_gt18
  rw [e4]; nlinarith

/-- `√(kD + H) ≤ √k·√D + (H/4)/√k` when `D ≥ 4`, `k > 0`, `H ≥ 0`. -/
lemma sqrt_shift {k D H : ℝ} (hk : 0 < k) (hD : 4 ≤ D) (hH : 0 ≤ H) :
    √(k * D + H) ≤ √k * √D + H / 4 / √k := by
  have sk := sqrt_pos.2 hk
  have sD : 2 ≤ √D := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt hD
  have hkk : √k * √k = k := mul_self_sqrt hk.le
  have hDD : √D * √D = D := mul_self_sqrt (by linarith)
  have hR : 0 ≤ √k * √D + H / 4 / √k := by positivity
  rw [sqrt_le_left hR]
  have hc : H / 4 / √k * √k = H / 4 := by field_simp
  nlinarith [sq_nonneg (H / 4 / √k), mul_nonneg hH (by linarith : (0:ℝ) ≤ √D - 2)]

/-- **QB alternative repair, part 1**: keeping the coefficient 78, the constant 23 becomes 68:
`c₁√((1375/32)D + 100) + 22.5 ≤ 78√D + 68` for every `D ≥ 4`. -/
theorem qb_alt_p1 {D : ℝ} (hD : 4 ≤ D) :
    (0.566 * log 108750000 + 1.41) * √(1375 / 32 * D + 100) + 22.5 ≤ 78 * √D + 68 := by
  have h := sqrt_shift (k := 1375 / 32) (H := 100) (by norm_num) hD (by norm_num)
  have hl := logA_lt; have hl0 := logA_gt18
  have sk1 : √(1375 / 32 : ℝ) < 6.5552 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have sk2 : 6.555 < √(1375 / 32 : ℝ) := by rw [lt_sqrt (by norm_num)]; norm_num
  have hq : 100 / 4 / √(1375 / 32 : ℝ) ≤ 3.814 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have sD := sqrt_nonneg D
  have hc : 0 ≤ 0.566 * log 108750000 + 1.41 := by linarith
  have := mul_le_mul_of_nonneg_left h hc
  nlinarith [mul_nonneg sD hc]

/-- **QB alternative repair, part 2**: keeping 95, the constant 23 becomes 99. -/
theorem qb_alt_p2 {D : ℝ} (hD : 4 ≤ D) :
    (0.566 * log 1.35e8 + 1.41) * √(125 / 2 * D + 200) + 22.3 ≤ 95 * √D + 99 := by
  have h := sqrt_shift (k := 125 / 2) (H := 200) (by norm_num) hD (by norm_num)
  have hl := logB_lt; have hl0 := logB_gt18
  have sk1 : √(125 / 2 : ℝ) < 7.9057 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have sk2 : 7.9056 < √(125 / 2 : ℝ) := by rw [lt_sqrt (by norm_num)]; norm_num
  have hq : 200 / 4 / √(125 / 2 : ℝ) ≤ 6.3248 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have sD := sqrt_nonneg D
  have hc : 0 ≤ 0.566 * log 1.35e8 + 1.41 := by linarith
  have := mul_le_mul_of_nonneg_left h hc
  nlinarith [mul_nonneg sD hc]

/-- **Theorem 14.3 part 1, repaired assembly**: with `√T`, `T = (1375/32)D + 100`, the
`√x`, `x⁰` and `x^{-1/2}` lines of (16.60) are at most `(98√D + 23)√x + 2d` and at most
`(78√D + 68)√x + 2d`, for `x ≥ 10⁶`, `1 ≤ q ≤ 400000`, `d ≥ 0`, `D ≥ 4`. -/
theorem thm143_p1_fixed {x q d D : ℝ} (hx : 1e6 ≤ x) (hq1 : 1 ≤ q) (hq : q ≤ 400000)
    (hd : 0 ≤ d) (hD : 4 ≤ D) :
    let S := ((0.566 * log 108750000 + 1.41) * √(1375 / 32 * D + 100) +
      (0.84 * log q + 11.52)) * √x + (1.6 * d + 1.1) + 6.1 * log q * (6 + 2 * d) / √x
    S ≤ (98 * √D + 23) * √x + 2 * d ∧ S ≤ (78 * √D + 68) * √x + 2 * d := by
  intro S
  set A := (0.566 * log 108750000 + 1.41) * √(1375 / 32 * D + 100) with hA
  have hl := (logq_p1 hq1 hq).1
  have sx := sqrt_nonneg x
  have hS : S ≤ (A + 22.5) * √x + 2 * d := by
    have := final_p1 (A := A) hx hq1 hq hd
    have : (A + (0.84 * log q + 11.52)) * √x ≤ (A + 22.4) * √x :=
      mul_le_mul_of_nonneg_right (by linarith) sx
    simp only [S]; rw [← hA]; linarith
  have k1 := kappa_fix_p1 hD
  have k2 := qb_alt_p1 hD
  constructor
  · have : (A + 22.5) * √x ≤ (98 * √D + 23) * √x :=
      mul_le_mul_of_nonneg_right (by simp only [A] at *; linarith) sx
    linarith
  · have : (A + 22.5) * √x ≤ (78 * √D + 68) * √x :=
      mul_le_mul_of_nonneg_right (by simp only [A] at *; linarith) sx
    linarith

/-- **Theorem 14.3 part 2, repaired assembly**: with `T = (125/2)D + 200`, at most
`(127.4√D + 23)√x + 2d` and at most `(95√D + 99)√x + 2d`, for `1 ≤ q ≤ 300000`. -/
theorem thm143_p2_fixed {x q d D : ℝ} (hx : 1e6 ≤ x) (hq1 : 1 ≤ q) (hq : q ≤ 300000)
    (hd : 0 ≤ d) (hD : 4 ≤ D) :
    let S := ((0.566 * log 1.35e8 + 1.41) * √(125 / 2 * D + 200) +
      (0.84 * log q + 11.52)) * √x + (1.6 * d + 1.1) + 6.1 * log q * (6 + 2 * d) / √x
    S ≤ (127.4 * √D + 23) * √x + 2 * d ∧ S ≤ (95 * √D + 99) * √x + 2 * d := by
  intro S
  set A := (0.566 * log 1.35e8 + 1.41) * √(125 / 2 * D + 200) with hA
  have hl := (logq_p2 hq1 hq).1
  have sx := sqrt_nonneg x
  have hS : S ≤ (A + 22.3) * √x + 2 * d := by
    have := final_p2 (A := A) hx hq1 hq hd
    have : (A + (0.84 * log q + 11.52)) * √x ≤ (A + 22.2) * √x :=
      mul_le_mul_of_nonneg_right (by linarith) sx
    simp only [S]; rw [← hA]; linarith
  have k1 := kappa_fix_p2 hD
  have k2 := qb_alt_p2 hD
  constructor
  · have : (A + 22.3) * √x ≤ (127.4 * √D + 23) * √x :=
      mul_le_mul_of_nonneg_right (by simp only [A] at *; linarith) sx
    linarith
  · have : (A + 22.3) * √x ≤ (95 * √D + 99) * √x :=
      mul_le_mul_of_nonneg_right (by simp only [A] at *; linarith) sx
    linarith

end LeanLab.HelfgottMajor.BookT143Fix

#print axioms LeanLab.HelfgottMajor.BookT143Fix.qa_gap
#print axioms LeanLab.HelfgottMajor.BookT143Fix.qa_fix
#print axioms LeanLab.HelfgottMajor.BookT143Fix.qb_gap_p1
#print axioms LeanLab.HelfgottMajor.BookT143Fix.qb_gap_p2
#print axioms LeanLab.HelfgottMajor.BookT143Fix.qb_alt_p1
#print axioms LeanLab.HelfgottMajor.BookT143Fix.qb_alt_p2
#print axioms LeanLab.HelfgottMajor.BookT143Fix.thm143_p1_fixed
#print axioms LeanLab.HelfgottMajor.BookT143Fix.thm143_p2_fixed
