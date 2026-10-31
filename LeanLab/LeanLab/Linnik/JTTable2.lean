/-
P0025 Johnston, Trudgian 2026, arXiv 2605.17825 v2, read in Claude in Chrome at
arxiv.org/html/2605.17825v2 by run 20261018T2303Z-8776: Theorem 3's numeric step and Table 2.
AI-written Lean code, Claude. Checked only by the Lean kernel. Goldbach is open.

* Theorem 3: under Elliott-Halberstam, Proposition 3 gives C₁ = 4, and then (23) holds for
  K = 4 = 2 + 2 in the unconditional setup, c₁ = 0.7894009 and P = N^{4/9-ε}. PROVED below as
  `thm3_numeric`, CONDITIONAL on nothing but the cited inputs A(2), R₀, C₀ as hypotheses; the
  analytic content, Theorem 2 and Proposition 3, stays cited.
* Table 2, Pintz's method, Section 4.1: with D = C₀ C₁ R₀ / log 2 + 1 the bound of Pintz's
  Lemma 3 is d̄ ≥ (⌈D⌉ + ⌊D⌋ - D)/(⌈D⌉⌊D⌋ log 2). Each printed row is PROVED to follow from its C₁
  for every C₀ ∈ [0.66, 0.6601619], R₀ ∈ [1.936, 1.93656] and ε ∈ [0, 10⁻⁷]. Reading note: the
  page shows C̃ = (C₀ (C₁+ε) R₀ / log 2 + 1)/log 2, the reading every row confirms.
-/
import LeanLab.Linnik.JTNumeric

open Real

noncomputable section
namespace LeanLab.Linnik.JT

/-- **Theorem 3, numeric step**: K = 4 = 2 + 2 with C₁ = 4 unconditionally, c₁ = 0.7894009:
the left side of (23) is below 0.976 for A(2) ≤ 0.05549, R₀ ≤ 1.93656, C₀ ≤ 0.6614,
ε ≤ 10⁻³ and log P / log N ≥ 0.44. -/
theorem thm3_numeric {A2 R0 C0 ε lp : ℝ} (hA0 : 0 ≤ A2) (hA : A2 ≤ 0.05549)
    (hR0 : 0 ≤ R0) (hR : R0 ≤ 1.93656) (hC00 : 0 ≤ C0) (hC0 : C0 ≤ 0.6614)
    (he0 : 0 ≤ ε) (he : ε ≤ 1e-3) (hl : 0.44 ≤ lp) (hl1 : lp ≤ 1) :
    crit A2 A2 (C2p 4 ε R0 C0 lp) 0.7894009 2 2 < 0.976 := by
  have hC := C2p_le (C1 := 4) (C1m := 4) (εm := 1e-3) (R0m := 1.93656) (C0m := 0.6614)
    (lpm := 0.44) le_rfl he (by linarith) hR0 hR hC00 hC0 hl
  have hC2 : 0 ≤ C2p 4 ε R0 C0 lp := by
    unfold C2p
    have : 0 ≤ (1 - lp) * log 2 / 2 := by
      have := log_pos (show (1 : ℝ) < 2 by norm_num); nlinarith
    have h1 : 0 ≤ 1 / 2 * (4 + ε - 2) := by linarith
    have : 0 ≤ 1 / 2 * (4 + ε - 2) * R0 * C0 := mul_nonneg (mul_nonneg h1 hR0) hC00
    linarith
  have hmax : C2p 4 1e-3 1.93656 0.6614 0.44 ≤ 1.4757 := by
    unfold C2p; have := log_two_lt_d9; norm_num at this ⊢; linarith
  unfold crit
  have hx : 0 ≤ A2 + C2p 4 ε R0 C0 lp * 0.7894009 ^ (2 * 2 - 2) := by positivity
  rw [← sqrt_mul hx, sqrt_mul_self hx]
  norm_num
  have : C2p 4 ε R0 C0 lp * 0.7894009 ^ 2 ≤ 1.4757 * 0.7894009 ^ 2 :=
    mul_le_mul_of_nonneg_right (hC.trans hmax) (by positivity)
  norm_num at this ⊢
  linarith

/-- `D = C₀ (C₁ + ε) R₀ / log 2 + 1`, Section 4.1. -/
def Dp (C0 C1 ε R0 : ℝ) : ℝ := C0 * (C1 + ε) * R0 / log 2 + 1

/-- Pintz's Lemma 3 bound with `⌊D⌋ = f`, `⌈D⌉ = f + 1`, divided by `log 2`. -/
def pintzVal (D : ℝ) (f : ℕ) : ℝ := (2 * f + 1 - D) / (f * (f + 1) * log 2)

lemma Dp_bounds {C0 C1 ε R0 : ℝ} (hC1 : 0 ≤ C1) (hC0l : 0.66 ≤ C0) (hC0 : C0 ≤ 0.6601619)
    (hRl : 1.936 ≤ R0) (hR : R0 ≤ 1.93656) (he0 : 0 ≤ ε) (he : ε ≤ 1e-7) :
    0.66 * C1 * 1.936 / 0.6931471808 + 1 ≤ Dp C0 C1 ε R0 ∧
      Dp C0 C1 ε R0 ≤ 0.6601619 * (C1 + 1e-7) * 1.93656 / 0.6931471803 + 1 := by
  have l1 := log_two_gt_d9
  have l2 := log_two_lt_d9
  have hL : 0 < log 2 := by linarith
  unfold Dp
  constructor
  · have a : 0.66 * C1 * 1.936 ≤ C0 * (C1 + ε) * R0 := by
      have := mul_le_mul (mul_le_mul hC0l (by linarith : C1 ≤ C1 + ε) hC1 (by linarith)) hRl
        (by norm_num) (by positivity)
      linarith
    have b : 0.66 * C1 * 1.936 / 0.6931471808 ≤ 0.66 * C1 * 1.936 / log 2 :=
      div_le_div_of_nonneg_left (by positivity) hL l2.le
    have c : 0.66 * C1 * 1.936 / log 2 ≤ C0 * (C1 + ε) * R0 / log 2 :=
      div_le_div_of_nonneg_right a hL.le
    linarith
  · have a : C0 * (C1 + ε) * R0 ≤ 0.6601619 * (C1 + 1e-7) * 1.93656 := by
      have := mul_le_mul (mul_le_mul hC0 (by linarith : C1 + ε ≤ C1 + 1e-7) (by linarith)
        (by norm_num)) hR (by linarith) (by positivity)
      linarith
    have b : C0 * (C1 + ε) * R0 / log 2 ≤ 0.6601619 * (C1 + 1e-7) * 1.93656 / log 2 :=
      div_le_div_of_nonneg_right a hL.le
    have c : 0.6601619 * (C1 + 1e-7) * 1.93656 / log 2 ≤
        0.6601619 * (C1 + 1e-7) * 1.93656 / 0.6931471803 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) l1.le
    linarith

/-- A Table 2 row from its numeric checks. -/
lemma row_of {C0 C1 ε R0 d : ℝ} {f : ℕ} (hd : 0 ≤ d) (hf : 1 ≤ f) (hC1 : 0 ≤ C1) (hC0l : 0.66 ≤ C0)
    (hC0 : C0 ≤ 0.6601619) (hRl : 1.936 ≤ R0) (hR : R0 ≤ 1.93656) (he0 : 0 ≤ ε)
    (he : ε ≤ 1e-7)
    (h1 : (f : ℝ) ≤ 0.66 * C1 * 1.936 / 0.6931471808 + 1)
    (h2 : 0.6601619 * (C1 + 1e-7) * 1.93656 / 0.6931471803 + 1 ≤ f + 1)
    (h3 : d * (f * (f + 1) * 0.6931471808) ≤
      2 * f + 1 - (0.6601619 * (C1 + 1e-7) * 1.93656 / 0.6931471803 + 1)) :
    (f : ℝ) ≤ Dp C0 C1 ε R0 ∧ Dp C0 C1 ε R0 ≤ f + 1 ∧ d ≤ pintzVal (Dp C0 C1 ε R0) f := by
  obtain ⟨a, b⟩ := Dp_bounds hC1 hC0l hC0 hRl hR he0 he
  refine ⟨h1.trans a, b.trans h2, ?_⟩
  unfold pintzVal
  have l2 := log_two_lt_d9
  have hL : 0 < log 2 := log_pos (by norm_num)
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hden : 0 < (f : ℝ) * (f + 1) * log 2 := by positivity
  rw [le_div_iff₀ hden]
  have : d * ((f : ℝ) * (f + 1) * log 2) ≤ d * (f * (f + 1) * 0.6931471808) := by
    apply mul_le_mul_of_nonneg_left _ hd
    apply mul_le_mul_of_nonneg_left l2.le (by positivity)
  linarith

/-- **Table 2**, every printed row, `C₁ ↦ d̄`: 8 ↦ 0.09163, 7.8209 ↦ 0.09362,
6.7814 ↦ 0.10695, 6.71 ↦ 0.10799, 4 ↦ 0.17277, 2 ↦ 0.31098. -/
theorem table2 {C0 ε R0 : ℝ} (hC0l : 0.66 ≤ C0) (hC0 : C0 ≤ 0.6601619) (hRl : 1.936 ≤ R0)
    (hR : R0 ≤ 1.93656) (he0 : 0 ≤ ε) (he : ε ≤ 1e-7) :
    0.09163 ≤ pintzVal (Dp C0 8 ε R0) 15 ∧
    0.09362 ≤ pintzVal (Dp C0 7.8209 ε R0) 15 ∧
    0.10695 ≤ pintzVal (Dp C0 6.7814 ε R0) 13 ∧
    0.10799 ≤ pintzVal (Dp C0 6.71 ε R0) 13 ∧
    0.17277 ≤ pintzVal (Dp C0 4 ε R0) 8 ∧
    0.31098 ≤ pintzVal (Dp C0 2 ε R0) 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (row_of (by norm_num) (f := 15) (by norm_num) (by norm_num) hC0l hC0 hRl hR he0 he
      (by norm_num) (by norm_num) (by norm_num)).2.2
  · exact (row_of (by norm_num) (f := 15) (by norm_num) (by norm_num) hC0l hC0 hRl hR he0 he
      (by norm_num) (by norm_num) (by norm_num)).2.2
  · exact (row_of (by norm_num) (f := 13) (by norm_num) (by norm_num) hC0l hC0 hRl hR he0 he
      (by norm_num) (by norm_num) (by norm_num)).2.2
  · exact (row_of (by norm_num) (f := 13) (by norm_num) (by norm_num) hC0l hC0 hRl hR he0 he
      (by norm_num) (by norm_num) (by norm_num)).2.2
  · exact (row_of (by norm_num) (f := 8) (by norm_num) (by norm_num) hC0l hC0 hRl hR he0 he
      (by norm_num) (by norm_num) (by norm_num)).2.2
  · exact (row_of (by norm_num) (f := 4) (by norm_num) (by norm_num) hC0l hC0 hRl hR he0 he
      (by norm_num) (by norm_num) (by norm_num)).2.2

end LeanLab.Linnik.JT
