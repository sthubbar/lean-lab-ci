/-
P0069 Baker, Harman, Pintz 1997, Section 3, the proof of Theorem 4, pages 12 to 15, read from
the page images papers/P0069-original.pdf. Unit U-5050, CLOUD 20261019T0213Z-cloud14.

Every power in the proof is `X^e`, so the proof is linear arithmetic in the exponents, measured
in units of `log X`: `k = 1 - θ` for `qT = X^{1-θ}`, `m = α₁`, `n = α₂`, `l = 1 - m - n` for
`L`, and `s` for `log_X |S|`. The large values inputs (3.10) to (3.12) read `s ≤ max(...)`;
the target (3.9) reads exponent `< 1/2`, the `ℒ^{-A}` saving coming either from a power of `X`
or from (3.2). This file checks those exponent steps.

PROVED here: (3.13); the dominance rule `M^{c(σ)} ≥ qT`; Cases 1, 2 (i), 2 (ii), 3 (i) and the
two terms of Case 3 (ii) for `g ≥ 2`; `d(0) = 2θ - 1`, `d` increasing, `d(g) → θ`; the range
`d(0) < α₁ < θ - ε/2` from (3.6), (3.7); the equivalences behind (3.15) and (3.16).
FOUND, cosmetic, the main result survives:
* `printed_sign_false`: the line after (3.15) prints `(1 - (2g-2)θ)/(2g-1) - α₁`; at θ = 0.55,
  g = 2, α₁ = 0.41 > d(1) it is false. With `1 + (2g-2)θ` it follows from α₁ > d(g-1),
  `corrected_sign`.
* `g1_printed_false`: at g = 1 the first term's weight on the `N` bound is `1/2 - 1/(2g) = 0`,
  outside the range `[1/6, 1/2]` of (3.13), and the printed `N^{1/(4g)} = N^{1/4}` fails for an
  admissible point with σ₂ = 0.76. `g1_repair`: the exponent is still below 1/2 by a power of
  `X`, since Case 3 gives `N^{4σ₂-2} < qT` and (3.6), (3.7) give `α₂ > (1-θ)/2` when g = 1.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Thm4

/-- `f(σ) = min(1 - 2σ, 4 - 6σ)`, page 13. -/
noncomputable def f (σ : ℝ) : ℝ := min (1 - 2 * σ) (4 - 6 * σ)

/-- `c(σ) = 1` for `σ ≤ 3/4`, `4σ - 2` for `σ > 3/4`, page 13. -/
noncomputable def c (σ : ℝ) : ℝ := if σ ≤ 3 / 4 then 1 else 4 * σ - 2

/-- `γ(θ) = min(4θ - 2, (20θ - 9)/11, (72θ - 37)/11)`, (3.8). -/
noncomputable def gam (θ : ℝ) : ℝ := min (4 * θ - 2) (min ((20 * θ - 9) / 11) ((72 * θ - 37) / 11))

/-- `d(g) = 2θ - (1 + 2gθ)/(2g + 1)`, Case 3 (ii), page 14. -/
noncomputable def d (θ g : ℝ) : ℝ := 2 * θ - (1 + 2 * g * θ) / (2 * g + 1)

lemma gam_le_one (θ : ℝ) : gam θ ≤ 4 * θ - 2 := min_le_left _ _
lemma gam_le_two (θ : ℝ) : gam θ ≤ (20 * θ - 9) / 11 :=
  le_trans (min_le_right _ _) (min_le_left _ _)
lemma gam_le_three (θ : ℝ) : gam θ ≤ (72 * θ - 37) / 11 :=
  le_trans (min_le_right _ _) (min_le_right _ _)

lemma f_le_one (σ : ℝ) : f σ ≤ 1 - 2 * σ := min_le_left _ _
lemma f_le_two (σ : ℝ) : f σ ≤ 4 - 6 * σ := min_le_right _ _

/-- (3.13): for `α ∈ [1/6, 1/2]` and every real `σ`, `α f(σ) + σ - 1/2 ≤ (1 - 2α)/4`. -/
theorem eq313 {α : ℝ} (h1 : 1 / 6 ≤ α) (h2 : α ≤ 1 / 2) (σ : ℝ) :
    α * f σ + σ - 1 / 2 ≤ (1 - 2 * α) / 4 := by
  rcases le_or_gt σ (3 / 4) with hσ | hσ
  · have := mul_le_mul_of_nonneg_left (f_le_one σ) (by linarith : (0 : ℝ) ≤ α)
    nlinarith
  · have := mul_le_mul_of_nonneg_left (f_le_two σ) (by linarith : (0 : ℝ) ≤ α)
    nlinarith

/-- `f(3/4) = -1/2`, so the bound in (3.13) is attained at `σ = 3/4`. -/
theorem f_three_quarters : f (3 / 4) = -1 / 2 := by
  unfold f; norm_num

/-- `2 - 2σ - f(σ) = c(σ)`: the first term of (3.11) dominates, `M^{2-2σ} ≥ qT M^{f(σ)}`,
exactly when `M^{c(σ)} ≥ qT`, page 13. In exponents, for `m > 0`. -/
theorem two_sub_f (σ : ℝ) : 2 - 2 * σ - f σ = c σ := by
  unfold f c
  split_ifs with h
  · rw [min_eq_left (by linarith)]; ring
  · rw [min_eq_right (by linarith)]; ring

theorem dominance {m k σ : ℝ} : k + m * f σ ≤ m * (2 - 2 * σ) ↔ k ≤ m * c σ := by
  rw [← two_sub_f]; constructor <;> intro h <;> nlinarith

/-- Interpolation in exponents: from `s ≤ a`, `s ≤ b`, `s ≤ e` and weights summing to 1,
`s ≤ w₁ a + w₂ b + w₃ e`. This is `|S| ≤ A^{w₁} B^{w₂} E^{w₃}`. -/
theorem interp {s a b e w₁ w₂ w₃ : ℝ} (ha : s ≤ a) (hb : s ≤ b) (he : s ≤ e)
    (h1 : 0 ≤ w₁) (h2 : 0 ≤ w₂) (h3 : 0 ≤ w₃) (hw : w₁ + w₂ + w₃ = 1) :
    s ≤ w₁ * a + w₂ * b + w₃ * e := by
  have hs : s = w₁ * s + w₂ * s + w₃ * s := by rw [← add_mul, ← add_mul, hw, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left ha h1, mul_le_mul_of_nonneg_left hb h2,
    mul_le_mul_of_nonneg_left he h3]

/-! ### Case 1, page 13 -/

/-- Case 1: `(M^{2-2σ₁} N^{2-2σ₂})^{1/2} M^{σ₁-1/2} N^{σ₂-1/2} = M^{1/2} N^{1/2}`. With
`‖L‖_∞ ≪ L^{1/2} ℒ^{-A}` from (3.2) this is `X^{1/2} ℒ^{-A}`, since `MNL = X`. -/
theorem case1 (m n σ₁ σ₂ : ℝ) :
    (m * (2 - 2 * σ₁) + n * (2 - 2 * σ₂)) / 2 + m * (σ₁ - 1 / 2) + n * (σ₂ - 1 / 2) =
      m / 2 + n / 2 := by ring

/-! ### Case 2, page 13 -/

/-- Case 2 (i), the bound: `(qT M^{f(σ₁)} · qT N^{f(σ₂)})^{1/2} M^{σ₁-1/2} N^{σ₂-1/2} L^{σ₃-1/2}`
is at most `qT L^{1/4}` when `σ₃ ≤ 3/4`. -/
theorem case2i_bound {k m n l σ₁ σ₂ σ₃ : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hl : 0 ≤ l)
    (h3 : σ₃ ≤ 3 / 4) :
    (k + m * f σ₁ + (k + n * f σ₂)) / 2 + m * (σ₁ - 1 / 2) + n * (σ₂ - 1 / 2) +
      l * (σ₃ - 1 / 2) ≤ k + l / 4 := by
  have e1 := mul_le_mul_of_nonneg_left (f_le_one σ₁) hm
  have e2 := mul_le_mul_of_nonneg_left (f_le_one σ₂) hn
  have e3 := mul_le_mul_of_nonneg_left h3 hl
  nlinarith

/-- Case 2 (i), the conclusion: `L ≪ X² (qT)^{-4}` from (3.7), as `γ(θ) ≤ 4θ - 2`, gives
`qT L^{1/4} ≪ X^{1/2}` by a power of `X`. -/
theorem case2i_final {θ ε l : ℝ} (hε : 0 < ε) (hl : l < gam θ - ε) :
    (1 - θ) + l / 4 < 1 / 2 := by
  have := gam_le_one θ; linarith

/-- Case 2 (ii), first term with `g = 3`, weights `5/12, 5/12, 1/6`: the exponent is at most
`(5/6)(1-θ) + (m+n)/24 + l/2`, by (3.13) at `α = 5/12`. -/
theorem case2ii_I1 (k m n l σ₁ σ₂ σ₃ : ℝ) (hm : 0 ≤ m) (hn : 0 ≤ n) :
    5 / 12 * (k + m * f σ₁) + 5 / 12 * (k + n * f σ₂) + 1 / 6 * (3 * l * (2 - 2 * σ₃)) +
      m * (σ₁ - 1 / 2) + n * (σ₂ - 1 / 2) + l * (σ₃ - 1 / 2) ≤
      5 / 6 * k + (m + n) / 24 + l / 2 := by
  have h1 := mul_le_mul_of_nonneg_left (eq313 (α := 5 / 12) (by norm_num) (by norm_num) σ₁) hm
  have h2 := mul_le_mul_of_nonneg_left (eq313 (α := 5 / 12) (by norm_num) (by norm_num) σ₂) hn
  nlinarith

/-- Case 2 (ii), second term, weights `17/36, 17/36, 1/18`, using `(L³)^{4-6σ₃}`: the exponent is
at most `(1-θ) + (m+n)/72 + l/6`, by (3.13) at `α = 17/36`. -/
theorem case2ii_I2 (k m n l σ₁ σ₂ σ₃ : ℝ) (hm : 0 ≤ m) (hn : 0 ≤ n) :
    17 / 36 * (k + m * f σ₁) + 17 / 36 * (k + n * f σ₂) + 1 / 18 * (k + 3 * l * (4 - 6 * σ₃)) +
      m * (σ₁ - 1 / 2) + n * (σ₂ - 1 / 2) + l * (σ₃ - 1 / 2) ≤
      k + (m + n) / 72 + l / 6 := by
  have h1 := mul_le_mul_of_nonneg_left (eq313 (α := 17 / 36) (by norm_num) (by norm_num) σ₁) hm
  have h2 := mul_le_mul_of_nonneg_left (eq313 (α := 17 / 36) (by norm_num) (by norm_num) σ₂) hn
  nlinarith

/-- Case 2 (ii): `I₁ ≪ (qT)^{5/6} (X/L)^{1/24} L^{1/2} ≪ X^{1/2}` since `L ≪ X^{(20θ-9)/11 - ε}`. -/
theorem case2ii_I1_final {θ ε l : ℝ} (hε : 0 < ε) (hl : l < gam θ - ε) :
    5 / 6 * (1 - θ) + (1 - l) / 24 + l / 2 < 1 / 2 := by
  have := gam_le_two θ; linarith

/-- Case 2 (ii): `I₂ ≪ qT (X/L)^{1/72} L^{1/6} ≪ X^{1/2}` since `L ≪ X^{(72θ-37)/11 - ε}`. -/
theorem case2ii_I2_final {θ ε l : ℝ} (hε : 0 < ε) (hl : l < gam θ - ε) :
    (1 - θ) + (1 - l) / 72 + l / 6 < 1 / 2 := by
  have := gam_le_three θ; linarith

/-! ### Case 3 (i), page 14 -/

/-- Case 3 (i), the bound: `M^{(2-2σ₁)/2} (qT N^{f(σ₂)})^{1/2} M^{σ₁-1/2} N^{σ₂-1/2} L^{σ₃-1/2}`
is at most `M^{1/2} (qT)^{1/2} L^{1/4}` when `σ₃ ≤ 3/4`. -/
theorem case3i_bound {k m n l σ₁ σ₂ σ₃ : ℝ} (hn : 0 ≤ n) (hl : 0 ≤ l) (h3 : σ₃ ≤ 3 / 4) :
    m * (2 - 2 * σ₁) / 2 + (k + n * f σ₂) / 2 + m * (σ₁ - 1 / 2) + n * (σ₂ - 1 / 2) +
      l * (σ₃ - 1 / 2) ≤ m / 2 + k / 2 + l / 4 := by
  have e2 := mul_le_mul_of_nonneg_left (f_le_one σ₂) hn
  have e3 := mul_le_mul_of_nonneg_left h3 hl
  nlinarith

/-- (3.14) from (3.6): `L ≪ X^{2θ - 2α₁ - ε}`. -/
theorem eq314 {θ ε m n : ℝ} (h36 : |m - n| < 2 * θ - 1 - ε) :
    1 - m - n < 2 * θ - 2 * m - ε := by
  have := (abs_lt.mp h36).2; linarith

/-- Case 3 (i), the conclusion: `M^{1/2} (qT)^{1/2} L^{1/4} ≪ X^{1/2}` by a power of `X`. -/
theorem case3i_final {θ ε m n : ℝ} (hε : 0 < ε) (h36 : |m - n| < 2 * θ - 1 - ε) :
    m / 2 + (1 - θ) / 2 + (1 - m - n) / 4 < 1 / 2 := by
  have := eq314 h36; linarith

/-! ### Case 3 (ii), page 14 -/

theorem d_zero (θ : ℝ) : d θ 0 = 2 * θ - 1 := by unfold d; norm_num

/-- `d(g) = (2(g+1)θ - 1)/(2g+1)`. -/
theorem d_eq (θ g : ℝ) (hg : 0 ≤ g) : d θ g = (2 * (g + 1) * θ - 1) / (2 * g + 1) := by
  unfold d; field_simp; ring

/-- `d` is increasing in `g` for `θ < 1`. -/
theorem d_mono {θ g g' : ℝ} (hθ : θ < 1) (hg : 0 ≤ g) (hgg : g ≤ g') : d θ g ≤ d θ g' := by
  rw [d_eq θ g hg, d_eq θ g' (le_trans hg hgg), div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hgg (by linarith : (0 : ℝ) ≤ 1 - θ)]

/-- `θ - d(g) = (1 - θ)/(2g + 1)`, so `d(g) → θ` and `d(g₀) > θ - δ` once `2g₀ + 1 > (1-θ)/δ`. -/
theorem theta_sub_d (θ g : ℝ) (hg : 0 ≤ g) : θ - d θ g = (1 - θ) / (2 * g + 1) := by
  unfold d; field_simp; ring

theorem exists_d_gt {θ δ : ℝ} (hθ : θ < 1) (hδ : 0 < δ) : ∃ g₀ : ℕ, θ - δ < d θ g₀ := by
  obtain ⟨g₀, hg₀⟩ := exists_nat_gt ((1 - θ) / δ)
  refine ⟨g₀, ?_⟩
  have h0 : (0 : ℝ) ≤ g₀ := Nat.cast_nonneg _
  have := theta_sub_d θ g₀ h0
  have hlt : (1 - θ) / (2 * (g₀ : ℝ) + 1) < δ := by
    rw [div_lt_iff₀ (by linarith)]
    rw [div_lt_iff₀ hδ] at hg₀
    nlinarith
  linarith

/-- "It easily follows from (3.6), (3.7) that α₁ ∈ (d(0), d(g₀)]": in fact
`2θ - 1 < α₁ < θ - ε/2`, for `θ < 3/5` and `L ≥ 1`. -/
theorem alpha1_range {θ ε m n : ℝ} (hε : 0 < ε) (hθ : θ < 3 / 5)
    (h36 : |m - n| < 2 * θ - 1 - ε) (h37 : 1 - (m + n) < gam θ - ε) (hl : 0 ≤ 1 - m - n) :
    d θ 0 < m ∧ m < θ - ε / 2 := by
  rw [d_zero]
  have h1 := (abs_lt.mp h36).1
  have h2 := (abs_lt.mp h36).2
  have := gam_le_one θ
  constructor <;> linarith

/-- Some `g` with `1 ≤ g ≤ g₀` has `d(g - 1) < α₁ ≤ d(g)`. -/
theorem exists_g {θ m : ℝ} (g₀ : ℕ) (h0 : d θ 0 < m) (hg₀ : m ≤ d θ g₀) :
    ∃ g : ℕ, 1 ≤ g ∧ g ≤ g₀ ∧ d θ ((g : ℝ) - 1) < m ∧ m ≤ d θ g := by
  classical
  have hex : ∃ g : ℕ, m ≤ d θ g := ⟨g₀, hg₀⟩
  let g := Nat.find hex
  have hg : m ≤ d θ g := Nat.find_spec hex
  have hgle : g ≤ g₀ := Nat.find_min' hex hg₀
  have hg1 : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · exfalso; rw [h] at hg; push_cast at hg; linarith
    · exact h
  refine ⟨g, hg1, hgle, ?_, hg⟩
  have hmin := Nat.find_min hex (show g - 1 < g by omega)
  push_neg at hmin
  have : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by rw [Nat.cast_sub hg1]; simp
  rw [this] at hmin
  exact hmin

/-- Case 3 (ii), first term, `g ≥ 2`, weights `1/2, 1/2 - 1/(2g), 1/(2g)`: the exponent is at most
`m/2 + l/2 + (1/2 - 1/(2g))(1-θ) + n/(4g)`, by (3.13) at `α = 1/2 - 1/(2g) ∈ [1/4, 1/2)`. -/
theorem case3ii_T1 {g : ℝ} (hg : 2 ≤ g) (k m n l σ₁ σ₂ σ₃ : ℝ) (hn : 0 ≤ n) :
    1 / 2 * (m * (2 - 2 * σ₁)) + (1 / 2 - 1 / (2 * g)) * (k + n * f σ₂) +
      1 / (2 * g) * (g * l * (2 - 2 * σ₃)) +
      m * (σ₁ - 1 / 2) + n * (σ₂ - 1 / 2) + l * (σ₃ - 1 / 2) ≤
      m / 2 + l / 2 + (1 / 2 - 1 / (2 * g)) * k + n / (4 * g) := by
  have hg0 : 0 < g := by linarith
  have e1 : 1 / (2 * g) * (g * l * (2 - 2 * σ₃)) = l * (1 - σ₃) := by field_simp
  have e2 : n / (4 * g) = n * (1 / (2 * g)) / 2 := by field_simp; ring
  have ht1 : 1 / (2 * g) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have ht0 : 0 < 1 / (2 * g) := by positivity
  rw [e1, e2]
  have h := mul_le_mul_of_nonneg_left
    (eq313 (α := 1 / 2 - 1 / (2 * g)) (by linarith) (by linarith) σ₂) hn
  nlinarith

/-- Case 3 (ii), second term, `g ≥ 1`, weights `1/2, 1/2 - 1/(6g), 1/(6g)`, using
`qT (L^g)^{4-6σ₃}`: the exponent is at most `m/2 + l/6 + (1-θ)/2 + n/(12g)`, by (3.13) at
`α = 1/2 - 1/(6g) ∈ [1/3, 1/2)`. -/
theorem case3ii_T2 {g : ℝ} (hg : 1 ≤ g) (k m n l σ₁ σ₂ σ₃ : ℝ) (hn : 0 ≤ n) :
    1 / 2 * (m * (2 - 2 * σ₁)) + (1 / 2 - 1 / (6 * g)) * (k + n * f σ₂) +
      1 / (6 * g) * (k + g * l * (4 - 6 * σ₃)) +
      m * (σ₁ - 1 / 2) + n * (σ₂ - 1 / 2) + l * (σ₃ - 1 / 2) ≤
      m / 2 + l / 6 + k / 2 + n / (12 * g) := by
  have hg0 : 0 < g := by linarith
  have e1 : 1 / (6 * g) * (k + g * l * (4 - 6 * σ₃)) =
      1 / (6 * g) * k + l * (4 - 6 * σ₃) / 6 := by field_simp
  have e2 : n / (12 * g) = n * (1 / (6 * g)) / 2 := by field_simp; ring
  have ht1 : 1 / (6 * g) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have ht0 : 0 < 1 / (6 * g) := by positivity
  rw [e1, e2]
  have h := mul_le_mul_of_nonneg_left
    (eq313 (α := 1 / 2 - 1 / (6 * g)) (by linarith) (by linarith) σ₂) hn
  nlinarith

/-- (3.15) is equivalent to `N ≫ (qT)^{(2g-2)/(2g-1)}`, in exponents, with `m + n + l = 1`. -/
theorem eq315_iff {g θ m n l : ℝ} (hg : 1 ≤ g) (hsum : m + n + l = 1) :
    m / 2 + l / 2 + (1 / 2 - 1 / (2 * g)) * (1 - θ) + n / (4 * g) < 1 / 2 ↔
      (2 * g - 2) * (1 - θ) < (2 * g - 1) * n := by
  have hg0 : 0 < g := by linarith
  have hl : l = 1 - m - n := by linarith
  subst hl
  have key : m / 2 + (1 - m - n) / 2 + (1 / 2 - 1 / (2 * g)) * (1 - θ) + n / (4 * g) - 1 / 2 =
      ((2 * g - 2) * (1 - θ) - (2 * g - 1) * n) / (4 * g) := by
    field_simp; ring
  rw [← sub_neg, key, div_lt_iff₀ (by linarith), zero_mul, sub_neg]

/-- ... or to `L ≪ X^{(1 + (2g-2)θ)/(2g-1) - α₁}`. -/
theorem eq315_iff' {g θ m n l : ℝ} (hg : 1 ≤ g) (hsum : m + n + l = 1) :
    (2 * g - 2) * (1 - θ) < (2 * g - 1) * n ↔ l < (1 + (2 * g - 2) * θ) / (2 * g - 1) - m := by
  have h1 : 0 < 2 * g - 1 := by linarith
  rw [lt_sub_iff_add_lt, lt_div_iff₀ h1]
  have hn : n = 1 - m - l := by linarith
  subst hn
  constructor <;> intro h <;> nlinarith

/-- (3.16) is equivalent to `L ≪ X^{(6gθ - 1 - (6g-1)α₁)/(2g-1)}`, in exponents. -/
theorem eq316_iff {g θ m n l : ℝ} (hg : 1 ≤ g) (hsum : m + n + l = 1) :
    m / 2 + l / 6 + (1 - θ) / 2 + n / (12 * g) < 1 / 2 ↔
      l < (6 * g * θ - 1 - (6 * g - 1) * m) / (2 * g - 1) := by
  have hg0 : 0 < g := by linarith
  have h1 : 0 < 2 * g - 1 := by linarith
  have hn : n = 1 - m - l := by linarith
  subst hn
  have key : m / 2 + l / 6 + (1 - θ) / 2 + (1 - m - l) / (12 * g) - 1 / 2 =
      ((2 * g - 1) * l - (6 * g * θ - 1 - (6 * g - 1) * m)) / (12 * g) := by
    field_simp; ring
  rw [← sub_neg, key, div_lt_iff₀ (by linarith), zero_mul, sub_neg, lt_div_iff₀ h1]
  constructor <;> intro h <;> linarith

/-- Since `α₁ ≤ d(g)`, `2θ - 2α₁ ≤ (6gθ - 1 - (6g-1)α₁)/(2g-1)`, so (3.16) follows from (3.14). -/
theorem eq316_of_d {g θ m : ℝ} (hg : 1 ≤ g) (h : m ≤ d θ g) :
    2 * θ - 2 * m ≤ (6 * g * θ - 1 - (6 * g - 1) * m) / (2 * g - 1) := by
  have h1 : 0 < 2 * g - 1 := by linarith
  rw [d_eq θ g (by linarith), le_div_iff₀ (by linarith)] at h
  rw [le_div_iff₀ h1]
  nlinarith

/-- The corrected line after (3.15): since `α₁ > d(g-1)`,
`2θ - 2α₁ < (1 + (2g-2)θ)/(2g-1) - α₁`, so (3.15) follows from (3.14). -/
theorem corrected_sign {g θ m : ℝ} (h : d θ (g - 1) < m) :
    2 * θ - 2 * m < (1 + (2 * g - 2) * θ) / (2 * g - 1) - m := by
  unfold d at h
  have e : (1 + 2 * (g - 1) * θ) / (2 * (g - 1) + 1) = (1 + (2 * g - 2) * θ) / (2 * g - 1) := by
    ring_nf
  rw [e] at h
  linarith

/-- FINDING, cosmetic: the line as printed, `2θ - 2α₁ < (1 - (2g-2)θ)/(2g-1) - α₁`, is false at
θ = 0.55, g = 2, α₁ = 0.41, a point with `d(1) < α₁ ≤ d(2)` that (3.6) and (3.7) allow with
α₂ = 0.45, ε = 0.001. -/
theorem printed_sign_false :
    d 0.55 1 < 0.41 ∧ (0.41 : ℝ) ≤ d 0.55 2 ∧
      |(0.41 : ℝ) - 0.45| < 2 * 0.55 - 1 - 0.001 ∧ 1 - ((0.41 : ℝ) + 0.45) < gam 0.55 - 0.001 ∧
      ¬ (2 * 0.55 - 2 * 0.41 < (1 - (2 * 2 - 2) * 0.55) / (2 * 2 - 1) - (0.41 : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold d; norm_num
  · unfold d; norm_num
  · rw [abs_lt]; constructor <;> norm_num
  · have : gam 0.55 = (20 * 0.55 - 9) / 11 := by
      unfold gam; rw [min_eq_left (by norm_num : ((20 : ℝ) * 0.55 - 9) / 11 ≤ (72 * 0.55 - 37) / 11),
        min_eq_right (by norm_num)]
    rw [this]; norm_num
  · norm_num

/-- FINDING, cosmetic: at `g = 1` the first term of Case 3 (ii) has weight `1/2 - 1/(2g) = 0` on
the `N` bound, so its exponent is `m/2 + l/2 + n(σ₂ - 1/2)`, and the printed
`M^{1/2} L^{1/2} (qT)^0 N^{1/4}` is smaller at an admissible point: θ = 0.58, ε = 0.001,
α₁ = 0.43, α₂ = 0.40, σ₁ = 1, σ₂ = 0.76, σ₃ = 0.8. The point satisfies (3.6), (3.7), the Case 3
condition `M^{c(σ₁)} ≥ qT > N^{c(σ₂)}`, `σ₃ > 3/4` and `d(0) < α₁ ≤ d(1)`. -/
theorem g1_printed_false :
    let θ : ℝ := 0.58; let m : ℝ := 0.43; let n : ℝ := 0.4; let l : ℝ := 1 - m - n
    let σ₁ : ℝ := 1; let σ₂ : ℝ := 0.76; let σ₃ : ℝ := 0.8
    1 / 2 + 0.001 < θ ∧ θ < 7 / 12 ∧ |m - n| < 2 * θ - 1 - 0.001 ∧ 1 - (m + n) < gam θ - 0.001 ∧
      1 - θ ≤ m * c σ₁ ∧ n * c σ₂ < 1 - θ ∧ 3 / 4 < σ₃ ∧ d θ 0 < m ∧ m ≤ d θ 1 ∧
      m / 2 + l / 2 + n / 4 <
        1 / 2 * (m * (2 - 2 * σ₁)) + 0 * (1 - θ + n * f σ₂) + 1 / 2 * (1 * l * (2 - 2 * σ₃)) +
          m * (σ₁ - 1 / 2) + n * (σ₂ - 1 / 2) + l * (σ₃ - 1 / 2) := by
  intro θ m n l σ₁ σ₂ σ₃
  have hg : gam θ = (20 * θ - 9) / 11 := by
    unfold gam; rw [min_eq_left (by norm_num [θ] : ((20 : ℝ) * θ - 9) / 11 ≤ (72 * θ - 37) / 11),
      min_eq_right (by norm_num [θ])]
  have hc1 : c σ₁ = 4 * σ₁ - 2 := by unfold c; rw [if_neg (show ¬ σ₁ ≤ 3 / 4 by norm_num [σ₁])]
  have hc2 : c σ₂ = 4 * σ₂ - 2 := by unfold c; rw [if_neg (show ¬ σ₂ ≤ 3 / 4 by norm_num [σ₂])]
  refine ⟨by norm_num [θ], by norm_num [θ], ?_, ?_, ?_, ?_, by norm_num [σ₃], ?_, ?_, ?_⟩
  · rw [abs_lt]; constructor <;> norm_num [θ, m, n]
  · rw [hg]; norm_num [θ, m, n]
  · rw [hc1]; norm_num [θ, m, σ₁]
  · rw [hc2]; norm_num [θ, n, σ₂]
  · rw [d_zero]; norm_num [θ, m]
  · unfold d; norm_num [θ, m]
  · norm_num [θ, m, n, l, σ₁, σ₂, σ₃]

/-- REPAIR of the `g = 1` step: under (3.6), (3.7), `α₁ ≤ d(1)` and the Case 3 condition
`N^{c(σ₂)} < qT`, the `g = 1` first term still has exponent below 1/2 by the fixed margin
`min(α₂/4, α₂/2 - (1-θ)/4) > 0`, so (3.15) holds at `g = 1` and Theorem 4 survives. The key is
`α₂ > (10 - 16θ)/3 > (1-θ)/2`, which needs `θ < 17/29`, true as `θ < 7/12`. -/
theorem g1_repair {θ ε m n σ₂ : ℝ} (hε : 0 < ε) (hθ : θ < 7 / 12)
    (h37 : 1 - (m + n) < gam θ - ε) (hd : m ≤ d θ 1) (hc : n * c σ₂ < 1 - θ) :
    0 < min (n / 4) (n / 2 - (1 - θ) / 4) ∧
      m / 2 + (1 - m - n) / 2 + n * (σ₂ - 1 / 2) ≤ 1 / 2 - min (n / 4) (n / 2 - (1 - θ) / 4) := by
  have hg := gam_le_one θ
  have hd1 : d θ 1 = (4 * θ - 1) / 3 := by unfold d; ring
  rw [hd1] at hd
  have hn : (1 - θ) / 2 < n := by linarith
  have hn0 : 0 < n := by linarith
  refine ⟨lt_min (by linarith) (by linarith), ?_⟩
  unfold c at hc
  split_ifs at hc with h
  · have := min_le_left (n / 4) (n / 2 - (1 - θ) / 4)
    nlinarith
  · have := min_le_right (n / 4) (n / 2 - (1 - θ) / 4)
    nlinarith

end LeanLab.BHP1997.Thm4
