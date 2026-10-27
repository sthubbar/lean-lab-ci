/-
P0069 Baker, Harman, Pintz 1997, Lemma 3, pages 16 and 17, read from the page images
papers/P0069-original.pdf. Unit U-5063, CLOUD 20261019T0213Z-cloud14.

Exponents in units of `log X`, `qT ≤ X^{0.45}` from (3.23).
PROVED: the Hölder exponent sums of cases (i) to (iv) (a); every use of (3.27),
`N ≫ (qT)^{2/β₁}`, and of Lemma 2's `qT ≤ L^γ`, (3.18) and (3.19) in those cases;
`α₁ > 0.18` in Case (b); and (3.29) in full, `S ≥ c/(1.8 - 12c/7)` for every admissible
`α₁, α₂, α₃` with sum `c`, by a tangent line bound for the convex `a/(1.8 - ka)`, with the
minimum attained at `α₂ = α₃ = 2c/7`, value 1/2 at `c = 63/130`, and `S ≥ 1/2 + δ` for
`c ≥ 63/130 + δ`.
FINDING, cosmetic: case (i) prints `4β₂ = 8`, so β₂ = 2, and then `Σ 1/βⱼ = 7/8`, not the 1/2
that (3.25) needs; β₂ = 8 is meant, the β = 8 of Lemma 2 for `L` in the same case.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma3

/-- The Hölder sums: (i) as printed `β₂ = 8/4` fails, with `β₂ = 8` it is 1/2; (ii) 4, 12, 6;
(iii) 2, 6, 4, 12 summing to 1 with `‖M‖₂`; (iv) (a) 10, 4, 20/3. -/
theorem holder_sums :
    (1 / 8 + 1 / (8 / 4) + 1 / 4 : ℝ) ≠ 1 / 2 ∧ (1 / 8 + 1 / 8 + 1 / 4 : ℝ) = 1 / 2 ∧
    (1 / 4 + 1 / 12 + 1 / 6 : ℝ) = 1 / 2 ∧ (1 / 2 + 1 / 6 + 1 / 4 + 1 / 12 : ℝ) = 1 ∧
    (1 / 10 + 1 / 4 + 1 / (20 / 3) : ℝ) = 1 / 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- (3.27) thresholds `(qT)^{2/β}` with `qT = X^{0.45}`: β = 8, 4, 6, 10 give
0.1125, 0.225, 0.15, 0.09, matching the hypotheses of (i), (ii), (iii) and Case (a), where
`N > X^{0.1} > X^{0.09}`. -/
theorem thresholds :
    (0.45 : ℝ) * (2 / 8) = 0.1125 ∧ (0.45 : ℝ) * (2 / 4) = 0.225 ∧
    (0.45 : ℝ) * (2 / 6) = 0.15 ∧ (0.45 : ℝ) * (2 / 10) < 0.1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Lemma 2 in cases (i), (ii), (iii): `L^γ ≥ X^{0.45}` at the lower ends `9/70`, `0.1`, `0.18`
with γ = 7/2, 9/2, 5/2, minus ε; and (3.18) `β ≥ 4γ - 2h + ε` with γ = γ₀ - ε. -/
theorem lemma2_uses {ε : ℝ} (hε : 0 < ε) :
    (9 / 70 : ℝ) * (7 / 2) = 0.45 ∧ (0.1 : ℝ) * (9 / 2) = 0.45 ∧ (0.18 : ℝ) * (5 / 2) = 0.45 ∧
    4 * (7 / 2 - ε) - 2 * 3 + ε ≤ 8 ∧ 4 * (9 / 2 - ε) - 2 * 3 + ε ≤ 12 ∧
    4 * (5 / 2 - ε) - 2 * 2 + ε ≤ 6 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by linarith, by linarith, by linarith⟩

/-- Case (iv) (a): `γ = 0.45/(9/35 - 0.1125) = 28/9`, and β = 20/3 satisfies (3.18) with
h = 3 for ε < 2/9, and (3.19). -/
theorem case_iva {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 2 / 9) :
    (0.45 : ℝ) / (9 / 35 - 0.1125) = 28 / 9 ∧ 4 * (28 / 9 : ℝ) - 2 * 3 + ε ≤ 20 / 3 ∧
    2 * 3 - ε < (20 / 3 : ℝ) ∧ (20 / 3 : ℝ) < 6 * 3 - ε := by
  refine ⟨by norm_num, by linarith, by linarith, by linarith⟩

/-- Case (iv) (b): from `LNR ≫ X^{63/130}` and `N, R ≪ X^{0.15}`, `α₁ > 0.18`. -/
theorem case_ivb_alpha1 {a1 a2 a3 : ℝ} (h : 63 / 130 ≤ a1 + a2 + a3) (h2 : a2 < 0.15)
    (h3 : a3 < 0.15) : 0.18 < a1 := by linarith

/-- Tangent line bound for the convex `a/(1.8 - ka)` at the point where `1.8 - ka = D`. -/
theorem tangent {k a D : ℝ} (hk : 0 < k) (hy : 0 < 1.8 - k * a) (hD : 0 < D) :
    (1.8 - D) / k / D + 1.8 * (a - (1.8 - D) / k) / D ^ 2 ≤ a / (1.8 - k * a) := by
  set y := 1.8 - k * a with hy'
  have ha : a = (1.8 - y) / k := by rw [hy']; field_simp; ring
  rw [ha]
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : 0 ≤ (D - y) ^ 2 := sq_nonneg _
  field_simp
  ring_nf
  nlinarith [mul_nonneg (mul_nonneg hk.le hk.le) hsq, mul_pos hk hD, mul_pos hy hD,
    mul_nonneg (mul_nonneg (mul_nonneg hk.le hk.le) hsq) (sq_nonneg D),
    mul_nonneg (mul_nonneg (mul_nonneg hk.le hk.le) hsq) (mul_nonneg hy.le hD.le),
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hk.le hk.le) hsq) hy.le) (sq_nonneg D),
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hk.le hk.le) hk.le) hsq) (sq_nonneg D)]

/-- (3.29), the minimisation: `S = α₁/(1.8 - 4α₁) + α₂/(1.8 - 6α₂) + α₃/(1.8 - 6α₃)`, which is
the printed sum of `1/((1.8/αᵢ) - 4 or 6)`, is at least `c/(1.8 - 12c/7)`, `c = α₁ + α₂ + α₃`. -/
theorem S_ge {a1 a2 a3 : ℝ} (h1 : 0 < 1.8 - 4 * a1) (h2 : 0 < 1.8 - 6 * a2)
    (h3 : 0 < 1.8 - 6 * a3) (hD : 0 < 1.8 - 12 * (a1 + a2 + a3) / 7) :
    (a1 + a2 + a3) / (1.8 - 12 * (a1 + a2 + a3) / 7) ≤
      a1 / (1.8 - 4 * a1) + a2 / (1.8 - 6 * a2) + a3 / (1.8 - 6 * a3) := by
  set D := 1.8 - 12 * (a1 + a2 + a3) / 7 with hDdef
  have t1 := tangent (k := 4) (by norm_num) h1 hD
  have t2 := tangent (k := 6) (by norm_num) h2 hD
  have t3 := tangent (k := 6) (by norm_num) h3 hD
  have hsum : (1.8 - D) / 4 + (1.8 - D) / 6 + (1.8 - D) / 6 = a1 + a2 + a3 := by
    rw [hDdef]; ring
  have e : (1.8 - D) / 4 / D + 1.8 * (a1 - (1.8 - D) / 4) / D ^ 2 +
      ((1.8 - D) / 6 / D + 1.8 * (a2 - (1.8 - D) / 6) / D ^ 2) +
      ((1.8 - D) / 6 / D + 1.8 * (a3 - (1.8 - D) / 6) / D ^ 2) = (a1 + a2 + a3) / D := by
    have : a1 - (1.8 - D) / 4 + (a2 - (1.8 - D) / 6) + (a3 - (1.8 - D) / 6) = 0 := by
      linarith
    field_simp
    linear_combination (D * 1.8) * this + D ^ 2 * hsum
  linarith

/-- The minimum is attained at `α₂ = α₃ = 2c/7`, `α₁ = 3c/7`. -/
theorem S_attained (c : ℝ) (hc : 0 < 1.8 - 12 * c / 7) :
    3 * c / 7 / (1.8 - 4 * (3 * c / 7)) + 2 * (2 * c / 7 / (1.8 - 6 * (2 * c / 7))) =
      c / (1.8 - 12 * c / 7) := by
  have e1 : 1.8 - 4 * (3 * c / 7) = 1.8 - 12 * c / 7 := by ring
  have e2 : 1.8 - 6 * (2 * c / 7) = 1.8 - 12 * c / 7 := by ring
  rw [e1, e2]; field_simp; ring

/-- `c/(1.8 - 12c/7) = 1/2` at `c = 63/130`, and the minimiser lies in the region,
`0.18 < 3c/7 < 0.225` and `0.1 < 2c/7 < 0.15`. -/
theorem value_at_63_130 :
    (63 / 130 : ℝ) / (1.8 - 12 * (63 / 130) / 7) = 1 / 2 ∧
    (0.18 : ℝ) < 3 * (63 / 130) / 7 ∧ 3 * (63 / 130 : ℝ) / 7 < 0.225 ∧
    (0.1 : ℝ) < 2 * (63 / 130) / 7 ∧ 2 * (63 / 130 : ℝ) / 7 < 0.15 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- (3.29) with its margin: if `c ≥ 63/130 + δ`, `δ ≥ 0`, and `c < 1.05`, then
`c/(1.8 - 12c/7) ≥ 1/2 + δ`. -/
theorem margin {c δ : ℝ} (hδ : 0 ≤ δ) (hc : 63 / 130 + δ ≤ c) (hc1 : c < 1.05) :
    1 / 2 + δ ≤ c / (1.8 - 12 * c / 7) := by
  have hD : 0 < 1.8 - 12 * c / 7 := by linarith
  rw [le_div_iff₀ hD]
  nlinarith

/-- (3.29) assembled: on the region of Case (b) with `α₁ + α₂ + α₃ ≥ 63/130 + δ`,
`S ≥ 1/2 + δ`. -/
theorem eq329 {a1 a2 a3 δ : ℝ} (hδ : 0 ≤ δ) (h1 : 0.18 < a1) (h1' : a1 < 0.225)
    (h2 : 0.1 < a2) (h2' : a2 < 0.15) (h3 : 0.1 < a3) (h3' : a3 < 0.15)
    (hc : 63 / 130 + δ ≤ a1 + a2 + a3) :
    1 / 2 + δ ≤ a1 / (1.8 - 4 * a1) + a2 / (1.8 - 6 * a2) + a3 / (1.8 - 6 * a3) :=
  le_trans (margin hδ hc (by linarith))
    (S_ge (by linarith) (by linarith) (by linarith) (by linarith))

end LeanLab.BHP1997.Lemma3
