/-
P0014 H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, Prop. 4.11 for
`η = η₊`, pages 51 and 52: `c₀ ≤ 6.536232 + 9.319578|δ|` and the error total (4.66), from the
printed bounds (B.25) to (B.33) and `Γ(1/2) = √π`, `Γ(3/2) = √π/2`, `Γ(5/2) = 3√π/4`,
`Γ(7/2) = 15√π/8`. Unit U-6065, CLOUD 20261020T0516Z-cloud35. All MATCH; the `|δ|` coefficient
9.319578 has a margin of only 7 · 10⁻⁸ over the value 9.31957790.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import LeanLab.HelfgottMajor.Sec45

namespace LeanLab.HelfgottMajor.Prop411Terms
open Real

lemma sqrt_pi_lt' : √π < 1.77245386 := by
  rw [Real.sqrt_lt' (by norm_num)]; have := pi_lt_d20; nlinarith

lemma sqrt_lt_of {a hi : ℝ} (hh : 0 < hi) (h : a < hi ^ 2) : √a < hi := (Real.sqrt_lt' hh).mpr h

lemma bounds : √(√π) < 1.331335368 ∧ √(√π / 2) < 0.941396267 ∧ √(3 * √π / 4) < 1.152970249 ∧
    √(15 * √π / 8) < 1.823006031 := by
  have h := sqrt_pi_lt'
  refine ⟨sqrt_lt_of (by norm_num) (by nlinarith), sqrt_lt_of (by norm_num) (by nlinarith),
    sqrt_lt_of (by norm_num) (by nlinarith), sqrt_lt_of (by norm_num) (by nlinarith)⟩

/-- **(4.66) c₀: `(2/3)(2.922875(√Γ(1/2) + √Γ(3/2)) + 1.062319(√Γ(5/2) + √Γ(7/2))) ≤ 6.536232`**,
MATCH, value 6.53623106. -/
theorem c0_const :
    2 / 3 * (2.922875 * (√(√π) + √(√π / 2)) + 1.062319 * (√(3 * √π / 4) + √(15 * √π / 8)))
      ≤ 6.536232 := by
  obtain ⟨a, b, c, d⟩ := bounds
  nlinarith

/-- **(4.66) c₀, the `|δ|` coefficient: `(4π/3) · 1.062319 (√Γ(3/2) + √Γ(5/2)) ≤ 9.319578`**, MATCH,
value 9.31957790. -/
theorem c0_delta : 4 * π / 3 * (1.062319 * (√(√π / 2) + √(3 * √π / 4))) ≤ 9.319578 := by
  obtain ⟨-, b, c, -⟩ := bounds
  have hp := pi_lt_d20
  have hs : √(√π / 2) + √(3 * √π / 4) ≤ 2.094366516 := by linarith
  have h0 : (0 : ℝ) ≤ 4 * π / 3 * 1.062319 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hs h0
  have h2 : 4 * π / 3 * 1.062319 * 2.094366516 ≤ 9.319578 := by nlinarith
  nlinarith

/-- **(4.66)**: for `x ≥ 10³`, `log q = L ≥ 0`, `|δ| ≥ 0`,
`6.536232 + 9.319578|δ| + (L + 6.01)(10.845789 + 2π · 0.80044|δ|) x^{-1/2}
≤ 9 + 11|δ| + L (11 + 6|δ|) x^{-1/2}`, MATCH. -/
theorem eq466 {x L δ : ℝ} (hx : 1000 ≤ x) (hL : 0 ≤ L) (hδ : 0 ≤ δ) :
    6.536232 + 9.319578 * δ + (L + 6.01) * (10.845789 + 2 * π * 0.80044 * δ) / √x
      ≤ 9 + 11 * δ + L * (11 + 6 * δ) / √x := by
  have hp := pi_lt_d20
  have hsx : 31.6 ≤ √x := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  have hs0 : 0 < √x := by linarith
  have key : (L + 6.01) * (10.845789 + 2 * π * 0.80044 * δ) ≤
      L * (11 + 6 * δ) + (9 - 6.536232 + (11 - 9.319578) * δ) * √x := by
    nlinarith [mul_nonneg hL hδ, mul_le_mul_of_nonneg_left hsx (by positivity : (0 : ℝ) ≤ δ)]
  have e1 : (L + 6.01) * (10.845789 + 2 * π * 0.80044 * δ) / √x ≤
      L * (11 + 6 * δ) / √x + (9 - 6.536232 + (11 - 9.319578) * δ) := by
    rw [div_le_iff₀ hs0]
    have e : (L * (11 + 6 * δ) / √x + (9 - 6.536232 + (11 - 9.319578) * δ)) * √x =
        L * (11 + 6 * δ) + (9 - 6.536232 + (11 - 9.319578) * δ) * √x := by
      field_simp
    rw [e]; linarith
  linarith

end LeanLab.HelfgottMajor.Prop411Terms
