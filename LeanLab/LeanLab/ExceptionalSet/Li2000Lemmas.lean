/-
CODEX task85 status: eleven valid original open leaves now have proofs. The coefficient conjunction at 279.6 is false and stays sealed. A counterexample and safe coefficient bounds are proved below. The second scalar assemblies for Lemma 6 parts i to v are added. The three cited analytic inputs remain conditional.
AI wrote the Lean code. Binary Goldbach is open.
-/
/-
P0034 H. Z. Li, The exceptional set of Goldbach numbers (II), Acta Arith. 92 (2000), 71-88.
Unit U-1521, PC run 20261025T1603Z-10248, track T1, type STATE. Copy: papers/P0034.pdf; every
constant below was read on the rendered page images of pp. 71, 72, 73, 75, 78, 81, 87.

The companion `Li2000.lean` (unit U-6811) already holds the Theorem's exponent arithmetic and the
numerics (5.4)-(6.7). This file states the numbered lemmas that were not yet in the lab:

* CITED, analytic inputs we do not intend to prove: Lemma 2 (p. 72, from Li 1999), Lemma 7
  (p. 81, from Chen-Pan 1980 Lemma 8), Lemma 8 (p. 85, Wang 1986 Theorem 2).
* OPEN leaves, elementary or explicit: the numerical cores of Lemma 3 (pp. 72-75), of Lemma 5
  (pp. 75-76), of the coefficients of Lemma 6 (pp. 76-80), the count (6.3) (p. 87), the bound
  `q̃ ≤ 16 (n, q̃)/ε²` (p. 87, case 3) and the step `x^{(1-ε)(β̃-1)} n^{β̃} ≤ 0.8905 n` (p. 87).
* PROVED assemblies deriving the paper's printed conclusions from the leaves.

FINDING (p. 78, Section 3 (iii)): the displayed inequality with `0.1876` evaluates to
`0.0146526 > 0.014621` at `a = 6.3`; with Lemma 1's `φ/2 + ε = 0.18751` it is `0.0146207 ≤
0.014621`. Both are proved below. The printed `0.1876` is a misprint; no later constant changes.

AI-written Lean code, Claude, 2026-10-25. Binary Goldbach is OPEN; this is an almost-all result.
-/
import Mathlib
import LeanLab.ExceptionalSet.U1423MVMinor

namespace LeanLab.ExceptionalSet.Li2000Lemmas
open Real

/-! ## CITED analytic inputs -/

/-- Lemma 2, p. 72, CITED from Li 1999 Lemma 2.3: for `Y` large, at most one primitive
character `χ` mod `q ≤ Y` has `L(s, χ)` vanishing in `σ ≥ 1 - 0.239/log Y`,
`q(|t| + 1) ≤ Y^{1+ε}`, and such an exceptional character is real (`χ² = 1`). The paper's
`ε` is "sufficiently small"; we assert only that some `ε > 0` works. The bounds on the real zero
`β̃` are not stated. Unit U-1521. -/
theorem lemma2_cited : ∃ ε : ℝ, 0 < ε ∧ ∃ Y0 : ℝ, ∀ Y : ℝ, Y0 ≤ Y →
    let Z : Set ((q : ℕ+) × DirichletCharacter ℂ (q : ℕ)) :=
      {p | ((p.1 : ℕ) : ℝ) ≤ Y ∧ p.2.IsPrimitive ∧
        ∃ s : ℂ, DirichletCharacter.LFunction p.2 s = 0 ∧ 1 - 0.239 / Real.log Y ≤ s.re ∧
          ((p.1 : ℕ) : ℝ) * (|s.im| + 1) ≤ Y ^ (1 + ε)}
    Z.Subsingleton ∧ ∀ p ∈ Z, p.2 ^ 2 = 1 := by
  sorry

/-- Lemma 8, p. 85, CITED from W. Wang 1986 Theorem 2: `χ₁` real non-principal mod `q` with a
real zero `β₁ = 1 - δ₁`, `χ` mod `q` with a zero `1 - δ + iγ`, `δ < 1/6`, `1 - δ ≤ β₁`,
`D = q(|γ| + 1) ≥ D₀(ε)`; then `δ₁ ≥ (2/3 - ε)(1 - 6δ) D^{-(3/2+ε)δ/(1-6δ)} / log D`.
Transcribed from Li's statement; the source [9] was not seen. Unit U-1521. -/
theorem lemma8_cited : ∀ ε : ℝ, 0 < ε → ∃ D0 : ℝ, ∀ (q : ℕ) [NeZero q]
    (χ₁ χ : DirichletCharacter ℂ q) (δ₁ δ γ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → DirichletCharacter.LFunction χ₁ (1 - δ₁ : ℝ) = 0 →
    DirichletCharacter.LFunction χ ⟨1 - δ, γ⟩ = 0 → δ < 1 / 6 → 1 - δ ≤ 1 - δ₁ →
    D0 ≤ (q : ℝ) * (|γ| + 1) →
    (2 / 3 - ε) * (1 - 6 * δ) * ((q : ℝ) * (|γ| + 1)) ^ (-(3 / 2 + ε) * δ / (1 - 6 * δ)) /
      Real.log ((q : ℝ) * (|γ| + 1)) ≤ δ₁ := by
  sorry

/-- p. 81: `S(α) = Σ_{Y < p ≤ x} log p · e(αp)`. -/
noncomputable def S (x Y α : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Iic ⌊x⌋₊ : Finset ℕ).filter (fun p : ℕ => p.Prime ∧ Y < (p : ℝ)),
    (Real.log (p : ℝ) : ℂ) * Complex.exp (2 * π * Complex.I * α * (p : ℂ))

/-- p. 81: the major arcs `E₁ = ⋃_{q ≤ Y} ⋃_{a ≤ q, (a,q)=1} [a/q - 1/(qQ), a/q + 1/(qQ)]`,
`Y = x^λ`, `Q = x^{1-λ}`. -/
noncomputable def E1 (x lam : ℝ) : Set ℝ :=
  ⋃ q ∈ Finset.Icc 1 ⌊x ^ lam⌋₊, ⋃ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
    Set.Icc ((a : ℝ) / q - 1 / (q * x ^ (1 - lam))) ((a : ℝ) / q + 1 / (q * x ^ (1 - lam)))

/-- (4.2), p. 81: `D₂(n) = ∫_{E₂} S²(α) e(-αn) dα`, `E₂ = (-τ, 1-τ] \ E₁`, `τ = 1/Q`. -/
noncomputable def D2 (x lam : ℝ) (n : ℕ) : ℂ :=
  ∫ α in Set.Ioc (-(x ^ (1 - lam))⁻¹) (1 - (x ^ (1 - lam))⁻¹) \ E1 x lam,
    S x (x ^ lam) α ^ 2 * Complex.exp (-(2 * π * Complex.I * α * n))

/-- Lemma 7, p. 81, CITED from Chen-Pan 1980 Lemma 8: with `λ = 0.0862`, the number of integers
`n ∈ [(1-ε)x, x]` with `|D₂(n)| > 0.5 x^{1-10^{-5}λ}` is `≪ x^{1-(1-10^{-4})λ}`. The paper's
`ε` is "sufficiently small"; we assert it for all `ε` below some `ε₀ > 0`. Unit U-1521. -/
theorem lemma7_cited : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
      (((Finset.Iic ⌊x⌋₊).filter (fun n : ℕ => (1 - ε) * x ≤ (n : ℝ) ∧
          0.5 * x ^ (1 - (10 : ℝ)⁻¹ ^ 5 * 0.0862) < ‖D2 x 0.0862 n‖)).card : ℝ)
        ≤ C * x ^ (1 - (1 - (10 : ℝ)⁻¹ ^ 4) * 0.0862) := by
  sorry

/-! ## Lemma 3, pp. 72-75 -/

/-- p. 72: `P(x) = x + x² + (2/3)x³`. -/
noncomputable def P (x : ℝ) : ℝ := x + x ^ 2 + 2 / 3 * x ^ 3

/-- p. 72: `ψ = (φ/2)(k² + 3k + 3/2)`, `φ = 3/8`. -/
noncomputable def psi (k : ℝ) : ℝ := (3 / 8) / 2 * (k ^ 2 + 3 * k + 3 / 2)

/-- Lemma 3, p. 72, the case `χ² = χ₀`, `ϱ₁` complex or `χ³ = χ₀`, with `a = 2.4`, `k = 0.88`:
for `0 ≤ λ₁, λ₂ ≤ 0.618` and `0 ≤ ε ≤ 10^{-4}`,
`(k² + 1/2){P((a+λ₁)/a) - P((a+λ₁)/(a+λ₂))} - 2kP(1) + (a+λ₁)(ψ + ε) < 0`.
Numerically the maximum is `-0.0036` at `λ₁ = λ₂ = 0.618`. Unit U-1521. -/
theorem lemma3_a24 (l1 l2 ε : ℝ) (h1 : 0 ≤ l1) (h1' : l1 ≤ 0.618) (h2 : 0 ≤ l2)
    (h2' : l2 ≤ 0.618) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 10 ^ 4) :
    (0.88 ^ 2 + 1 / 2) * (P ((2.4 + l1) / 2.4) - P ((2.4 + l1) / (2.4 + l2)))
      - 2 * 0.88 * P 1 + (2.4 + l1) * (psi 0.88 + ε) < 0 := by
  have hm : P ((2.4 + l1) / 3.018) ≤ P ((2.4 + l1) / (2.4 + l2)) := by
    unfold P
    gcongr <;> linarith
  have hpow2 : (2.4 + l1)^2 ≤ (3.018 : ℝ)^2 := by gcongr; linarith
  have hpow3 : (2.4 + l1)^3 ≤ (3.018 : ℝ)^3 := by gcongr; linarith
  have hdiff : P ((2.4 + l1) / 2.4) - P ((2.4 + l1) / 3.018) ≤ P (3.018 / 2.4) - P 1 := by
    norm_num [P] at *
    nlinarith
  have he : (2.4 + l1) * (psi 0.88 + ε) ≤ 3.018 * (psi 0.88 + 1 / 10 ^ 4) := by
    gcongr <;> norm_num [psi] <;> linarith
  norm_num [P, psi] at hm hdiff he ⊢
  linarith

/-- Lemma 3, p. 73, the case `χ` not of order 2 or 3, `a = 2.21`, `k = 0.89`: for
`0 ≤ λ₁, λ₂ ≤ 0.575`, `0 ≤ ε ≤ 1/20000`, `(k²+1/2){P((a+0.239)/a) - P((a+0.239)/(a+λ₂))}
- 2kP((a+0.239)/(a+λ₁)) + (a+0.239)(ψ+ε) < 0`. Numerically the maximum is `-0.000403` at
`λ₁ = λ₂ = 0.575`. Unit U-1521. -/
theorem lemma3_a221 (l1 l2 ε : ℝ) (h1 : 0 ≤ l1) (h1' : l1 ≤ 0.575) (h2 : 0 ≤ l2)
    (h2' : l2 ≤ 0.575) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 20000) :
    (0.89 ^ 2 + 1 / 2) * (P ((2.21 + 0.239) / 2.21) - P ((2.21 + 0.239) / (2.21 + l2)))
      - 2 * 0.89 * P ((2.21 + 0.239) / (2.21 + l1)) + (2.21 + 0.239) * (psi 0.89 + ε) < 0 := by
  have hm : ∀ x : ℝ, 0 ≤ x → x ≤ 0.575 → P ((2.21 + 0.239) / (2.21 + 0.575)) ≤ P ((2.21 + 0.239) / (2.21 + x)) := by
    intro x hx hx'
    unfold P
    gcongr
  have hA := hm l1 h1 h1'
  have hB := hm l2 h2 h2'
  norm_num [P, psi] at hA hB ⊢
  linarith

/-- Lemma 3, p. 75, `λ₃`, `a = 2`: for `0 ≤ λ₁ ≤ λ₂ ≤ λ₃ < 0.68` and `0 ≤ ε ≤ 1/200`,
`P(1) - P(a/(a+λ₁)) - P(a/(a+λ₂)) - P(a/(a+λ₃)) + a((11/4)φ + ε) < 0`; at `λⱼ = 0.68` the value
is `-0.0116`. Unit U-1521. -/
theorem lemma3_lambda3 (l1 l2 l3 ε : ℝ) (h1 : 0 ≤ l1) (h12 : l1 ≤ l2) (h23 : l2 ≤ l3)
    (h3 : l3 < 0.68) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 200) :
    P 1 - P (2 / (2 + l1)) - P (2 / (2 + l2)) - P (2 / (2 + l3))
      + 2 * (11 / 4 * (3 / 8) + ε) < 0 := by
  have hm : ∀ x : ℝ, 0 ≤ x → x ≤ 0.68 → P (2 / (2 + 0.68)) ≤ P (2 / (2 + x)) := by
    intro x hx hx'
    unfold P
    gcongr <;> linarith
  have hA := hm l1 h1 (by linarith)
  have hB := hm l2 (by linarith) (by linarith)
  have hC := hm l3 (by linarith) h3.le
  norm_num [P] at hA hB hC ⊢
  linarith

/-- ASSEMBLY, p. 72: "if `λ₁ ≤ 0.618` then `λ₂ > 0.618`", from `lemma3_a24`. -/
theorem lemma3_a24_conclusion (l1 l2 ε : ℝ) (h1 : 0 ≤ l1) (h1' : l1 ≤ 0.618) (h2 : 0 ≤ l2)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 10 ^ 4)
    (hHB : 0 ≤ (0.88 ^ 2 + 1 / 2) * (P ((2.4 + l1) / 2.4) - P ((2.4 + l1) / (2.4 + l2)))
      - 2 * 0.88 * P 1 + (2.4 + l1) * (psi 0.88 + ε)) : 0.618 < l2 := by
  by_contra h
  exact absurd hHB (not_le.mpr (lemma3_a24 l1 l2 ε h1 h1' h2 (not_lt.mp h) hε hε'))

/-- ASSEMBLY, p. 73: "if `λ₁ ≤ 0.575` then `λ₂ > 0.575`", from `lemma3_a221`. -/
theorem lemma3_a221_conclusion (l1 l2 ε : ℝ) (h1 : 0 ≤ l1) (h1' : l1 ≤ 0.575) (h2 : 0 ≤ l2)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 20000)
    (hHB : 0 ≤ (0.89 ^ 2 + 1 / 2) * (P ((2.21 + 0.239) / 2.21) - P ((2.21 + 0.239) / (2.21 + l2)))
      - 2 * 0.89 * P ((2.21 + 0.239) / (2.21 + l1)) + (2.21 + 0.239) * (psi 0.89 + ε)) :
    0.575 < l2 := by
  by_contra h
  exact absurd hHB (not_le.mpr (lemma3_a221 l1 l2 ε h1 h1' h2 (not_lt.mp h) hε hε'))

/-- ASSEMBLY, p. 75: "taking `a = 2`, we have `λ₃ ≥ 0.68`", from `lemma3_lambda3`. -/
theorem lemma3_lambda3_conclusion (l1 l2 l3 ε : ℝ) (h1 : 0 ≤ l1) (h12 : l1 ≤ l2) (h23 : l2 ≤ l3)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 200)
    (h : 0 ≤ P 1 - P (2 / (2 + l1)) - P (2 / (2 + l2)) - P (2 / (2 + l3))
      + 2 * (11 / 4 * (3 / 8) + ε)) : 0.68 ≤ l3 := by
  by_contra h3
  exact absurd h (not_le.mpr (lemma3_lambda3 l1 l2 l3 ε h1 h12 h23 (not_le.mp h3) hε hε'))

/-! ## Lemma 5, pp. 75-76 -/

/-- Lemma 5 (i), p. 75, the kernel step: `x ↦ x/(x² + w²)` decreases for `x ≥ w`, so for
`0 < a`, `w ≤ a ≤ b`, `|u| ≤ w`, `b/(b² + w²) ≤ a/(a² + u²)`. With `a = 8.4 + λ`, `b = 9.4`,
`w = 5.8` this is `-ℜ 1/(s - ϱ) ≤ -𝓛 · 9.4/(9.4² + 5.8²)`. Unit U-1521. -/
theorem kernel_anti (a b u w : ℝ) (ha : 0 < a) (hw : 0 ≤ w) (hwa : w ≤ a) (hab : a ≤ b)
    (hu : |u| ≤ w) : b / (b ^ 2 + w ^ 2) ≤ a / (a ^ 2 + u ^ 2) := by
  have hb : 0 < b := ha.trans_le hab
  have hu2 : u ^ 2 ≤ w ^ 2 := by nlinarith [abs_le.mp hu, sq_abs u]
  have hwa2 : w ^ 2 ≤ a * b := by nlinarith [mul_nonneg (sub_nonneg.mpr hwa) (add_nonneg ha.le hw), mul_nonneg ha.le (sub_nonneg.mpr hab)]
  apply (div_le_div_iff₀ (by positivity : 0 < b ^ 2 + w ^ 2) (by positivity : 0 < a ^ 2 + u ^ 2)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hwa2), mul_nonneg hb.le (sub_nonneg.mpr hu2)]

/-- Lemma 5 (ii), p. 76, the `R₂` arithmetic: for `λ⁺ > 5` and `n ≥ 0`,
`n · (24+λ⁺)/((24+λ⁺)² + 23.4²) ≤ 1/24 + 0.18752` gives `n ≤ 0.2292(λ⁺ + 42.9)`
(use `(24+λ⁺) + 23.4²/(24+λ⁺) ≤ λ⁺ + 42.882`). Unit U-1521. -/
theorem lemma5_n2_arith (lp n : ℝ) (hlp : 5 < lp) (hn : 0 ≤ n)
    (h : n * ((24 + lp) / ((24 + lp) ^ 2 + 23.4 ^ 2)) ≤ 1 / 24 + 0.18752) :
    n ≤ 0.2292 * (lp + 42.9) := by
  have hd : 0 < (24 + lp) ^ 2 + 23.4 ^ 2 := by positivity
  have h' : n * (24 + lp) ≤ (1 / 24 + 0.18752) * ((24 + lp) ^ 2 + 23.4 ^ 2) := by
    apply (div_le_iff₀ hd).mp
    simpa [mul_div_assoc] using h
  have hp : 0 < lp - 5 := by linarith
  have hx := sq_nonneg (lp - 5)
  norm_num at h'
  nlinarith

/-- ASSEMBLY, Lemma 5 (i), p. 75, `n₀ ≤ 3`: zeros `ϱⱼ = 1 - λⱼ/𝓛 + iγⱼ` in `R₀`, written
`0 ≤ λⱼ ≤ 1`, `uⱼ = (γⱼ - t₀)𝓛`, `|uⱼ| ≤ 5.8`, counted with multiplicity as a family indexed
by `Fin n`; the Lemma 1 bound at `σ = 1 + 8.4/𝓛` gives `Σⱼ (8.4+λⱼ)/((8.4+λⱼ)² + uⱼ²) ≤
1/8.4 + 0.18752`. Then `n ≤ 3`. -/
theorem lemma5_R0 (n : ℕ) (l u : Fin n → ℝ) (hl : ∀ j, 0 ≤ l j ∧ l j ≤ 1)
    (hu : ∀ j, |u j| ≤ 5.8)
    (hsum : ∑ j, (8.4 + l j) / ((8.4 + l j) ^ 2 + u j ^ 2) ≤ 1 / 8.4 + 0.18752) : n ≤ 3 := by
  have hk : ∀ j, (9.4 : ℝ) / (9.4 ^ 2 + 5.8 ^ 2) ≤ (8.4 + l j) / ((8.4 + l j) ^ 2 + u j ^ 2) :=
    fun j => kernel_anti _ _ _ _ (by linarith [(hl j).1]) (by norm_num) (by linarith [(hl j).1])
      (by linarith [(hl j).2]) (hu j)
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hk j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have : (n : ℝ) < 4 := by nlinarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- ASSEMBLY, Lemma 5 (ii), p. 76, `n₁ ≤ 10`: as `lemma5_R0` for `R₁`, `σ = 1 + 24/𝓛`,
`0 ≤ λⱼ ≤ 5`, `|uⱼ| ≤ 23.4`. -/
theorem lemma5_R1 (n : ℕ) (l u : Fin n → ℝ) (hl : ∀ j, 0 ≤ l j ∧ l j ≤ 5)
    (hu : ∀ j, |u j| ≤ 23.4)
    (hsum : ∑ j, (24 + l j) / ((24 + l j) ^ 2 + u j ^ 2) ≤ 1 / 24 + 0.18752) : n ≤ 10 := by
  have hk : ∀ j, (29 : ℝ) / (29 ^ 2 + 23.4 ^ 2) ≤ (24 + l j) / ((24 + l j) ^ 2 + u j ^ 2) :=
    fun j => kernel_anti _ _ _ _ (by linarith [(hl j).1]) (by norm_num) (by linarith [(hl j).1])
      (by linarith [(hl j).2]) (hu j)
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hk j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have : (n : ℝ) < 11 := by nlinarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- ASSEMBLY, Lemma 5 (ii), p. 76, `n₂ ≤ 0.2292(λ⁺ + 42.9)`: as `lemma5_R0` for `R₂`,
`σ = 1 + 24/𝓛`, `0 ≤ λⱼ ≤ λ⁺`, `5 < λ⁺`, `|uⱼ| ≤ 23.4`; from `kernel_anti` and
`lemma5_n2_arith`. -/
theorem lemma5_R2 (n : ℕ) (lp : ℝ) (hlp : 5 < lp) (l u : Fin n → ℝ)
    (hl : ∀ j, 0 ≤ l j ∧ l j ≤ lp) (hu : ∀ j, |u j| ≤ 23.4)
    (hsum : ∑ j, (24 + l j) / ((24 + l j) ^ 2 + u j ^ 2) ≤ 1 / 24 + 0.18752) :
    (n : ℝ) ≤ 0.2292 * (lp + 42.9) := by
  have hk : ∀ j, (24 + lp) / ((24 + lp) ^ 2 + 23.4 ^ 2) ≤
      (24 + l j) / ((24 + l j) ^ 2 + u j ^ 2) :=
    fun j => kernel_anti _ _ _ _ (by linarith [(hl j).1]) (by norm_num) (by linarith [(hl j).1])
      (by linarith [(hl j).2]) (hu j)
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hk j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  exact lemma5_n2_arith lp n hlp (Nat.cast_nonneg n) (hs.trans hsum)

/-! ## Lemma 6, pp. 76-80: the explicit coefficients -/

/-- Lemma 6, (3.9)-(3.15), pp. 77-80, the bracket: for `λ > 0`, `C < B ≤ A`,
`0 ≤ (e^{Bλ} - e^{Cλ})/((B-C)λ) ≤ e^{Aλ}`, the mean of `e^{tλ}` over `[C, B]`; here
`A = 2h₃`, `B = 2h₂`, `C = 2h₁`, so the bracket `e^{2h₃λ} - (e^{2h₂λ} - e^{2h₁λ})/(2λ(h₂-h₁))`
is nonnegative. Unit U-1521. -/
theorem bracket_bounds (A B C l : ℝ) (hl : 0 < l) (hCB : C < B) (hBA : B ≤ A) :
    0 ≤ (Real.exp (B * l) - Real.exp (C * l)) / ((B - C) * l) ∧
      (Real.exp (B * l) - Real.exp (C * l)) / ((B - C) * l) ≤ Real.exp (A * l) := by
  have hd : 0 < (B-C)*l := mul_pos (sub_pos.mpr hCB) hl
  constructor
  · exact div_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCB.le hl.le))) hd.le
  · apply (div_le_iff₀ hd).2
    have ht := Real.add_one_le_exp ((C-B)*l)
    have hm := mul_le_mul_of_nonneg_left ht (Real.exp_pos (B*l)).le
    have he : Real.exp (B*l) * Real.exp ((C-B)*l) = Real.exp (C*l) := by
      rw [← Real.exp_add]
      ring_nf
    rw [he] at hm
    have hx : Real.exp (B*l) ≤ Real.exp (A*l) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hBA hl.le)
    have hy := mul_le_mul_of_nonneg_right hx hd.le
    nlinarith

/-- Generic ASSEMBLY for Lemma 6: a coefficient bound `(1+δ)c ≤ K` turns the right side of
(3.9)-(3.15), `(1+δ) c/λ · (e^{Aλ} - (e^{Bλ} - e^{Cλ})/(Wλ))` with `W = B - C`, into the printed
form `K · C_i(λ) e^{Aλ}`, `C_i(λ) = λ⁻¹(1 - e^{-Aλ}(e^{Bλ} - e^{Cλ})/(Wλ))`. -/
theorem zd_assembly (A B C W l c K δ : ℝ) (hl : 0 < l) (hCB : C < B) (hBA : B ≤ A)
    (hW : W = B - C) (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hK : (1 + δ) * c ≤ K) :
    (1 + δ) * c / l * (Real.exp (A * l) - (Real.exp (B * l) - Real.exp (C * l)) / (W * l)) ≤
      K * (l⁻¹ * (1 - Real.exp (-(A * l)) * (Real.exp (B * l) - Real.exp (C * l)) / (W * l))) *
        Real.exp (A * l) := by
  subst hW
  obtain ⟨_, hb⟩ := bracket_bounds A B C l hl hCB hBA
  set m := (Real.exp (B * l) - Real.exp (C * l)) / ((B - C) * l)
  have hm : Real.exp (-(A * l)) * (Real.exp (B * l) - Real.exp (C * l)) / ((B - C) * l)
      = Real.exp (-(A * l)) * m := by simp only [m]; ring
  have he : (l⁻¹ * (1 - Real.exp (-(A * l)) * m)) * Real.exp (A * l) =
      (Real.exp (A * l) - m) / l := by
    rw [Real.exp_neg]; field_simp
  rw [hm, mul_assoc K, he]
  have h0 : 0 ≤ (Real.exp (A * l) - m) / l := div_nonneg (by linarith) hl.le
  calc (1 + δ) * c / l * (Real.exp (A * l) - m) = ((1 + δ) * c) * ((Real.exp (A * l) - m) / l) := by
        ring
    _ ≤ K * ((Real.exp (A * l) - m) / l) := mul_le_mul_of_nonneg_right hK h0

/-- A safe intermediate bound for the printed coefficients on Li 2000 page 78. -/
theorem lemma6_i_coef_safe (l : ℝ) (hl : 5 < l) :
    0.2292 * (l + 42.9) * (1.08 - 0.58 + 2 * Real.pi / 23.4) / (2 * l * (0.669 - 0.58) * 0.0353)
        ≤ 268.56 ∧
      0.2292 * (l + 42.9) * (1.45 - 0.95 + 2 * Real.pi / 23.4) / (2 * l * (1.042 - 0.95) * 0.0328)
        ≤ 279.61 := by
  have hpi := Real.pi_lt_d4
  have hp : 0 ≤ l + 42.9 := by linarith
  have hm := mul_le_mul_of_nonneg_left hpi.le hp
  constructor <;> rw [div_le_iff₀ (by positivity)] <;> norm_num at * <;> nlinarith




/-- A counterexample to the sealed 279.6 coefficient bound. The paper prints 279.7. -/
theorem lemma6_i_coef_second_counterexample : (279.6 : ℝ) <
    0.2292 * (5.000001 + 42.9) * (1.45 - 0.95 + 2 * Real.pi / 23.4) /
      (2 * 5.000001 * (1.042 - 0.95) * 0.0328) := by
  have hpi := Real.pi_gt_d6
  norm_num at *
  linarith


/-- Lemma 6 (i), p. 78, the `δ₁h₁ = δ₃h₃ = π/23.4` coefficients after the bracket of `M(ϱ₀)`
simplifies to `(h₃ - h₁) + 2π/23.4` (`lemma6_i_simplify`): for `λ > 5`,
`0.2292(λ+42.9)(1.08-0.58+2π/23.4)/(2λ(0.669-0.58)·0.0353) ≤ 268.56` and
`0.2292(λ+42.9)(1.45-0.95+2π/23.4)/(2λ(1.042-0.95)·0.0328) ≤ 279.6`; the values at `λ = 5` are
`268.552` and `279.596`. Unit U-1521. -/

theorem lemma6_i_coef (l : ℝ) (hl : 5 < l) :
    0.2292 * (l + 42.9) * (1.08 - 0.58 + 2 * π / 23.4) / (2 * l * (0.669 - 0.58) * 0.0353)
        ≤ 268.56 ∧
      0.2292 * (l + 42.9) * (1.45 - 0.95 + 2 * π / 23.4) / (2 * l * (1.042 - 0.95) * 0.0328)
        ≤ 279.6 := by
  sorry

/-- Lemma 6 (ii), p. 78, with `n₁ ≤ 10`, so `M(ϱ₀) ≤ (10/2)𝓛³{…}` and the coefficient is
`10((h₃-h₁) + 2π/23.4)/(2(h₂-h₁)h₄)`: `10(1.71-0.82+2π/23.4)/(2(1.179-0.82)·0.155) ≤ 104.099`
and `10(2.08-1.19+2π/23.4)/(2(1.552-1.19)·0.1528) ≤ 104.73`; values `104.0985`, `104.7222`.
PROVED from `π < 3.1416`. -/
theorem lemma6_ii_coef :
    10 * (1.71 - 0.82 + 2 * π / 23.4) / (2 * (1.179 - 0.82) * 0.155) ≤ (104.099 : ℝ) ∧
      10 * (2.08 - 1.19 + 2 * π / 23.4) / (2 * (1.552 - 1.19) * 0.1528) ≤ (104.73 : ℝ) := by
  have hpi := Real.pi_lt_d4
  constructor <;> rw [div_le_iff₀ (by norm_num)] <;> norm_num <;> linarith

/-- p. 78: with `δ₁ = t/h₁`, `δ₃ = t/h₃`, the bracket of `M(ϱ₀)` divided by the `δ₁δ₃h₁h₃`
of (3.9), times `1/2`, is `(h₃ - h₁) + 2t`. PROVED. -/
theorem lemma6_i_simplify (t h1 h3 : ℝ) (ht : 0 < t) (h1p : 0 < h1) (h3p : 0 < h3) :
    (1 / 2) * (((t / h1) * h1 * (2 * (t / h3) + (t / h3) ^ 2) * h3 ^ 2
        - (t / h3) * h3 * (2 * (t / h1) - (t / h1) ^ 2) * h1 ^ 2)
        + t ^ 2 * ((t / h1) * h1 + (t / h3) * h3)) / ((t / h1) * (t / h3) * h1 * h3)
      = (h3 - h1) + 2 * t := by
  field_simp
  ring

/-- ASSEMBLY, Lemma 6 (i), p. 78, `N₁*(α, Y) ≤ 268.6 e^{2.16λ}` for `5 < λ`: the right side of
(3.9) with Lemma 5's `M(ϱ₀)`, simplified by `lemma6_i_simplify`, is at most the printed bound,
for `0 ≤ δ ≤ 10^{-6}`. `e^{2h₃λ} = e^{2.16λ}`, and the subtracted term only helps. -/
theorem lemma6_i_N1 (l δ : ℝ) (hl : 5 < l) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10 ^ 6) :
    (1 + δ) * (0.2292 * (l + 42.9) * (1.08 - 0.58 + 2 * π / 23.4) /
        (2 * l * (0.669 - 0.58) * 0.0353)) *
      (Real.exp (2.16 * l) - (Real.exp (1.338 * l) - Real.exp (1.16 * l)) / (0.178 * l))
      ≤ 268.6 * Real.exp (2.16 * l) := by
  have hl0 : 0 < l := by linarith
  obtain ⟨hb0, _⟩ := bracket_bounds 2.16 1.338 1.16 l hl0 (by norm_num) (by norm_num)
  have hW : (1.338 - 1.16 : ℝ) * l = 0.178 * l := by ring
  rw [hW] at hb0
  have hc := (lemma6_i_coef_safe l hl).1
  have hpi := Real.pi_pos
  have hc0 : 0 ≤ 0.2292 * (l + 42.9) * (1.08 - 0.58 + 2 * π / 23.4) /
      (2 * l * (0.669 - 0.58) * 0.0353) := by positivity
  have hE := Real.exp_pos (2.16 * l)
  set c := 0.2292 * (l + 42.9) * (1.08 - 0.58 + 2 * π / 23.4) / (2 * l * (0.669 - 0.58) * 0.0353)
  set m := (Real.exp (1.338 * l) - Real.exp (1.16 * l)) / (0.178 * l)
  have h1 : (1 + δ) * c ≤ 268.6 := by nlinarith
  have h2 : Real.exp (2.16 * l) - m ≤ Real.exp (2.16 * l) := by linarith
  calc (1 + δ) * c * (Real.exp (2.16 * l) - m) ≤ (1 + δ) * c * Real.exp (2.16 * l) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 268.6 * Real.exp (2.16 * l) := mul_le_mul_of_nonneg_right h1 hE.le

/-- Li 2000 page 78, scalar assembly for the second estimate of Lemma 6 part i. -/
theorem lemma6_i_N (l δ : ℝ) (hl : 5 < l) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10 ^ 6) :
    (1 + δ) * (0.2292 * (l + 42.9) * (1.45 - 0.95 + 2 * π / 23.4) /
        (2 * l * (1.042 - 0.95) * 0.0328)) *
      (Real.exp (2.9 * l) - (Real.exp (2.084 * l) - Real.exp (1.9 * l)) / (0.184 * l))
      ≤ 279.7 * Real.exp (2.9 * l) := by
  have hl0 : 0 < l := by linarith
  obtain ⟨hb0, _⟩ := bracket_bounds 2.9 2.084 1.9 l hl0 (by norm_num) (by norm_num)
  have hW : (2.084 - 1.9 : ℝ) * l = 0.184 * l := by ring
  rw [hW] at hb0
  have hc := (lemma6_i_coef_safe l hl).2
  have hpi := Real.pi_pos
  have hc0 : 0 ≤ 0.2292 * (l + 42.9) * (1.45 - 0.95 + 2 * π / 23.4) /
      (2 * l * (1.042 - 0.95) * 0.0328) := by positivity
  have hE := Real.exp_pos (2.9 * l)
  set c := 0.2292 * (l + 42.9) * (1.45 - 0.95 + 2 * π / 23.4) / (2 * l * (1.042 - 0.95) * 0.0328)
  set m := (Real.exp (2.084 * l) - Real.exp (1.9 * l)) / (0.184 * l)
  have h1 : (1 + δ) * c ≤ 279.7 := by nlinarith
  have h2 : Real.exp (2.9 * l) - m ≤ Real.exp (2.9 * l) := by linarith
  calc (1 + δ) * c * (Real.exp (2.9 * l) - m) ≤ (1 + δ) * c * Real.exp (2.9 * l) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 279.7 * Real.exp (2.9 * l) := mul_le_mul_of_nonneg_right h1 hE.le

/-- ASSEMBLY, Lemma 6 (ii), p. 78, `N₁*(α, Y) ≤ 104.1 C₄(λ) e^{3.42λ}`, `C₄(λ) = λ⁻¹(1 -
e^{-3.42λ}(e^{2.358λ} - e^{1.64λ})/(0.718λ))`, from (3.9) with `n₁ ≤ 10` and
`lemma6_i_simplify`, for every `λ > 0`
(the paper needs `1 < λ ≤ 5`) and `0 ≤ δ ≤ 10^{-6}`; from `lemma6_ii_coef`, `zd_assembly`. -/
theorem lemma6_ii_N1 (l δ : ℝ) (hl : 0 < l) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10 ^ 6) :
    (1 + δ) * (10 * (1.71 - 0.82 + 2 * π / 23.4) / (2 * (1.179 - 0.82) * 0.155)) / l *
      (Real.exp (3.42 * l) - (Real.exp (2.358 * l) - Real.exp (1.64 * l)) / (0.718 * l))
      ≤ 104.1 * (l⁻¹ * (1 - Real.exp (-(3.42 * l)) *
          (Real.exp (2.358 * l) - Real.exp (1.64 * l)) / (0.718 * l))) * Real.exp (3.42 * l) := by
  have hpi := Real.pi_pos
  have hc := (lemma6_ii_coef).1
  have hc0 : (0 : ℝ) ≤ 10 * (1.71 - 0.82 + 2 * π / 23.4) / (2 * (1.179 - 0.82) * 0.155) := by
    positivity
  exact zd_assembly 3.42 2.358 1.64 0.718 l _ 104.1 δ hl (by norm_num) (by norm_num)
    (by norm_num) hc0 hδ (by nlinarith)

/-- ASSEMBLY, Lemma 6 (iii), p. 79, `N₁*(α, Y) ≤ 14.3 C₃(λ) e^{4.5λ}`: (3.9) with `a = 6.3`,
`h = (1.0065, 1.599, 2.25, 0.2759)`, `δ₁ = 0.079`, `δ₃ = 0.094`; the coefficient is `14.2932`.
PROVED. -/
theorem lemma6_iii_N1 (l δ : ℝ) (hl : 0 < l) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10 ^ 6) :
    (1 + δ) * ((1.5 * (0.079 * 1.0065 * (2 * 0.094 + 0.094 ^ 2) * 2.25 ^ 2
        - 0.094 * 2.25 * (2 * 0.079 - 0.079 ^ 2) * 1.0065 ^ 2)
        + 2 * 0.014621 * (0.079 * 1.0065 + 0.094 * 2.25)) /
        (2 * (1.599 - 1.0065) * 0.079 * 0.094 * 1.0065 * 2.25 * 0.2759)) / l *
      (Real.exp (4.5 * l) - (Real.exp (3.198 * l) - Real.exp (2.013 * l)) / (1.185 * l))
      ≤ 14.3 * (l⁻¹ * (1 - Real.exp (-(4.5 * l)) *
          (Real.exp (3.198 * l) - Real.exp (2.013 * l)) / (1.185 * l))) * Real.exp (4.5 * l) :=
  zd_assembly 4.5 3.198 2.013 1.185 l _ 14.3 δ hl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hδ (by nlinarith)

/-- ASSEMBLY, Lemma 6 (iv), p. 79, `N₁*(α, Y) ≤ 8.46 C₂(λ) e^{4.12λ}`: (3.11) with
`M̃ ≤ 2(h₃ - h₁)𝓛`, `h = (0.89, 1.4275, 2.06, 0.2574)`; coefficient `8.4567`. PROVED. -/
theorem lemma6_iv_N1 (l δ : ℝ) (hl : 0 < l) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10 ^ 6) :
    (1 + δ) * (2 * (2.06 - 0.89) / (2 * (1.4275 - 0.89) * 0.2574)) / l *
      (Real.exp (4.12 * l) - (Real.exp (2.855 * l) - Real.exp (1.78 * l)) / (1.075 * l))
      ≤ 8.46 * (l⁻¹ * (1 - Real.exp (-(4.12 * l)) *
          (Real.exp (2.855 * l) - Real.exp (1.78 * l)) / (1.075 * l))) * Real.exp (4.12 * l) :=
  zd_assembly 4.12 2.855 1.78 1.075 l _ 8.46 δ hl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hδ (by nlinarith)

/-- ASSEMBLY, Lemma 6 (v), p. 80, `N₁*(α, Y) ≤ 4.356 C₁(λ) e^{4.064λ}`: (3.13) with
`h = (0.88, 1.404, 2.032, 0.2524)`; coefficient `(h₃-h₁)/(2(h₂-h₁)h₄) = 4.35505`. PROVED. -/
theorem lemma6_v_N1 (l δ : ℝ) (hl : 0 < l) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10 ^ 6) :
    (1 + δ) * ((2.032 - 0.88) / (2 * (1.404 - 0.88) * 0.2524)) / l *
      (Real.exp (4.064 * l) - (Real.exp (2.808 * l) - Real.exp (1.76 * l)) / (1.048 * l))
      ≤ 4.356 * (l⁻¹ * (1 - Real.exp (-(4.064 * l)) *
          (Real.exp (2.808 * l) - Real.exp (1.76 * l)) / (1.048 * l))) * Real.exp (4.064 * l) :=
  zd_assembly 4.064 2.808 1.76 1.048 l _ 4.356 δ hl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hδ (by nlinarith)

/-- ASSEMBLY, Lemma 6 (vi), p. 80, `N*(α, Y) ≤ 3.632 C₅(λ) e^{5.2λ}`: (3.15) with
`h = (1.334, 1.933, 2.6, 0.291)`; coefficient `3.63149`. PROVED. -/
theorem lemma6_vi_N (l δ : ℝ) (hl : 0 < l) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10 ^ 6) :
    (1 + δ) * ((2.6 - 1.334) / (2 * (1.933 - 1.334) * 0.291)) / l *
      (Real.exp (5.2 * l) - (Real.exp (3.866 * l) - Real.exp (2.668 * l)) / (1.198 * l))
      ≤ 3.632 * (l⁻¹ * (1 - Real.exp (-(5.2 * l)) *
          (Real.exp (3.866 * l) - Real.exp (2.668 * l)) / (1.198 * l))) * Real.exp (5.2 * l) :=
  zd_assembly 5.2 3.866 2.668 1.198 l _ 3.632 δ hl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hδ (by nlinarith)

/-- Li 2000 page 78, second scalar assembly for Lemma 6 part ii. -/
theorem lemma6_ii_N (l δ : ℝ) (hl : 0 < l) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10 ^ 6) :
    (1 + δ) * (10 * (2.08 - 1.19 + 2 * π / 23.4) / (2 * (1.552 - 1.19) * 0.1528)) / l *
      (Real.exp (4.16 * l) - (Real.exp (3.104 * l) - Real.exp (2.38 * l)) / (0.724 * l))
      ≤ 104.8 * (l⁻¹ * (1 - Real.exp (-(4.16 * l)) *
          (Real.exp (3.104 * l) - Real.exp (2.38 * l)) / (0.724 * l))) * Real.exp (4.16 * l) := by
  have hpi := Real.pi_pos
  have hc := (lemma6_ii_coef).2
  have hc0 : (0 : ℝ) ≤ 10 * (2.08 - 1.19 + 2 * π / 23.4) / (2 * (1.552 - 1.19) * 0.1528) := by
    positivity
  exact zd_assembly 4.16 3.104 2.38 0.724 l _ 104.8 δ hl (by norm_num) (by norm_num)
    (by norm_num) hc0 hδ (by nlinarith)

/-- Li 2000 page 79, second scalar assembly for Lemma 6 part iii. -/
theorem lemma6_iii_N (l δ : ℝ) (hl : 0 < l) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10 ^ 6) :
    (1 + δ) * ((1.5 * (0.07 * 1.3656 * (2 * 0.094 + 0.094 ^ 2) * 2.6 ^ 2
        - 0.094 * 2.6 * (2 * 0.07 - 0.07 ^ 2) * 1.3656 ^ 2)
        + 2 * 0.014621 * (0.07 * 1.3656 + 0.094 * 2.6)) /
        (2 * (1.964 - 1.3656) * 0.07 * 0.094 * 1.3656 * 2.6 * 0.26)) / l *
      (Real.exp (5.2 * l) - (Real.exp (3.928 * l) - Real.exp (2.7312 * l)) / (1.1968 * l))
      ≤ 14.91 * (l⁻¹ * (1 - Real.exp (-(5.2 * l)) *
          (Real.exp (3.928 * l) - Real.exp (2.7312 * l)) / (1.1968 * l))) * Real.exp (5.2 * l) :=
  zd_assembly 5.2 3.928 2.7312 1.1968 l _ 14.91 δ hl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hδ (by nlinarith)

/-- Li 2000 page 79, second scalar assembly for Lemma 6 part iv. -/
theorem lemma6_iv_N (l δ : ℝ) (hl : 0 < l) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10 ^ 6) :
    (1 + δ) * (2 * (2.25 - 1.18) / (2 * (1.66 - 1.18) * 0.214)) / l *
      (Real.exp (4.5 * l) - (Real.exp (3.32 * l) - Real.exp (2.36 * l)) / (0.96 * l))
      ≤ 10.42 * (l⁻¹ * (1 - Real.exp (-(4.5 * l)) *
          (Real.exp (3.32 * l) - Real.exp (2.36 * l)) / (0.96 * l))) * Real.exp (4.5 * l) :=
  zd_assembly 4.5 3.32 2.36 0.96 l _ 10.42 δ hl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hδ (by nlinarith)

/-- Li 2000 page 80, second scalar assembly for Lemma 6 part v. -/
theorem lemma6_v_N (l δ : ℝ) (hl : 0 < l) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10 ^ 6) :
    (1 + δ) * ((2.41 - 1.255) / (2 * (1.7825 - 1.255) * 0.2524)) / l *
      (Real.exp (4.82 * l) - (Real.exp (3.565 * l) - Real.exp (2.51 * l)) / (1.055 * l))
      ≤ 4.338 * (l⁻¹ * (1 - Real.exp (-(4.82 * l)) *
          (Real.exp (3.565 * l) - Real.exp (2.51 * l)) / (1.055 * l))) * Real.exp (4.82 * l) :=
  zd_assembly 4.82 3.565 2.51 1.055 l _ 4.338 δ hl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hδ (by nlinarith)

/-- (3.4) and (3.5), p. 77: every printed parameter set of pp. 78-80 satisfies `h₁ < h₂ < h₃`,
`h₂ + h₄ + 3/8 < h₃` and `2h₄ + 3/8 < h₁` (for `N₁*`) or `2h₄ + 3/4 < h₁` (for `N*`). PROVED. -/
theorem lemma6_params :
    ∀ h ∈ ([(0.58, 0.669, 1.08, 0.0353, 3/8), (0.95, 1.042, 1.45, 0.0328, 3/4),
      (0.82, 1.179, 1.71, 0.155, 3/8), (1.19, 1.552, 2.08, 0.1528, 3/4),
      (1.0065, 1.599, 2.25, 0.2759, 3/8), (1.3656, 1.964, 2.6, 0.26, 3/4),
      (0.89, 1.4275, 2.06, 0.2574, 3/8), (1.18, 1.66, 2.25, 0.214, 3/4),
      (0.88, 1.404, 2.032, 0.2524, 3/8), (1.255, 1.7825, 2.41, 0.2524, 3/4),
      (1.334, 1.933, 2.6, 0.291, 3/4)] : List (ℚ × ℚ × ℚ × ℚ × ℚ)),
      h.1 < h.2.1 ∧ h.2.1 < h.2.2.1 ∧ h.2.1 + h.2.2.2.1 + 3 / 8 < h.2.2.1 ∧
        2 * h.2.2.2.1 + h.2.2.2.2 < h.1 := by
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  norm_num

/-- Helper for the two FINDING checks: bounding a product with a `max`. PROVED. -/
theorem mul_max_le_aux (g A B c : ℝ) (hg : 0 ≤ g) (hBA : B ≤ A) (h : g * A ≤ c) :
    g * max A B ≤ c := by rwa [max_eq_left hBA]

/-- Helper: a strict lower bound through `max`. PROVED. -/
theorem lt_mul_max_aux (g A B c : ℝ) (hg : 0 ≤ g) (h : c < g * A) : c < g * max A B :=
  h.trans_le (mul_le_mul_of_nonneg_left (le_max_left A B) hg)

/-- FINDING, p. 78, Section 3 (iii): the printed inequality with `0.1876` FAILS at `a = 6.3`,
the value is `> 0.01465`. PROVED. -/
theorem sec3iii_printed_fails :
    (0.01465 : ℝ) < (1 / 6.3 - 1 / (6.3 + 1) - 2 * (6.3 + 1) / ((6.3 + 1) ^ 2 + 5.8 ^ 2) + 0.1876) *
      max ((6.3 + 1) / 5.8 ^ 2 + 1 / (6.3 + 1)) ((6.3 + 0.618) / 5.8 ^ 2 + 1 / (6.3 + 0.618)) := by
  apply lt_mul_max_aux <;> norm_num

/-- FINDING, p. 78: with Lemma 1's constant `0.18751` in place of `0.1876` the printed
`≤ 0.014621` holds at `a = 6.3`. PROVED. -/
theorem sec3iii_corrected :
    (1 / 6.3 - 1 / (6.3 + 1) - 2 * (6.3 + 1) / ((6.3 + 1) ^ 2 + 5.8 ^ 2) + 0.18751) *
      max ((6.3 + 1) / 5.8 ^ 2 + 1 / (6.3 + 1)) ((6.3 + 0.618) / 5.8 ^ 2 + 1 / (6.3 + 0.618))
      ≤ (0.014621 : ℝ) :=
  mul_max_le_aux _ _ _ _ (by norm_num) (by norm_num) (by norm_num)

/-! ## Section 6, p. 87 -/

/-- (6.3), p. 87, the counting step: for `q ≥ 1` and `T > 0`, the `n ∈ [1, N]` with
`(n, q) > T` number at most `τ(q) N / T`, since each lies in a residue class `0 mod d` for a
divisor `d > T` of `q`. Unit U-1521. -/
theorem gcd_count_le (q N : ℕ) (hq : 0 < q) (T : ℝ) (hT : 0 < T) :
    (((Finset.Icc 1 N).filter (fun n => T < (Nat.gcd n q : ℝ))).card : ℝ) ≤
      (q.divisors.card : ℝ) * N / T := by
  have hI : Finset.Icc 1 N = Finset.Ioc 0 N := by ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hI, mul_comm]
  exact LeanLab.ExceptionalSet.MV75U1423.card_gcd_gt_le N hq hT

/-- ASSEMBLY, (6.3), p. 87: with a divisor bound `τ(q̃) ≤ C N^ε` (a named hypothesis; `q̃ ≤ x^λ`
and `τ(q) ≪ q^ε` give it), `#{n ≤ N : (n, q̃) > N^θ} ≤ C N^{1-θ+ε}`; the paper's
`θ = (1-10^{-4})λ`. -/
theorem eq63 (q N : ℕ) (hq : 0 < q) (hN : 1 ≤ N) (θ ε C : ℝ)
    (hdiv : (q.divisors.card : ℝ) ≤ C * (N : ℝ) ^ ε) :
    (((Finset.Icc 1 N).filter (fun n => (N : ℝ) ^ θ < (Nat.gcd n q : ℝ))).card : ℝ) ≤
      C * (N : ℝ) ^ (1 - θ + ε) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hT := Real.rpow_pos_of_pos hN0 θ
  refine (gcd_count_le q N hq _ hT).trans ?_
  have hsplit : (N : ℝ) ^ (1 - θ + ε) = (N : ℝ) ^ ε * N / (N : ℝ) ^ θ := by
    rw [show 1 - θ + ε = ε + 1 - θ by ring, Real.rpow_sub hN0, Real.rpow_add hN0, Real.rpow_one]
  rw [hsplit]
  have : (q.divisors.card : ℝ) * N / (N : ℝ) ^ θ ≤ C * (N : ℝ) ^ ε * N / (N : ℝ) ^ θ := by
    apply div_le_div_of_nonneg_right _ hT.le
    exact mul_le_mul_of_nonneg_right hdiv hN0.le
  linarith [show C * (N : ℝ) ^ ε * N / (N : ℝ) ^ θ = C * ((N : ℝ) ^ ε * N / (N : ℝ) ^ θ) by ring]

/-- p. 87, case 3, first half: for even `n` and `E ≥ 1`, if `∏_{p | q, p ∤ n} (p - 2) ≤ E` then
`∏_{p | q, p ∤ n} p ≤ 3E²` (all such `p` are odd, `p ≤ 3(p - 2)`, and at most one equals 3).
Unit U-1521. -/
theorem prod_primes_le (q n : ℕ) (hn : Even n) (E : ℝ) (hE : 1 ≤ E)
    (h : ∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ n), ((p : ℝ) - 2) ≤ E) :
    ∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ n), (p : ℝ) ≤ 3 * E ^ 2 := by
  classical
  let s := q.primeFactors.filter (fun p => ¬ p ∣ n)
  have hs : ∀ p ∈ s, p = 3 ∨ 5 ≤ p := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hprime := (Nat.mem_primeFactors.mp hp'.1).1
    have hp2 := hprime.two_le
    have hne : p ≠ 2 := by
      intro he
      apply hp'.2
      rw [he]
      exact even_iff_two_dvd.mp hn
    by_contra hh
    have hp4 : p ≤ 4 := by omega
    interval_cases p <;> norm_num at *
  have hnonneg : ∀ p ∈ s, 0 ≤ (p : ℝ) - 2 := by
    intro p hp
    rcases hs p hp with he | he
    · subst p; norm_num
    · have : (5 : ℝ) ≤ p := by exact_mod_cast he
      linarith
  have hprod : ∏ p ∈ s.erase 3, (p : ℝ) ≤ (∏ p ∈ s.erase 3, ((p : ℝ)-2))^2 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_le_prod₀
    · intro p hp; positivity
    · intro p hp
      obtain ⟨hne, hps⟩ := Finset.mem_erase.mp hp
      have hp5 := (hs p hps).resolve_left hne
      have hp5' : (5 : ℝ) ≤ p := by exact_mod_cast hp5
      nlinarith
  have hbound : ∏ p ∈ s, (p : ℝ) ≤ 3 * (∏ p ∈ s, ((p : ℝ)-2))^2 := by
    by_cases h3 : 3 ∈ s
    · rw [← Finset.mul_prod_erase s (fun p : ℕ => (p : ℝ)) h3,
        ← Finset.mul_prod_erase s (fun p : ℕ => (p : ℝ)-2) h3]
      norm_num
      linarith
    · rw [Finset.erase_eq_of_notMem h3] at hprod
      nlinarith [sq_nonneg (∏ p ∈ s, ((p : ℝ)-2))]
  have hp0 : 0 ≤ ∏ p ∈ s, ((p : ℝ)-2) := Finset.prod_nonneg hnonneg
  change (∏ p ∈ s, (p : ℝ)) ≤ 3 * E^2
  change (∏ p ∈ s, ((p : ℝ)-2)) ≤ E at h
  nlinarith

/-- p. 87, case 3, second half: if `16 ∤ q`, `p² ∤ q` for primes `p ≥ 3`, and `n` is even, then
`q ≤ 4 (n, q) ∏_{p | q, p ∤ n} p`. Unit U-1521. -/
theorem q_le_gcd_mul_prod (q n : ℕ) (hq : 0 < q) (hn : Even n) (h16 : ¬ 16 ∣ q)
    (hsq : ∀ p : ℕ, p.Prime → 3 ≤ p → ¬ p ^ 2 ∣ q) :
    (q : ℝ) ≤ 4 * (Nat.gcd n q : ℝ) * ∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ n), (p : ℝ) := by
  classical
  let s := q.primeFactors.filter (fun p => ¬ p ∣ n)
  have hdiv : q ∣ 4 * Nat.gcd n q * ∏ p ∈ s, p := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2
    intro p k hp hpk
    by_cases hk0 : k = 0
    · simp [hk0]
    have hkp : 1 ≤ k := by omega
    have hpq : p ∣ q := dvd_trans (by simpa using pow_dvd_pow p hkp) hpk
    by_cases hp2 : p = 2
    · subst p
      have hk : k ≤ 3 := by
        by_contra hh
        exact h16 (dvd_trans (by convert pow_dvd_pow (2 : ℕ) (show 4 ≤ k by omega) using 1 <;> norm_num) hpk)
      have hg2 : 2 ∣ Nat.gcd n q := Nat.dvd_gcd (even_iff_two_dvd.mp hn) hpq
      have h8 : 8 ∣ 4 * Nat.gcd n q := by simpa using Nat.mul_dvd_mul_left 4 hg2
      exact dvd_trans (by convert pow_dvd_pow (2 : ℕ) hk using 1 <;> norm_num) (dvd_mul_of_dvd_left h8 _)
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hk : k ≤ 1 := by
        by_contra hh
        exact hsq p hp hp3 (dvd_trans (pow_dvd_pow p (show 2 ≤ k by omega)) hpk)
      have hk1 : k = 1 := by omega
      rw [hk1, pow_one]
      by_cases hpn : p ∣ n
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Nat.dvd_gcd hpn hpq) 4) _
      · have hps : p ∈ s := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpq, hq.ne'⟩, hpn⟩
        exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun p : ℕ => p) hps) _
  have hg0 : 0 < Nat.gcd n q := Nat.gcd_pos_of_pos_right n hq
  have hprod0 : 0 < ∏ p ∈ s, p := Finset.prod_pos (fun p hp => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1.pos)
  have hle := Nat.le_of_dvd (by positivity : 0 < 4 * Nat.gcd n q * ∏ p ∈ s, p) hdiv
  have hreal : (q : ℝ) ≤ ((4 * Nat.gcd n q * ∏ p ∈ s, p : ℕ) : ℝ) := by exact_mod_cast hle
  push_cast at hreal
  simpa [s] using hreal

/-- ASSEMBLY, p. 87, case 3: "there exists `q̃ ≤ 16(n, q̃)/ε²`", with `E = 1/ε`: under the
hypotheses of the two halves, `q̃ ≤ 16 (n, q̃) E²`. -/
theorem qtilde_le (q n : ℕ) (hq : 0 < q) (hn : Even n) (h16 : ¬ 16 ∣ q)
    (hsq : ∀ p : ℕ, p.Prime → 3 ≤ p → ¬ p ^ 2 ∣ q) (E : ℝ) (hE : 1 ≤ E)
    (h : ∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ n), ((p : ℝ) - 2) ≤ E) :
    (q : ℝ) ≤ 16 * (Nat.gcd n q : ℝ) * E ^ 2 := by
  have h1 := q_le_gcd_mul_prod q n hq hn h16 hsq
  have h2 := prod_primes_le q n hn E hE h
  have hg : (0 : ℝ) ≤ Nat.gcd n q := Nat.cast_nonneg _
  have hE2 : 0 ≤ E ^ 2 := sq_nonneg E
  nlinarith

/-- p. 87, before (6.5), the numerical half: for `0 ≤ ε ≤ 10^{-6}`,
`exp(-(2-ε) · 0.005/(0.0862 + ε)) ≤ 0.89048`; at `ε = 0` it is `0.890467`. Unit U-1521. -/
theorem exp_bound_eq64 (ε : ℝ) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 10 ^ 6) :
    Real.exp (-((2 - ε) * 0.005 / (0.0862 + ε))) ≤ 0.89048 := by
  have hd : 0 < 0.0862 + ε := by linarith
  have ht : (0.116 : ℝ) ≤ (2 - ε) * 0.005 / (0.0862 + ε) := by
    rw [le_div_iff₀ hd]
    norm_num at *
    linarith
  refine (Real.exp_le_exp.mpr (neg_le_neg ht)).trans ?_
  rw [Real.exp_neg]
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.116) 5
  norm_num [Finset.sum_range_succ] at hs
  rw [inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  nlinarith

/-- p. 87, before (6.5), the reduction: for `x > 1`, `0 < ε < 1`, `(1-ε)x ≤ n ≤ x`,
`0 ≤ β̃ ≤ 1 - 0.005/((λ+ε) log x)` with `λ = 0.0862`,
`x^{(1-ε)(β̃-1)} n^{β̃} ≤ exp(-(2-ε)·0.005/(λ+ε)) · n/(1-ε)`. Unit U-1521. -/
theorem eq64_reduce (x n β ε : ℝ) (hx : 1 < x) (hε : 0 < ε) (hε1 : ε < 1)
    (hn : (1 - ε) * x ≤ n) (hnx : n ≤ x) (hβ0 : 0 ≤ β)
    (hβ : β ≤ 1 - 0.005 / ((0.0862 + ε) * Real.log x)) :
    x ^ ((1 - ε) * (β - 1)) * n ^ β ≤
      Real.exp (-((2 - ε) * 0.005 / (0.0862 + ε))) * n / (1 - ε) := by
  have hx0 : 0 < x := by linarith
  have he0 : 0 < 1 - ε := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (mul_pos he0 hx0) hn
  have hL : 0 < Real.log x := Real.log_pos hx
  have hd : 0 < 0.0862 + ε := by linarith
  have hmul := mul_le_mul_of_nonneg_right hβ hL.le
  have hcancel : (1 - 0.005 / ((0.0862 + ε) * Real.log x)) * Real.log x =
      Real.log x - 0.005 / (0.0862 + ε) := by field_simp
  rw [hcancel] at hmul
  have hsmall : Real.log x * ((2 - ε) * (β - 1)) ≤ -((2 - ε) * 0.005 / (0.0862 + ε)) := by
    have hm := mul_le_mul_of_nonneg_left (show (β-1)*Real.log x ≤ -(0.005 / (0.0862+ε)) by linarith) (show 0 ≤ 2-ε by linarith)
    convert hm using 1 <;> ring
  have hbase : x ≤ n / (1-ε) := (le_div_iff₀ he0).2 (by nlinarith [hn])
  calc x ^ ((1-ε)*(β-1)) * n^β ≤ x ^ ((1-ε)*(β-1)) * x^β := by
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le hnx hβ0) (by positivity)
    _ = Real.exp (Real.log x * ((2-ε)*(β-1))) * x := by
        rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hx0]
        conv_rhs => arg 2; rw [← Real.exp_log hx0]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-((2-ε)*0.005/(0.0862+ε))) * (n/(1-ε)) := by
        exact mul_le_mul (Real.exp_le_exp.mpr hsmall) hbase hx0.le (Real.exp_pos _).le
    _ = _ := by ring

/-- ASSEMBLY, p. 87: "when `1 - 0.239/((λ+ε) log x) ≤ β̃ ≤ 1 - 0.005/((λ+ε) log x)`,
`x^{(1-ε)(β̃-1)} n^{β̃} ≤ 0.8905 n`", for `0 < ε ≤ 10^{-6}` (lower bound on `β̃` weakened to
`β̃ ≥ 0`). From `exp_bound_eq64` and `eq64_reduce`. -/
theorem eq64 (x n β ε : ℝ) (hx : 1 < x) (hε : 0 < ε) (hε' : ε ≤ 1 / 10 ^ 6)
    (hn : (1 - ε) * x ≤ n) (hnx : n ≤ x) (hβ0 : 0 ≤ β)
    (hβ : β ≤ 1 - 0.005 / ((0.0862 + ε) * Real.log x)) :
    x ^ ((1 - ε) * (β - 1)) * n ^ β ≤ 0.8905 * n := by
  have hε1 : ε < 1 := by linarith [show (1 : ℝ) / 10 ^ 6 < 1 by norm_num]
  have h1 := eq64_reduce x n β ε hx hε hε1 hn hnx hβ0 hβ
  have h2 := exp_bound_eq64 ε hε.le hε'
  have hn0 : 0 < n := by nlinarith
  have h1e : 0 < 1 - ε := by linarith
  refine h1.trans ?_
  rw [div_le_iff₀ h1e]
  have : Real.exp (-((2 - ε) * 0.005 / (0.0862 + ε))) * n ≤ 0.89048 * n :=
    mul_le_mul_of_nonneg_right h2 hn0.le
  nlinarith

/-! ## Vacuity instances: each leaf's hypotheses hold at a concrete point. PROVED. -/

theorem lemma3_a24_vacuity : ∃ l1 l2 ε : ℝ, 0 ≤ l1 ∧ l1 ≤ 0.618 ∧ 0 ≤ l2 ∧ l2 ≤ 0.618 ∧
    0 ≤ ε ∧ ε ≤ 1 / 10 ^ 4 := ⟨0.618, 0.618, 1 / 10 ^ 4, by norm_num⟩

theorem lemma3_a221_vacuity : ∃ l1 l2 ε : ℝ, 0 ≤ l1 ∧ l1 ≤ 0.575 ∧ 0 ≤ l2 ∧ l2 ≤ 0.575 ∧
    0 ≤ ε ∧ ε ≤ 1 / 20000 := ⟨0.575, 0.575, 1 / 20000, by norm_num⟩

theorem lemma3_lambda3_vacuity : ∃ l1 l2 l3 ε : ℝ, 0 ≤ l1 ∧ l1 ≤ l2 ∧ l2 ≤ l3 ∧ l3 < 0.68 ∧
    0 ≤ ε ∧ ε ≤ 1 / 200 := ⟨0.6, 0.65, 0.67, 1 / 200, by norm_num⟩

theorem kernel_anti_vacuity : ∃ a b u w : ℝ, 0 < a ∧ 0 ≤ w ∧ w ≤ a ∧ a ≤ b ∧ |u| ≤ w :=
  ⟨8.4, 9.4, -5.8, 5.8, by norm_num [abs_of_neg]⟩

theorem lemma5_n2_arith_vacuity : ∃ lp n : ℝ, 5 < lp ∧ 0 ≤ n ∧
    n * ((24 + lp) / ((24 + lp) ^ 2 + 23.4 ^ 2)) ≤ 1 / 24 + 0.18752 :=
  ⟨6, 10, by norm_num⟩

theorem bracket_bounds_vacuity : ∃ A B C l : ℝ, 0 < l ∧ C < B ∧ B ≤ A :=
  ⟨4.064, 2.808, 1.76, 0.55, by norm_num⟩

theorem lemma6_i_coef_vacuity : ∃ l : ℝ, 5 < l := ⟨6, by norm_num⟩

theorem gcd_count_le_vacuity : 0 < (6 : ℕ) ∧ (0 : ℝ) < 1 ∧
    2 ∈ (Finset.Icc 1 12).filter (fun n => (1 : ℝ) < (Nat.gcd n 6 : ℝ)) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [Finset.mem_filter, show Nat.gcd 2 6 = 2 by decide]
  norm_num

theorem prod_primes_le_vacuity : Even 2 ∧
    ∏ p ∈ (Nat.primeFactors 3).filter (fun p => ¬ p ∣ 2), ((p : ℝ) - 2) ≤ 1 := by
  refine ⟨even_two, ?_⟩
  rw [Nat.Prime.primeFactors Nat.prime_three, Finset.filter_singleton, ite_eq_left_iff.mpr (fun h => absurd (show ¬ 3 ∣ 2 by decide) h)]
  norm_num

theorem q_le_gcd_mul_prod_vacuity : 0 < 24 ∧ Even 2 ∧ ¬ 16 ∣ 24 ∧
    ∀ p : ℕ, p.Prime → 3 ≤ p → ¬ p ^ 2 ∣ 24 := by
  refine ⟨by norm_num, even_two, by norm_num, fun p hp h3 hd => ?_⟩
  have hle : p ^ 2 ≤ 24 := Nat.le_of_dvd (by norm_num) hd
  have hp5 : p ≤ 4 := by nlinarith
  interval_cases p <;> revert hp h3 hd <;> decide

theorem exp_bound_eq64_vacuity : ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ 1 / 10 ^ 6 := ⟨1 / 10 ^ 6, by norm_num⟩

theorem eq64_reduce_vacuity : ∃ x n β ε : ℝ, 1 < x ∧ 0 < ε ∧ ε < 1 ∧ (1 - ε) * x ≤ n ∧ n ≤ x ∧
    0 ≤ β ∧ β ≤ 1 - 0.005 / ((0.0862 + ε) * Real.log x) := by
  refine ⟨Real.exp 1, Real.exp 1, 0, 1 / 2, ?_⟩
  have he : 1 < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  refine ⟨he, by norm_num, by norm_num, by nlinarith, le_rfl, le_rfl, ?_⟩
  rw [Real.log_exp]
  norm_num

end LeanLab.ExceptionalSet.Li2000Lemmas

#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.lemma3_a24_conclusion
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.lemma5_R0
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.lemma6_i_simplify
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.lemma6_params
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.sec3iii_printed_fails
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.sec3iii_corrected
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.eq63
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.qtilde_le
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.eq64
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.lemma6_v_N1
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.lemma6_ii_coef
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.lemma6_ii_N1
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.gcd_count_le_vacuity
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.prod_primes_le_vacuity
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.q_le_gcd_mul_prod_vacuity
#print axioms LeanLab.ExceptionalSet.Li2000Lemmas.eq64_reduce_vacuity
