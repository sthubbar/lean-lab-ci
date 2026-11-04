/-
Partial decomposition of P0079, arXiv 0811.3663v2, pages 4 to 12.
AI wrote this Lean code. Goldbach is open.
The threshold sign QUESTION is not an input leaf here.
-/
import LeanLab.LZPowersOfTwo.Statements

open Real Finset MeasureTheory Filter

noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 4, the common exponent cutoff. -/
def cutoff293 (s : ℕ) (μ : ℕ → ℝ) (ε X : ℝ) : ℝ :=
  logb 2 (ε * X / (2 * ∑ i : Fin s, |μ i|))

/-- P0079 page 4, the additive character. -/
def character293 (u : ℝ) : ℂ := Complex.exp ((2 * Real.pi * u : ℝ) * Complex.I)

/-- P0079 page 4, the prime exponential sum. -/
def primeSum293 (ε X α : ℝ) : ℂ :=
  ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
    (Real.log p : ℂ) * character293 ((p : ℝ) * α)

/-- P0079 page 4, the powers of two exponential sum. -/
def powerSum293 (L α : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 ⌊L⌋₊, character293 (2 ^ m * α)

/-- P0079 page 4, the kernel with its continuous value at zero. -/
def kernel293 (η α : ℝ) : ℝ := (η * Real.sinc (Real.pi * η * α)) ^ 2

/-- P0079 page 4, the integrand defining I. -/
def integrand293 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X α : ℝ) : ℂ :=
  primeSum293 ε X (l1 * α) * primeSum293 ε X (l2 * α) *
    (∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)) *
    character293 (γ * α) * kernel293 η α

/-- P0079 page 4, display 14, the major arc. -/
def major293 (X : ℝ) : Set ℝ := {α | |α| ≤ X ^ (1 / 3 : ℝ) / X}

/-- P0079 page 4, display 14, the minor arc. -/
def minor293 (X L : ℝ) : Set ℝ := {α | X ^ (1 / 3 : ℝ) / X < |α| ∧ |α| ≤ L ^ 2}

/-- P0079 page 4, display 14, the trivial arc. -/
def trivial293 (X L : ℝ) : Set ℝ := (major293 X ∪ minor293 X L)ᶜ

/-- LEAF. P0079 page 4, displays 11 to 13. Fourier expansion bounds the full
integral by the weighted number of solutions. No irrationality input is used. -/
theorem count_integral293 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X : ℝ)
    (hη : 0 < η) (hε : 0 < ε) (hX : 2 ≤ X) :
    Integrable (integrand293 s l1 l2 μ γ η ε X) ∧
    (∫ α : ℝ, integrand293 s l1 l2 μ γ η ε X α).re ≤
      η * (log X) ^ 2 * NX l1 l2 (fun i : Fin s => μ i) γ η ε X := by
  sorry

/-- LEAF. P0079 page 9, displays 33 to 35. This is only the major arc estimate.
It makes no assertion about the sign of the final major minus minor coefficient. -/
theorem major_lower293 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ᶠ X : ℝ in atTop,
      (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 * X * (cutoff293 s μ ε X) ^ s ≤
        (∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α).re := by
  sorry

/-- LEAF. P0079 page 10, Section 5, display 17. The trivial arc is little o
of X times L to the power s. The tolerance is explicit. -/
theorem trivial_small293 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : l1 ≠ 0) (h2 : l2 ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in trivial293 X (cutoff293 s μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
        δ * X * (cutoff293 s μ ε X) ^ s := by
  sorry

/-- LEAF. P0079 pages 11 to 12, displays 40 to 43 and their conclusions.
The two cases share the estimate. A positive tolerance absorbs the little o term.
This leaf does not assert display 19 or the disputed endpoint implication. -/
theorem minor_upper293 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in minor293 X (cutoff293 s μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
        (ν ^ (s - 2) * Cq r1.den r2.den + δ) * η * X * (cutoff293 s μ ε X) ^ s := by
  sorry

end LeanLab.LZPowersOfTwo
