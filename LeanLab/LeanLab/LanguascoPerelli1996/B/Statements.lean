/-
Merged copy, PC run 20261020T0503Z-11094, unit U-1179: the repo encoding of P0071 moved under the
namespace LeanLab.LanguascoPerelli1996.B in LanguascoPerelli1996/B, so it builds beside the OneDrive
encoding, which BHP1997, BG2026 and Languasco2004 import. Content unchanged apart from names.
P0071 A. Languasco and A. Perelli, "A pair correlation hypothesis and the exceptional set in
Goldbach's problem", Mathematika 43 (1996), 349-361. Read 2026-10-18 from the open published
copy research.unipd.it/bitstream/11577/122141/1/[3].pdf, pages 349 to 351, formulas taken from
the rendered page images, not the OCR text.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Every result of the paper here assumes GRH and the hypothesis GMC(θ).

Encoding of `≪`: a bound `F ≪ G` becomes `∃ C X₀, ∀ X ≥ X₀, F ≤ C G`, with the stated
uniformity in the other variables; `≪_ε` puts `∀ ε > 0` in front of `∃ C X₀`.
Zeros of `L(s, χ)` in the open critical strip are counted with multiplicity by
`analyticOrderNatAt`, as in `GoldbachAverage/ZeroSums.lean`. The pair sum is a `tsum` over pairs
of zeros cut to `|γ| ≤ T`; that set is finite, so the `tsum` is a finite sum.
GRH is `LeanLab.DERZ1997.GRH`: every zero of every Dirichlet `L(s, χ)` in `0 < Re s < 1`
has `Re s = 1/2`.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.DERZ1997.Statements

namespace LeanLab.LanguascoPerelli1996.B
open Complex Finset Real
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### The exceptional set -/

/-- The even `n` in `[X, X+H]` that are not sums of two primes. -/
def Eset (X H : ℝ) : Finset ℕ :=
  (Finset.range (⌊X + H⌋₊ + 1)).filter
    (fun n => X ≤ n ∧ (n : ℝ) ≤ X + H ∧ Even n ∧ ¬ IsGoldbachSum n)

/-- The paper's `E(X, H) = |{2n ∈ [X, X+H] : 2n is not a sum of two primes}|`, page 350. -/
def E (X H : ℝ) : ℕ := (Eset X H).card

/-! ### The pair correlation function for Dirichlet `L`-functions, page 349 -/

/-- Montgomery's weight `w(u) = 4 / (4 + u²)`. -/
def w (u : ℝ) : ℝ := 4 / (4 + u ^ 2)

/-- `e(x) = exp(2πix)`. -/
def e (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- Nontrivial zeros of `L(s, χ)`: zeros in the open strip `0 < Re s < 1`. -/
def ZeroL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Type :=
  {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- `∑_{|γ₁|, |γ₂| ≤ T} X^{i(γ₁ - γ₂)} w(γ₁ - γ₂)`, over zeros `1/2 + iγⱼ` of `L(s, χⱼ)`
with multiplicity. Under GRH every zero in the strip is `1/2 + iγ`, so `γ = Im ρ`. -/
def pairSum (X T : ℝ) {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) : ℂ :=
  ∑' p : ZeroL χ₁ × ZeroL χ₂,
    if |p.1.1.im| ≤ T ∧ |p.2.1.im| ≤ T then
      (analyticOrderNatAt (DirichletCharacter.LFunction χ₁) p.1.1 : ℂ) *
        (analyticOrderNatAt (DirichletCharacter.LFunction χ₂) p.2.1 : ℂ) *
        (X : ℂ) ^ (Complex.I * ((p.1.1.im - p.2.1.im : ℝ) : ℂ)) *
        (w (p.1.1.im - p.2.1.im) : ℂ)
    else 0

/-- The Gauss sum `τ(χ) = ∑_{a mod q} χ(a) e(a/q)`. -/
def tau {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ := gaussSum χ ZMod.stdAddChar

/-- `F` AS PRINTED, page 349: `∑_{χ₁, χ₂} χ₁(a) χ̄₂(a) τ(χ̄₁) τ(χ₂) ∑ X^{i(γ₁-γ₂)} w(γ₁-γ₂)`.
A `def` only since audit U-1010, run 20261019T0202Z-9877, F-0046. -/
def FPrinted (X T : ℝ) (q : ℕ) [NeZero q] (a : ℕ) : ℂ :=
  ∑ χ₁ : DirichletCharacter ℂ q, ∑ χ₂ : DirichletCharacter ℂ q,
    χ₁ (a : ZMod q) * (starRingEnd ℂ) (χ₂ (a : ZMod q)) * tau χ₁⁻¹ * tau χ₂ * pairSum X T χ₁ χ₂

/-- `F(X, T; q, a)` as the paper's identity (11), page 354, defines it: the factor of `χ₂` is
`conj(τ(χ̄₂)) = χ₂(-1) τ(χ₂)`, not the printed `τ(χ₂)`, F-0046. Changed by audit U-1010, run
20261019T0202Z-9877: GMC for the printed F is a weaker hypothesis than the proofs use, so the
cited Theorem 3 with it claimed more than the paper proves. The conjugate character `χ̄` is `χ⁻¹`. -/
def F (X T : ℝ) (q : ℕ) [NeZero q] (a : ℕ) : ℂ :=
  ∑ χ₁ : DirichletCharacter ℂ q, ∑ χ₂ : DirichletCharacter ℂ q,
    χ₁ (a : ZMod q) * (starRingEnd ℂ) (χ₂ (a : ZMod q)) * tau χ₁⁻¹ * (starRingEnd ℂ) (tau χ₂⁻¹) *
      pairSum X T χ₁ χ₂

/-- GMC(θ), page 350: assume GRH; for every `ε > 0`, `F(X, T; q, a) ≪_ε q² T X^ε` uniformly for
`V ≤ T ≤ X`, `q ≤ X^θ`, `(a, q) = 1`, where `V = X^{1-θ} / q`. The paper fixes
`θ ∈ (0, 1/2]`; the range is a hypothesis of each theorem below. -/
def GMC (θ : ℝ) : Prop :=
  DERZ1997.GRH ∧ ∀ ε : ℝ, 0 < ε → ∃ C X₀ : ℝ, ∀ (X T : ℝ) (q : ℕ) [NeZero q] (a : ℕ),
    X₀ ≤ X → X ^ (1 - θ) / q ≤ T → T ≤ X → (q : ℝ) ≤ X ^ θ → a.Coprime q →
      ‖F X T q a‖ ≤ C * (q : ℝ) ^ 2 * T * X ^ ε

/-! ### The mean square `I(X, Q; q, a)`, page 350 -/

/-- `S(α) = ∑_{X ≤ n ≤ 2X} Λ(n) e(nα)`. -/
def S (X α : ℝ) : ℂ := ∑ n ∈ Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊, (Λ n : ℂ) * e (n * α)

/-- `T(α) = ∑_{X ≤ n ≤ 2X} e(nα)`. -/
def Tsum (X α : ℝ) : ℂ := ∑ n ∈ Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊, e (n * α)

/-- `R(η; q, a) = S(a/q + η) - μ(q)/φ(q) T(η)`. -/
def R (X η : ℝ) (q a : ℕ) : ℂ :=
  S X ((a : ℝ) / q + η) - ((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * Tsum X η

/-- `I(X, Q; q, a) = ∫_{-1/qQ}^{1/qQ} |R(η; q, a)|² dη`. -/
def I (X Q : ℝ) (q a : ℕ) : ℝ :=
  ∫ η in (-(1 / (q * Q)))..(1 / (q * Q)), ‖R X η q a‖ ^ 2

/-- Hypothesis (5) with exponent `ε` and constant `C`, for one `X` and `Q`:
`I(X, Q; q, a) ≤ C X^{1+ε} / (qQ)` for all `1 ≤ q ≤ Q` and `(a, q) = 1`. -/
def Hyp5 (ε C X Q : ℝ) : Prop :=
  ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ Q → a.Coprime q → I X Q q a ≤ C * X ^ (1 + ε) / (q * Q)

/-! ### The paper's results, cited -/

/-- Theorem 2, page 350: assume GRH; let `ε > 0` and `X^ε ≤ Q ≤ X^{1/2}/2`, and assume (5)
uniformly for `q ≤ Q`, `(a, q) = 1`. Then `E(X, 4Q²) ≪_ε X^ε`. The constant of the conclusion
may depend on `ε` and on the constant `C` of (5). -/
def Theorem2 : Prop :=
  DERZ1997.GRH → ∀ ε : ℝ, 0 < ε → ∀ C : ℝ, ∃ C' X₀ : ℝ, ∀ X Q : ℝ, X₀ ≤ X →
    X ^ ε ≤ Q → Q ≤ X ^ ((1 : ℝ) / 2) / 2 → Hyp5 ε C X Q → (E X (4 * Q ^ 2) : ℝ) ≤ C' * X ^ ε

/-- Theorem 3, page 351: let `θ ∈ (0, 1/2]`, `Q = X^θ / 2` and assume GMC(θ). Then (5) holds
uniformly for `q ≤ Q`, `(a, q) = 1`: for every `ε > 0` there are `C, X₀` with (5) for `X ≥ X₀`. -/
def Theorem3 (θ : ℝ) : Prop :=
  GMC θ → ∀ ε : ℝ, 0 < ε → ∃ C X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → Hyp5 ε C X (X ^ θ / 2)

/-- Corollary 1, first assertion: GMC(θ) gives `E(X, X^{2θ}) ≪_ε X^ε`. -/
def Cor1a (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → (E X (X ^ (2 * θ)) : ℝ) ≤ C * X ^ ε

/-- Corollary 1, second assertion: `E(X) = E(X, X) ≪_ε X^{1-2θ+ε}`. -/
def Cor1b (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → (E X X : ℝ) ≤ C * X ^ (1 - 2 * θ + ε)

/-- Cited. P0071 Theorem 2, by the method of Kaczorowski-Perelli-Pintz. -/
theorem lp_theorem2 : Theorem2 := by sorry

/-- Cited. P0071 Theorem 3. -/
theorem lp_theorem3 (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ 1 / 2) : Theorem3 θ := by sorry

end

end LeanLab.LanguascoPerelli1996.B


