/-
P0069 page 7 display 2.5 and the following S2 replacement leading to 2.6.
Independent split of the long and short coefficient replacements.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561m

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

/-- P0069 page 7 display 2.5, replace only the long polynomial by its principal model.
The short polynomial still has its actual coefficients and rational phase. -/
noncomputable def longPrincipal561 (ε D x : ℝ) (b : ℕ → ℂ) (u : ℝ) (N : ℕ) : ℂ :=
  u / Real.log x *
    ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
      (ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ) *
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
            (Real.log x ^ (4 * D) / (q * length512 ε x)),
            polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) t *
            polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b ((r : ℝ) / q + t) *
            @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + t) : ℝ) : AddCircle (1 : ℝ))

/-- P0069 page 7 display 2.5, the long coefficient replacement error alone. -/
noncomputable def longReplacementError561 (ε D x : ℝ) (a b : ℕ → ℂ) (u : ℝ) : ℝ :=
  ∑ N ∈ frequencies512 ε x,
    ‖(∫ t in major512 ε D x, integrand512 ε x a b N t) - longPrincipal561 ε D x b u N‖ ^ 2

/-- P0069 page 7 following 2.5, the short coefficient replacement error alone. -/
noncomputable def shortReplacementError561 (ε D x : ℝ) (b : ℕ → ℂ) (u v : ℝ) : ℝ :=
  ∑ N ∈ frequencies512 ε x,
    ‖longPrincipal561 ε D x b u N - principalArc512 ε D x u v N‖ ^ 2

/-- P0069 page 7 display 2.5 and its S2 analogue, the combined coefficient error. -/
noncomputable def coefficientReplacementError512 (ε D x : ℝ)
    (a b : ℕ → ℂ) (u v : ℝ) : ℝ :=
  ∑ N ∈ frequencies512 ε x,
    ‖(∫ t in major512 ε D x, integrand512 ε x a b N t) - principalArc512 ε D x u v N‖ ^ 2

/-- LEAF. P0069 page 7 display 2.5, long coefficient replacement only.
Use the prefix distribution of a, its rough support, the Gauss evaluation and
partial summation. The short polynomial keeps its actual coefficient b and
only its divisor bound is assumed. Decomp561g proves the additive twist step.
No distribution or moving window estimate for b is required in this input. OPEN. -/
theorem leaf_long_coefficient561 :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (a b : ℝ → ℕ → ℂ) (u : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
          ‖∑ k ∈ (I x).filter (fun k : ℕ => (k : ℝ) ≤ t),
            (a x k * χ (k : ZMod q) - delta χ * u / Real.log x)‖ ≤ C * Y x * Real.log x ^ (-A)) →
      (∃ C : ℝ, ∀ x k, ‖a x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B ∧
        ‖b x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
        Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0) →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          longReplacementError561 ε D x (a x) (b x) u ≤ C * scale512 ε A x := by
  sorry

/-- LEAF. P0069 page 7 after display 2.5, short coefficient replacement only.
The long polynomial is already the explicit principal model. Use the prefix
distribution of b, its divisor bound and partial summation. The rational
character expansion must account for the nonunit residue classes. This is
not the large modulus local S2 estimate on page 9. No exceptional set or
moving window input is assumed here. OPEN. -/
theorem leaf_short_coefficient561 :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (b : ℝ → ℕ → ℂ) (u v : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let J : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊Y x⌋₊ ⌊2 * Y x⌋₊
      (∃ C : ℝ, ∀ x k, ‖b x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ 2 * Y x →
          ‖∑ m ∈ (J x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            (b x m * χ (m : ZMod q) - delta χ * v / Real.log (Y x))‖ ≤
              C * Y x * Real.log x ^ (-A)) →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          shortReplacementError561 ε D x (b x) u v ≤ C * scale512 ε A x := by
  sorry

/-- P0069 page 7 display 2.5 and its S2 replacement, exact expanded coefficient conclusion.
CONDITIONAL ON the separate long and short coefficient inputs. -/
theorem major_coefficients561 :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
  ∀ (a b : ℝ → ℕ → ℂ) (u v : ℝ) (E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)),
    let θ₁ : ℝ := 11 / 20 + ε
    let θ₂ : ℝ := 2 * (1 / 16 - 1 / 10 ^ 5)
    let Y : ℝ → ℝ := fun x => x ^ θ₁
    let Q : ℝ → ℕ := fun x => ⌊(Y x ^ θ₂) ^ (1 / 2 : ℝ) / 2⌋₊
    let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
    let J : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊Y x⌋₊ ⌊2 * Y x⌋₊
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
        ‖∑ k ∈ (I x).filter (fun k : ℕ => (k : ℝ) ≤ t),
          (a x k * χ (k : ZMod q) - delta χ * u / Real.log x)‖ ≤ C * Y x * Real.log x ^ (-A)) →
    (∃ C : ℝ, ∀ x k, ‖a x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B ∧
      ‖b x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
      Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0) →
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ 2 * Y x →
        ‖∑ m ∈ (J x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (b x m * χ (m : ZMod q) - delta χ * v / Real.log (Y x))‖ ≤
            C * Y x * Real.log x ^ (-A)) →
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ Q x →
      ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
      ∀ z : ℝ, (q * Q x : ℝ) / (6 * Y x) ≤ z → z ≤ 6 * q * Q x / Y x →
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
          ∫ y in (Y x / 2)..(3 * Y x),
            ‖∑ m ∈ (J x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m * χ (m : ZMod q) - delta χ * v / Real.log (Y x))‖ ^ 2 ≤
          C * ((q : ℝ) * Q x) ^ 2 * Y x * Real.log x ^ (-A)) →
    ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
      ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
        coefficientReplacementError512 ε D x (a x) (b x) u v ≤ C * scale512 ε A x := by
  intro B
  obtain ⟨ε₁, hε₁, hlong⟩ := leaf_long_coefficient561 B
  obtain ⟨ε₂, hε₂, hshort⟩ := leaf_short_coefficient561 B
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro ε hε he a b u v E
  dsimp only
  intro h1 h2 h3 h4 _h5 A hA
  have hL := hlong ε hε (lt_of_lt_of_le he (min_le_left _ _)) a b u h1 h2 h3 A hA
  have hb : ∃ C : ℝ, ∀ x k, ‖b x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B := by
    obtain ⟨C, hC⟩ := h2
    exact ⟨C, fun x k => (hC x k).2⟩
  have hS := hshort ε hε (lt_of_lt_of_le he (min_le_right _ _)) b u v hb h4 A hA
  apply combine_eventual561 ε A
    (fun D x => longReplacementError561 ε D x (a x) (b x) u)
    (fun D x => shortReplacementError561 ε D x (b x) u v)
    (fun D x => coefficientReplacementError512 ε D x (a x) (b x) u v) hL hS
  intro D x
  exact two_error_mean_square561 _ _ _ _

end LeanLab.BHP1997.Decomp561n
