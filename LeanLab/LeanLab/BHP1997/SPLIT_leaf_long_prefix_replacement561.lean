/-
Independent split of the single frequency replacement of the long polynomial by its
principal model.  The major arc integral is written as the sum of its Farey arcs, the
modulus cutoff of the major arcs is dominated by the Farey order, a single arc is
compared with the corresponding model term at a cost of a logarithmic saving times the
window width, and the resulting modulus sum is collected with the elementary harmonic
bound.  The main term of each arc is the mass of the short block.
AI wrote the Lean code.  Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_long_coefficient561

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

/-- LEAF. Arc decomposition step.  The integrand is a finite sum of characters of the
circle, hence one periodic; the Farey arcs of the major arcs are eventually pairwise
disjoint, of width below the separation of neighbouring fractions with that denominator
cut, and every arc that leaves the fundamental period of the circle re-enters it shifted
by one.  Consequently the integral over the major arcs is the double sum over the
moduli and the reduced residues of the integral over the symmetric local arc around the
centre of that arc, in the local variable of the arc.  No distribution hypothesis and no
coefficient information is used. -/
theorem leaf_long_arc_decomposition561 (ε D : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ (a b : ℝ → ℕ → ℂ) (N : ℕ),
      (∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) =
        ∑ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
          ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
                (Real.log x ^ (4 * D) / (q * length512 ε x)),
              integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s) := by
  sorry

/-- LEAF. Order domination step.  The Farey order of the major arcs grows like the
square root of a positive power of the block length, while the modulus cutoff of the
major arcs is a fixed power of the logarithm; from some point on the order is at least
the cutoff, so that the union of arcs is taken over the full range of the model sum.
This is an elementary threshold on `x`, uniform in the arc parameter. -/
theorem leaf_long_order_domination561 (ε D : ℝ) (hD : 0 ≤ D) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ⌊Real.log x ^ (2 * D)⌋₊ ≤ order512 ε x := by
  sorry

/-- LEAF. Single arc replacement step.  On one reduced arc of the major arcs, the
actual long polynomial may be replaced by its principal model: the character expansion
of the phase at the centre of the arc, the prefix distribution of the long coefficients
against the characters of that modulus, the rough support that makes the coefficients
coprime to the modulus, and the total variation of the weight coming from the short
polynomial.  The cost is an arbitrary logarithmic saving times the width of the arc
times the mass of the short block, and it is uniform in the modulus and in the reduced
residue.  The saving is charged at an exponent strictly larger than the one required
later, which is what makes the modulus sum converge. -/
theorem leaf_long_arc_model_replacement561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (a b : ℝ → ℕ → ℂ) (u : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
          ‖∑ k ∈ (I x).filter (fun k : ℕ => (k : ℝ) ≤ t),
            (a x k * χ (k : ZMod q) - delta χ * u / Real.log x)‖ ≤ C * Y x * Real.log x ^ (-A)) →
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
        Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0) →
      ∀ A : ℝ, 0 < A → ∃ C₀ : ℝ, ∀ x : ℝ, C₀ ≤ x → ∀ D : ℝ, 0 ≤ D →
        ∀ N ∈ frequencies512 ε x, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ (2 * D) →
        ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        ‖(∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
            ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
              polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
              polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x)
                ((r : ℝ) / q + s) *
              @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ))‖ ≤
          C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
            (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) *
            ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
  sorry

/-- LEAF. Modulus summation step.  If every single arc is within a logarithmic saving
times the width of the arc times the mass of the short block of its model term, then the
double sum over the moduli and the reduced residues is within a fixed constant times the
required saving times the mass of the short block.  There are at most one power of the
logarithm per unit of the arc parameter many moduli, the reduced residue count cancels
against the totient weight of the model, and the extra saving charged per arc pays for
both.  Elementary summation and power arithmetic only. -/
theorem leaf_long_model_summation561 (ε D : ℝ) (hD : 0 ≤ D) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ (a b : ℝ → ℕ → ℂ) (u A C₀ : ℝ) (N : ℕ),
      0 < A →
      ⌊Real.log x ^ (2 * D)⌋₊ ≤ order512 ε x →
      N ∈ frequencies512 ε x →
      (∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ (2 * D) →
        ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        ‖(∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
            ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
              polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
              polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x)
                ((r : ℝ) / q + s) *
              @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ))‖ ≤
          C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
            (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) *
            ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖) →
      ‖(∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
          ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
                (Real.log x ^ (4 * D) / (q * length512 ε x)),
              integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          longPrincipal561 ε D x (b x) u N‖ ≤
        max 1 C₀ * Real.log x ^ (-A) *
          ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
  sorry

/-- The single frequency long coefficient replacement, assembled from the arc
decomposition, the order domination, the single arc replacement and the modulus
summation.  CONDITIONAL ON those four separate inputs. -/
theorem leaf_long_prefix_replacement561_split :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (a b : ℝ → ℕ → ℂ) (u : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
          ‖∑ k ∈ (I x).filter (fun k : ℕ => (k : ℝ) ≤ t),
            (a x k * χ (k : ZMod q) - delta χ * u / Real.log x)‖ ≤ C * Y x * Real.log x ^ (-A)) →
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
        Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0) →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ N ∈ frequencies512 ε x,
          ‖(∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) -
              longPrincipal561 ε D x (b x) u N‖ ≤
            C * Real.log x ^ (-A) *
              ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
  obtain ⟨εR, hεR, hrep⟩ := leaf_long_arc_model_replacement561
  obtain ⟨εL, hεL, hlen⟩ := leaf_long_length_bounds561
  refine ⟨min εR εL, lt_min hεR hεL, ?_⟩
  intro ε hε hεlt a b u
  dsimp only
  intro hdist hrough A hA
  have hεR' : ε < εR := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hεL' : ε < εL := lt_of_lt_of_le hεlt (min_le_right _ _)
  obtain ⟨Xl, hXl⟩ := hlen ε hε hεL'
  obtain ⟨C₀, hC₀⟩ := hrep ε hε hεR' a b u hdist hrough A hA
  refine ⟨0, fun D hD => ?_⟩
  have hD0 : (0 : ℝ) ≤ D := hD
  obtain ⟨Xa, hXa⟩ := leaf_long_arc_decomposition561 ε D
  obtain ⟨Xo, hXo⟩ := leaf_long_order_domination561 ε D hD0
  obtain ⟨Xs, hXs⟩ := leaf_long_model_summation561 ε D hD0
  refine ⟨max (max (max (max Xa Xo) (max Xl C₀)) Xs + 3) (max 1 C₀), fun x hx => ?_⟩
  intro N hN
  have hthr : max (max (max Xa Xo) (max Xl C₀)) Xs + 3 ≤ x := le_trans (le_max_left _ _) hx
  have hthr' : max (max (max Xa Xo) (max Xl C₀)) Xs ≤ x := by linarith
  have hM1 : max (max Xa Xo) (max Xl C₀) ≤ x := le_trans (le_max_left _ _) hthr'
  have hAB : max Xa Xo ≤ x := le_trans (le_max_left _ _) hM1
  have hxa : Xa ≤ x := le_trans (le_max_left _ _) hAB
  have hxo : Xo ≤ x := le_trans (le_max_right _ _) hAB
  have hCD : max Xl C₀ ≤ x := le_trans (le_max_right _ _) hM1
  have hxl : Xl ≤ x := le_trans (le_max_left _ _) hCD
  have hxp : C₀ ≤ x := le_trans (le_max_right _ _) hCD
  have hxs : Xs ≤ x := le_trans (le_max_right _ _) hthr'
  obtain ⟨hL1, hlog1, -⟩ := hXl x hxl
  have hord : ⌊Real.log x ^ (2 * D)⌋₊ ≤ order512 ε x := hXo x hxo
  have hid : (∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) =
      ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s) := by
    rw [hXa x hxa a b N, min_eq_right hord]
  rw [hid]
  have hlogpos : 0 < Real.log x := by linarith
  have hM0 : (0 : ℝ) ≤
      ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ :=
    Finset.sum_nonneg (fun m _ => norm_nonneg _)
  refine le_trans (hXs x hxs a b u A C₀ N hA hord hN
    (fun q hq hqL r hr => hC₀ x hxp D hD0 N hN q hq hqL r hr)) ?_
  apply mul_le_mul_of_nonneg_right _ hM0
  exact mul_le_mul_of_nonneg_right (le_max_right _ _)
    (Real.rpow_nonneg (le_of_lt hlogpos) _)

end LeanLab.BHP1997.Decomp561n
