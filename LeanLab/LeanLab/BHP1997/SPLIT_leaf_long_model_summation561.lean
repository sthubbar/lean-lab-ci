/-
Split of theorem leaf_long_model_summation561 in
LeanLab.BHP1997.SPLIT_leaf_long_prefix_replacement561: the collection of the
single-arc budgets over the moduli of the major arcs of the long coefficient
replacement.  The double sum over the arcs is first written as the sum of the
individual arc errors, the operator norm of that sum is bounded by the sum of
the norms, and the per-arc budgets are then collected: the number of reduced
residues of a modulus cancels against the totient weight, the moduli are counted
by the cutoff, and the surplus logarithmic saving pays for both.  When the short
block is shorter than half a unit the block carries no mass at all and the whole
summation is vacuous.
AI wrote the Lean code.  Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_long_prefix_replacement561

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

set_option autoImplicit false

/-- LEAF: Telescoping step.  The principal model is, by its definition, the sum
over the same range of moduli and reduced residues of the model term multiplied by
the Moebius weight over the totient of the modulus and by the constant of the
principal density.  Subtracting that sum from the double sum of the actual arc
integrals and distributing the constant over the inner sum leaves exactly one
arc error per modulus and reduced residue.  This is an identity in the complex
numbers, with no analytic input and no side condition. -/
theorem leaf_long_model_difference561 (ε D x u : ℝ) (a b : ℝ → ℕ → ℂ) (N : ℕ) :
    (∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊, (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), (∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..(Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)))) -
      longPrincipal561 ε D x (b x) u N =
      ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), ((∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..(Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
            (∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..(Real.log x ^ (4 * D) / (q * length512 ε x)),
              polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
              polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x)
                ((r : ℝ) / q + s) *
              @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ))))) := by
  sorry

/-- LEAF: Triangle step.  The norm of the sum of the single arc errors is at most
the sum of their norms, and each of those is at most the per-arc budget supplied
by the single arc replacement, applied at that modulus and that reduced residue.
The moduli range over the cutoff of the model sum and the reduced residues over
the arc range of their modulus, so the passage from the index of a modulus to its
real value needs the nonnegativity of the arc parameter.  No coefficient
information enters. -/
theorem leaf_long_model_norm_le561 (ε D x u A C₀ : ℝ) (a b : ℝ → ℕ → ℂ) (N : ℕ)
    (hA : 0 < A) (hD : 0 ≤ D)
    (h : ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ (2 * D) →
        ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), ‖((∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..(Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
            (∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..(Real.log x ^ (4 * D) / (q * length512 ε x)),
              polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
              polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x)
                ((r : ℝ) / q + s) *
              @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ))))‖ ≤ (C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
            (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) *
            (∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖))) :
    ‖∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊, (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), ((∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..(Real.log x ^ (4 * D) / (q * length512 ε x)),
            integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s)) -
          (u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
            (∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..(Real.log x ^ (4 * D) / (q * length512 ε x)),
              polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) s *
              polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x)
                ((r : ℝ) / q + s) *
              @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + s) : ℝ) : AddCircle (1 : ℝ)))))‖ ≤
      ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), (C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
            (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) *
            (∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖))) := by
  sorry

/-- LEAF: Moduli collection step.  If the short block is at least half a unit long
and the block position is at least eight, then the double sum of the per-arc
budgets over all moduli up to the cutoff is at most the constant of the
conclusion times the required logarithmic saving times the mass of the short
block.  The residue count cancels the reciprocal of the modulus, the cutoff
bounds the number of moduli, and the surplus saving absorbs that power of the
logarithm.  Elementary summation and power arithmetic only. -/
theorem leaf_long_model_budget_collection561 (ε D x A C₀ : ℝ) (b : ℝ → ℕ → ℂ)
    (hA : 0 < A) (hD : 0 ≤ D) (hx : 8 ≤ x) (hY : 1 / 2 ≤ length512 ε x) :
    (∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), (C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
            (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) *
            (∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖)))) ≤
      max 1 C₀ * Real.log x ^ (-A) * (∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖) := by
  sorry

/-- LEAF: Degenerate block step.  If the block length is below one half then both
floors of the block range are zero, the range of indices of the short block is
empty, and the mass of the short block vanishes identically.  This is the case in
which the summation over the moduli is vacuous and no saving has to be paid
for. -/
theorem leaf_long_model_mass_degenerate561 (ε x : ℝ) (b : ℝ → ℕ → ℂ)
    (hY : length512 ε x < 1 / 2) :
    (∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖) = 0 := by
  sorry

/-- The modulus summation of the long coefficient replacement, assembled from the
telescoping identity, the triangle step, the collection of the per-arc budgets
and the degenerate block step.  The threshold of the conclusion is eight.
CONDITIONAL ON those four separate inputs. -/
theorem leaf_long_model_summation561_split (ε D : ℝ) (hD : 0 ≤ D) :
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
  refine ⟨8, ?_⟩
  intro x hx a b u A C₀ N hA hord hN hhyp
  have hD0 : (0 : ℝ) ≤ D := hD
  rw [leaf_long_model_difference561 ε D x u a b N]
  by_cases hY : (1 / 2 : ℝ) ≤ length512 ε x
  · exact le_trans
      (leaf_long_model_norm_le561 ε D x u A C₀ a b N hA hD0
        (fun q hq hqL r hr => hhyp q hq hqL r hr))
      (leaf_long_model_budget_collection561 ε D x A C₀ b hA hD0 hx hY)
  · have hM0 : (∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖) = 0 :=
      leaf_long_model_mass_degenerate561 ε x b (lt_of_not_ge hY)
    refine le_trans
      (leaf_long_model_norm_le561 ε D x u A C₀ a b N hA hD0
        (fun q hq hqL r hr => hhyp q hq hqL r hr)) ?_
    simp [hM0]

end LeanLab.BHP1997.Decomp561n
