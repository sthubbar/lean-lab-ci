/-
Upstream large sieve and Vaughan pieces for the page 17 maximal prime input.
Davenport, second edition, chapters 24, 27 and 28.
Source https://doi.org/10.1007/978-1-4757-5927-3_28
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PNTPort.LargeSieve.Bilinear
import LeanLab.PNTPort.BV.Vaughan
import LeanLab.PNTPort.BV.Characters

namespace LeanLab.KumchevLiu2007.Task557a

open ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Davenport chapter 28 page 162 display 2, the maximal character sum.
The inserted zero handles the empty endpoint range. -/
noncomputable def primitiveMax {q : ℕ} (T : ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  sSup (insert 0 {v : ℝ | ∃ x : ℝ, 0 ≤ x ∧ x ≤ T ∧
    v = ‖LeanLab.PNTPort.BV.psiChi x χ‖})

/-- Davenport chapter 28 page 162, the character supremum has a finite
von Mangoldt majorant. Thus its real supremum has no unbounded set artifact. -/
theorem primitiveMax_bddAbove {q : ℕ} (T : ℝ) (χ : DirichletCharacter ℂ q) :
    BddAbove (insert 0 {v : ℝ | ∃ x : ℝ, 0 ≤ x ∧ x ≤ T ∧
      v = ‖LeanLab.PNTPort.BV.psiChi x χ‖}) := by
  refine ⟨∑ n ∈ Finset.Icc 1 ⌊T⌋₊, ArithmeticFunction.vonMangoldt n, ?_⟩
  intro v hv
  rcases Set.mem_insert_iff.mp hv with rfl | hv
  · exact Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  · obtain ⟨x, hx, hxT, rfl⟩ := hv
    unfold LeanLab.PNTPort.BV.psiChi
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
          (DirichletCharacter.norm_le_one _ _)
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊T⌋₊, ArithmeticFunction.vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_right (Nat.floor_le_floor hxT))
          (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)

#print axioms primitiveMax_bddAbove

/-- Davenport chapter 28 page 162, the maximal character norm is nonnegative. -/
theorem primitiveMax_nonneg {q : ℕ} (T : ℝ) (χ : DirichletCharacter ℂ q) :
    0 ≤ primitiveMax T χ :=
  le_csSup (primitiveMax_bddAbove T χ) (Set.mem_insert 0 _)

#print axioms primitiveMax_nonneg

/-- Davenport chapter 28 page 162, every endpoint norm lies below its maximum. -/
theorem primitiveMax_majorizes {q : ℕ} (T x : ℝ) (χ : DirichletCharacter ℂ q)
    (hx : 0 ≤ x) (hxT : x ≤ T) :
    ‖LeanLab.PNTPort.BV.psiChi x χ‖ ≤ primitiveMax T χ := by
  apply le_csSup (primitiveMax_bddAbove T χ)
  exact Set.mem_insert_of_mem 0 ⟨x, hx, hxT, rfl⟩

#print axioms primitiveMax_majorizes

/-- LEAF. Davenport chapter 27 pages 151 to 160, the multiplicative large sieve
used in chapter 28 page 162 display 2. The lab supplies constant N plus 2 Q squared.
This weaker constant has the same strength needed in the chapter 28 argument. -/
theorem large_sieve {Q : ℕ} (hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  exact LeanLab.PNTPort.LargeSieve.multiplicative_large_sieve hQ a M N

#print axioms large_sieve

/-- LEAF. Davenport chapter 24 pages 138 and 139, display 1 and its four
Dirichlet series coefficients. This is the pointwise Vaughan decomposition
used by chapter 28 page 162 after display 2. -/
theorem vaughan_identity (u v : ℕ) (hv : 1 ≤ v) (n : ℕ) (hn : 1 ≤ n) :
    (ArithmeticFunction.vonMangoldt n : ℝ) =
      (if n ≤ u then Λ n else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          ∑ y ∈ x.1.divisorsAntidiagonal, (if y.1 ≤ u ∧ y.2 ≤ v then Λ y.1 * (μ y.2 : ℝ) else 0)
      + ∑ x ∈ n.divisorsAntidiagonal, (if x.1 ≤ v then (μ x.1 : ℝ) * Real.log x.2 else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          (if u < x.1 ∧ v < x.2 then
            Λ x.1 * ∑ d ∈ x.2.divisors, (if d ≤ v then (μ d : ℝ) else 0) else 0) := by
  exact LeanLab.PNTPort.BV.vaughan_identity u v hv n hn

#print axioms vaughan_identity

/-- LEAF. Davenport chapter 28 page 162 display 2, the maximal primitive
character mean estimate. Its proof uses the large sieve and the chapter 24
Vaughan decomposition supplied as explicit inputs. The factor log of 2 x Q
retains a positive logarithm at the endpoints. CONDITIONAL ON these inputs.
The hyperbolic Type II estimate and Type I summation remain OPEN. -/
theorem maximal_character_mean
    (hLS : ∀ {Q : ℕ} (hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ),
    ∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2)
    (hVaughan : ∀ (u v : ℕ) (hv : 1 ≤ v) (n : ℕ) (hn : 1 ≤ n),
    (ArithmeticFunction.vonMangoldt n : ℝ) =
      (if n ≤ u then Λ n else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          ∑ y ∈ x.1.divisorsAntidiagonal, (if y.1 ≤ u ∧ y.2 ≤ v then Λ y.1 * (μ y.2 : ℝ) else 0)
      + ∑ x ∈ n.divisorsAntidiagonal, (if x.1 ≤ v then (μ x.1 : ℝ) * Real.log x.2 else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          (if u < x.1 ∧ v < x.2 then
            Λ x.1 * ∑ d ∈ x.2.divisors, (if d ≤ v then (μ d : ℝ) else 0) else 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → ∀ Q : ℕ, 1 ≤ Q →
      (∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter
          (fun χ => χ.IsPrimitive), primitiveMax x χ) ≤
      K * (x + x ^ (5 / 6 : ℝ) * Q + Real.sqrt x * (Q : ℝ) ^ 2) *
        Real.log (2 * x * Q) ^ 4 := by
  sorry

#print axioms maximal_character_mean

end LeanLab.KumchevLiu2007.Task557a
