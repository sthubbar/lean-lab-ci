/-
Small modulus input and maximal character assembly for the page 17 citation.
The target Decomp542a is not imported.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Orthogonality557
import LeanLab.PNTPort.BVMax.Primes

namespace LeanLab.KumchevLiu2007.Task557b

open Task557a
open scoped BigOperators

/-- LEAF. Davenport chapter 22 pages 132 to 134, used in chapter 28
page 162 before display 2. Siegel Walfisz controls the small moduli.
This is a cited analytic input. The written proof is not in the public preview.
CONDITIONAL. -/
theorem siegel_walfisz_small_moduli : LeanLab.HeathBrown1985.SiegelWalfisz := by
  sorry

#print axioms siegel_walfisz_small_moduli

/-- LEAF. Davenport chapter 28 page 162, the first part of the proof after
 display 2. Reduce residue class maxima to primitive characters, separate small
conductors by Siegel Walfisz, and sum the remaining conductor blocks using
 display 2. This is the psi form with both maxima retained, before conversion
 to prime counting. CONDITIONAL ON the two explicit analytic inputs and the
proved centered character orthogonality and finite conductor normalization. -/
theorem maximal_psi_assembly
    (hOrth : ∀ {q : ℕ} [NeZero q] (T x : ℝ) (a : ℕ),
      0 ≤ x → x ≤ T → Nat.Coprime a q →
      |LeanLab.HeathBrown1985.psi x q a - x / q.totient| ≤
        (∑ χ : DirichletCharacter ℂ q, Task557o.centeredMax T χ) / q.totient)
    (hBlock : ∀ (Q : ℕ) (R : ℝ) (F : ℕ → ℝ), (∀ q, 0 ≤ F q) →
      R * (∑ k ∈ (Finset.range Q).filter (fun k => R ≤ ((k + 1 : ℕ) : ℝ)),
        F (k + 1) / (k + 1).totient) ≤
        ∑ k ∈ Finset.range Q,
          ((k + 1 : ℕ) : ℝ) / (k + 1).totient * F (k + 1))
    (hSW : LeanLab.HeathBrown1985.SiegelWalfisz)
    (hMean : ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → ∀ Q : ℕ, 1 ≤ Q →
      (∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter
          (fun χ => χ.IsPrimitive), primitiveMax x χ) ≤
      K * (x + x ^ (5 / 6 : ℝ) * Q + Real.sqrt x * (Q : ℝ) ^ 2) *
        Real.log (2 * x * Q) ^ 4) :
    LeanLab.PNTPort.BVMax.BombieriVinogradovMax := by
  sorry

#print axioms maximal_psi_assembly

/-- Davenport chapter 28 pages 161 and 162, the maximal psi distribution
bound assembled from the distinct analytic pieces above. CONDITIONAL ON
Siegel Walfisz, the maximal character mean and the conductor assembly. -/
theorem maximal_psi_bv : LeanLab.PNTPort.BVMax.BombieriVinogradovMax := by
  exact maximal_psi_assembly Task557o.maximal_orthogonality Task557o.conductor_block
    siegel_walfisz_small_moduli
    (maximal_character_mean large_sieve vaughan_identity)

#print axioms maximal_psi_bv

end LeanLab.KumchevLiu2007.Task557b
