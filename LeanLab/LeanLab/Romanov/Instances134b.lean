import LeanLab.Romanov.SigmaBridge134
import LeanLab.Romanov.GeneralBase134

/-!
# Concrete instances for the divisor and SigmaOne bounds

Gallagher pages 126, 134, 135 and 136. HBP v2 page 16, display 27.
These are kernel checks of the plain math twins, with nonzero tuple and divisor weights.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.Romanov.Instances134b

open Finset Real
open LeanLab.Romanov.Decomp134b
open LeanLab.Romanov.TotientWeights134
open LeanLab.Linnik.U1434Lemma21 (sv)

/-- Concrete nonzero divisor weights, masses and the logarithmic moment at three. -/
theorem weight_instances :
    totientWeight 1 = 1 ∧ totientWeight 3 = 1 / 2 ∧ totientWeight 9 = 0 ∧
    oddMass 4 = 1 ∧ oddMass 3 = 3 / 2 ∧ logMoment 3 = log 3 / 2 := by
  have hp4 : (4 : ℕ).primeFactors = {2} :=
    Nat.primeFactors_prime_pow (by decide : 2 ≠ 0) Nat.prime_two
  have hns9 : ¬ Squarefree (9 : ℕ) := by
    intro h
    exact (Nat.squarefree_iff_prime_squarefree.mp h) 3 Nat.prime_three (by decide)
  refine ⟨?_, ?_, totientWeight_zero_of_not_squarefree hns9, ?_, ?_, ?_⟩
  · norm_num [totientWeight, ArithmeticFunction.moebius_apply_one]
  · norm_num [totientWeight, ArithmeticFunction.moebius_apply_prime Nat.prime_three,
      Nat.totient_prime Nat.prime_three]
  · rw [oddMass_eq_prod 4 (by decide), hp4]
    norm_num
  · rw [oddMass_eq_prod 3 (by decide), Nat.prime_three.primeFactors]
    norm_num
  · rw [odd_log_moment_eq 3 (by decide), oddMass_eq_prod 3 (by decide), Nat.prime_three.primeFactors]
    norm_num
    ring

/-- The residue counts use ordered tuples, and the actual SigmaOne example is positive. -/
theorem tuple_instances :
    #{μ ∈ Icc 1 4 | 2 ^ μ % 3 = 1} = 2 ∧
    #{ν : Fin 2 → Fin 2 | sv ν % 3 = 0} = 2 ∧
    sigmaOne 9 36 1 = 3 ∧ Nat.log 2 (36 / (2 * 9)) = 1 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  have hphi : Nat.totient 18 = 6 := by decide +kernel
  norm_num [sigmaOne, sv, hphi]

/-- General base admissibility has an actual representation with prime five and base three. -/
theorem general_base_instance : Nat.Coprime 11 3 ∧ Nat.Coprime 9 2 := by
  have h := LeanLab.Romanov.GeneralBase134.general_base_admissibility 3 2 5
    (by decide) (by decide) (by decide) (fun _ => 1) (fun _ => le_rfl)
  convert h using 1 <;> norm_num

/-- The common logarithmic cutoff at exponent zero is nonempty and has weight one. -/
theorem cutoff_instance :
    LeanLab.Romanov.SigmaBridge134.cutoff 6 0 = {1} ∧
      (∑ q ∈ LeanLab.Romanov.SigmaBridge134.cutoff 6 0, totientWeight q) = 1 := by
  have h : LeanLab.Romanov.SigmaBridge134.cutoff 6 0 = {1} := by
    norm_num [LeanLab.Romanov.SigmaBridge134.cutoff, LeanLab.LPZ2007.OddSqf]
  exact ⟨h, by rw [h]; simpa using weight_instances.1⟩

end LeanLab.Romanov.Instances134b
