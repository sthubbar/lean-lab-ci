/-
Concrete hypothesis instances for the task577 helpers.
Hu 2019 pages 194 and 195. Rieger 1968 page 94.
These are instance checks, not analytic input proofs.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp577c
import LeanLab.Hathi2021.Decomp577f

open Finset Real MeasureTheory Set
open LeanLab.Hathi2021.Decomp319a LeanLab.Hathi2021.Decomp570b
open LeanLab.Hathi2021.Decomp577a LeanLab.Hathi2021.Decomp577d
open LeanLab.Hathi2021.Decomp577e

example : (squarePrimes 0 0) = ∅ := by norm_num [squarePrimes]

example : collisionCount 0 0 = 0 := by
  have hP : squarePrimes 0 0 = ∅ := by norm_num [squarePrimes]
  simp [collisionCount, hP]

example : offDiagonalEnergy 0 0 = 0 := by
  have hP : squarePrimes 0 0 = ∅ := by norm_num [squarePrimes]
  simp [offDiagonalEnergy, hP]

example : pairFrequency (3, 5) = 34 := by norm_num [pairFrequency]

example : 0 < pairWeight (3, 3) := by
  dsimp [pairWeight]
  exact mul_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

example : ((Finset.univ : Finset (ZMod 3)).filter (fun x => x ^ 2 = 1)).card = 2 := by decide

example (N : ℕ) : ∃ n₁ n₂ : ℕ,
    Odd n₁ ∧ Odd n₂ ∧ N ≤ n₂ ∧ n₂ < n₁ ∧ (n₁ : ℝ) ≤ 2 * n₂ := by
  exact pair_domain_unbounded 2 (by norm_num) N

example : ∃ n₁ : ℕ, (exceptionalSlice n₁ 0).Nonempty := by
  obtain ⟨N, hN⟩ := exceptionalSlice_eventually_nonempty
  exact ⟨N, hN N le_rfl⟩

example :
    (∫ z in ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ (univ : Set (ℝ × ℝ))) ∩
      {z | z.1 ∈ (univ : Set ℝ)}, (1 : ℝ) * 1 * 1 * 1) ≤
      (1 : ℝ) * Real.sqrt (∫ x in Icc (0 : ℝ) 1, (1 : ℝ) ^ 2) * Real.sqrt 1 *
        Real.sqrt (∫ y in Icc (0 : ℝ) 1, (1 : ℝ) ^ 2) *
        Real.sqrt (∫ y in Icc (0 : ℝ) 1, (1 : ℝ) ^ 2) := by
  apply sectional_cauchy_bound (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    continuous_const continuous_const continuous_const continuous_const
    (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num)
    MeasurableSet.univ MeasurableSet.univ (by norm_num)
  · intro x hx
    exact le_rfl
  · intro y hy
    norm_num [Real.volume_real_Icc]
