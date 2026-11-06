/- AI wrote this Lean code for CODEX task406. Goldbach is open.
Nonempty domains for the sharp sieve bridge and finite dyadic cover. -/
import LeanLab.BS2022GRH.Decomp406b
import LeanLab.BS2022GRH.Instances374
import LeanLab.BS2022GRH.Decomp406d

namespace LeanLab.BS2022GRH.Instances406
open Real Finset Classical ChenThresholdGRH Decomp148a Decomp374a
noncomputable section

/-- A nonzero vector with two coefficients satisfies the sparse sieve domain, display 15. -/
theorem sparse_domain :
    ({1, 2} : Finset ℕ) ⊆ Ioc 0 2 ∧
      (∑ n ∈ ({1, 2} : Finset ℕ), ‖(1 : ℂ)‖ ^ 2) = 2 := by
  norm_num [Finset.subset_iff]

/-- Both supports and the primitive character block are nonempty, journal p. 1225. -/
theorem energy_domain :
    (blockCharacters 2).Nonempty ∧
      1 ∈ (nRange 25).filter (fun n => Nat.Coprime n 1) ∧
      29 ∈ (pRange 30 25).filter (fun p => ¬ p ∣ 1) ∧
      (∀ n : ℕ, ‖(1 : ℂ)‖ ≤ 1) := by
  refine ⟨Instances374.block_characters_two_nonempty, ?_, ?_, ?_⟩
  · norm_num [nRange]
  · norm_num [pRange]
  · simp

/-- The cover has a nonempty support and a nonzero weight, journal p. 1225. -/
theorem cover_domain :
    (5 : ℝ) ≤ 10 ∧ (1 : ℝ) < 5 ∧ (5 : ℝ) ≤ 10 ∧
      6 ∈ (Ico 3 ⌈(10 : ℝ)⌉₊).filter (fun r : ℕ => (5 : ℝ) < r) ∧
      (∀ r : ℕ, (0 : ℝ) ≤ 1) ∧
      0 ∈ range ⌈log ((10 : ℝ) / max 5 2) / log 2⌉₊ := by
  have hl : log (2 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  norm_num [hl]

/-- The first source primorial used in Robin's reduction is thirty, p. 380. -/
theorem primeProduct_three : Decomp406c.primeProduct 3 = 30 := by
  norm_num [Decomp406c.primeProduct, prod_range_succ]

/-- The nontrivial Robin comparison and both source index ranges have instances, p. 380. -/
theorem robin_domain :
    3 ≤ (30 : ℕ) ∧ 3 ≤ (30 : ℕ).primeFactors.card ∧
      3 ≤ (3 : ℕ) ∧ (3 : ℕ) ≤ 12 ∧ 13 ≤ (13 : ℕ) := by
  decide +kernel

/-- A removed prime and a positive cofactor occur together, journal p. 1224. -/
theorem deletion_domain :
    29 ∈ (pRange 30 25).filter (fun p => p ∣ 29) ∧
      1 ≤ (29 : ℕ) ∧ (5 : ℝ) ≤ 30 ∧ ((29 : ℕ) : ℝ) < 30 := by
  norm_num [pRange]

end
end LeanLab.BS2022GRH.Instances406

#print axioms LeanLab.BS2022GRH.Instances406.sparse_domain
#print axioms LeanLab.BS2022GRH.Instances406.energy_domain
#print axioms LeanLab.BS2022GRH.Instances406.cover_domain

#print axioms LeanLab.BS2022GRH.Instances406.primeProduct_three
#print axioms LeanLab.BS2022GRH.Instances406.robin_domain
#print axioms LeanLab.BS2022GRH.Instances406.deletion_domain
