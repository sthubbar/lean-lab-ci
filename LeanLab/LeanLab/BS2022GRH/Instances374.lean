/- AI wrote this Lean code for CODEX task374. Goldbach is open.
Concrete nonempty domains for the new journal proof leaves. -/
import LeanLab.BS2022GRH.Decomp374a
import LeanLab.BS2022GRH.Decomp374b
import LeanLab.BS2022GRH.Decomp374d
import LeanLab.BS2022GRH.Decomp374f
import LeanLab.BS2022GRH.Decomp374g

namespace LeanLab.BS2022GRH.Instances374
open Real Finset Classical ChenThresholdGRH Decomp148a
noncomputable section

/-- A nonempty dyadic modulus block in display 15, journal p. 1225. -/
theorem block_two : Decomp374a.blockModuli 2 = {3} := by
  ext r
  norm_num [Decomp374a.blockModuli]

/-- There are nonprincipal complex characters modulo three, journal p. 1224. -/
theorem nonprincipal_three : ∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 := by
  have hc : Fintype.card (DirichletCharacter ℂ 3) = 2 := by
    rw [← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ 3]
    norm_num [Nat.totient_prime Nat.prime_three]
  exact Fintype.exists_ne_of_one_lt_card (by omega) 1

/-- The dyadic primitive character index set is nonempty, journal display 15. -/
theorem block_characters_two_nonempty : (Decomp374a.blockCharacters 2).Nonempty := by
  obtain ⟨χ, hχ⟩ := nonprincipal_three
  have hp : χ.IsPrimitive := by
    rcases (Nat.dvd_prime Nat.prime_three).mp χ.conductor_dvd_level with h | h
    · exact False.elim (hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
    · exact h
  refine ⟨⟨3, χ⟩, ?_⟩
  simp only [Decomp374a.blockCharacters, mem_sigma, mem_filter, mem_univ, true_and]
  exact ⟨by rw [block_two]; simp, hp⟩

/-- A prime in the character sum domain, journal p. 1224. -/
theorem prime_interval_nonempty : 29 ∈ pRange 30 25 := by
  norm_num [pRange]

/-- Every scalar domain guard in the conductor assemblies holds together, pp. 1224 to 1226. -/
theorem conductor_domain :
    (25 : ℝ) ≤ 25 ∧ (25 : ℝ) ≤ 100 ∧ (25 : ℝ) ≤ 36 ∧ (36 : ℝ) < 100 ∧
    (1 : ℝ) < 10 ∧ (10 : ℝ) < √(25 * 100) ∧ (1 : ℝ) < 5 ∧ (5 : ℝ) ≤ 10 ∧
    (5 : ℝ) ≤ √36 ∧ √(25 * 100) / 10 ≤ (5 : ℝ) ∧ Even (2 : ℤ) ∧
    (∀ n : ℕ, ‖(1 : ℂ)‖ ≤ 1) := by
  norm_num

/-- Both conductor ranges and the cofactor support have members, journal displays 13 and 16. -/
theorem conductor_support_nonempty :
    3 ∈ (conductors 10 2).filter (fun r : ℕ => (r : ℝ) ≤ 5) ∧
    7 ∈ (conductors 10 2).filter (fun r : ℕ => (5 : ℝ) < r) ∧
    1 ∈ moduli 10 2 := by
  have h7 : Squarefree (7 : ℕ) := (by norm_num : Nat.Prime 7).squarefree
  norm_num [conductors, moduli, Nat.prime_three.squarefree, h7]

/-- The boundary correction can have both endpoints prime, journal p. 1224. -/
theorem boundary_domain :
    (25 : ℝ) ≤ 29 ∧ (29 : ℝ) < 31 ∧ Nat.Prime 29 ∧ Nat.Prime 31 := by
  norm_num

/-- The large weighted prime domain has an even natural witness, journal Lemma 14. -/
theorem weighted_domain_nonempty : ∃ n : ℕ, Even n ∧ exp (exp 10) ≤ (n : ℝ) ∧
    (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by
  obtain ⟨n, hev, hn⟩ := threshold_nonvacuous
  have hN : exp (exp 10) ≤ (n : ℝ) :=
    (exp_le_exp.mpr (exp_le_exp.mpr (by norm_num : (10 : ℝ) ≤ 13.375))).trans hn
  exact ⟨n, hev, hN, by norm_num, by norm_num⟩

end
end LeanLab.BS2022GRH.Instances374
#print axioms LeanLab.BS2022GRH.Instances374.block_two
#print axioms LeanLab.BS2022GRH.Instances374.nonprincipal_three
#print axioms LeanLab.BS2022GRH.Instances374.block_characters_two_nonempty
#print axioms LeanLab.BS2022GRH.Instances374.prime_interval_nonempty
#print axioms LeanLab.BS2022GRH.Instances374.conductor_domain
#print axioms LeanLab.BS2022GRH.Instances374.conductor_support_nonempty
#print axioms LeanLab.BS2022GRH.Instances374.boundary_domain
#print axioms LeanLab.BS2022GRH.Instances374.weighted_domain_nonempty
