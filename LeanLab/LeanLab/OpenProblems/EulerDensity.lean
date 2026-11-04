import LeanLab.OpenProblems.State1612

/-!
# Elementary counting support for the Euler density targets

AI wrote the Lean code. The two sealed density targets remain OPEN in the lab.
Goldbach remains OPEN. No density conclusion follows from infinitude alone.

Source: https://www.primepuzzles.net/conjectures/conj_068.htm,
the opening Euler conjecture and Emmanuel Vantieghem's representation formula.
This HTML page has no page numbers. The counting identities below are elementary
consequences of the sealed exception count, rather than quoted analytic results.
-/

namespace LeanLab.OpenProblems.State1612

/-- The exception count cannot exceed the number of indices tested. -/
theorem euExc_le (X : ℕ) : euExc X ≤ X := by
  classical
  unfold euExc
  simpa using (Finset.card_filter_le (Finset.Icc 1 X) (fun n => ¬ IsEuler (8 * n + 3)))

/-- Subtracting exceptions counts exactly the represented indices from one through X. -/
theorem represented_count_eq (X : ℕ) :
    X - euExc X = ({n : ℕ | IsEuler (8 * n + 3)} ∩ Set.Icc 1 X).ncard := by
  classical
  have hset : {n : ℕ | IsEuler (8 * n + 3)} ∩ Set.Icc 1 X =
      (↑((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3))) : Set ℕ) := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc,
      Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    tauto
  rw [hset, Set.ncard_coe_finset]
  have h := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 X)
    (fun n => IsEuler (8 * n + 3))
  have hcard : (Finset.Icc 1 X).card = X := by simp
  rw [hcard] at h
  unfold euExc
  omega

/-- Taking the square to be one gives a represented index whenever 4n + 1 is prime. -/
theorem isEuler_of_four_mul_add_one_prime {n : ℕ} (hp : (4 * n + 1).Prime) :
    IsEuler (8 * n + 3) := by
  exact ⟨1, 4 * n + 1, by decide, hp, by ring⟩

/-- There are infinitely many represented indices, using primes congruent to one modulo four.
This gives no positive density bound. -/
theorem euler_represented_infinite : {n : ℕ | IsEuler (8 * n + 3)}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro B
  obtain ⟨p, hp, hB, hm⟩ := Nat.exists_prime_gt_modEq_one (k := 4) (4 * B + 5) (by decide)
  have hmod : p % 4 = 1 := hm
  refine ⟨p / 4, ?_, by omega⟩
  have heq : 4 * (p / 4) + 1 = p := by omega
  exact isEuler_of_four_mul_add_one_prime (heq.symm ▸ hp)

/-- CONDITIONAL on the stated almost-all bound. That bound implies positive lower density.
The input is explicit and neither sealed sorry theorem is used. -/
theorem positive_density_of_almost_all {E : ℕ → ℕ} (hle : ∀ X, E X ≤ X)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in Filter.atTop, (E X : ℝ) ≤ ε * X) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop, c * X ≤ ((X - E X : ℕ) : ℝ) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [h (1 / 2) (by norm_num)] with X hX
  rw [Nat.cast_sub (hle X)]
  linarith

end LeanLab.OpenProblems.State1612

#print axioms LeanLab.OpenProblems.State1612.euExc_le
#print axioms LeanLab.OpenProblems.State1612.represented_count_eq
#print axioms LeanLab.OpenProblems.State1612.isEuler_of_four_mul_add_one_prime
#print axioms LeanLab.OpenProblems.State1612.euler_represented_infinite

#print axioms LeanLab.OpenProblems.State1612.positive_density_of_almost_all
