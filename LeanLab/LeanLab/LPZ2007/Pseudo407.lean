import LeanLab.LPZ2007.Halasz407

/-!
The finite Euler product behind Jutila 1977 page 49, Lemma 3.
DOI https://doi.org/10.7146/math.scand.a-11701.
For psi of p equal to one minus p, each off diagonal local factor vanishes.
This file proves the finite product identity before any Dirichlet series argument.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.Pseudo407

open Finset

/-- Jutila 1977 page 49, Lemma 3, the finite Euler product calculation.
This is the product side of sum h of d over d equal to the diagonal totient.
It makes no assertion about a contour integral or convergence. -/
theorem pseudcharacter_euler_orthogonality {r r' : ℕ}
    (hr : Squarefree r) (hr' : Squarefree r') :
    (∏ p ∈ r.primeFactors ∪ r'.primeFactors,
      (1 + (if p ∈ r.primeFactors ∧ p ∈ r'.primeFactors
        then ((1 - (p : ℝ)) ^ 2 - 1) else -(p : ℝ)) / p)) =
      if r = r' then (r.totient : ℝ) else 0 := by
  classical
  by_cases heq : r = r'
  · subst r'
    rw [if_pos rfl, union_self]
    calc
      _ = ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := by
        apply prod_congr rfl
        intro p hp
        rw [if_pos ⟨hp, hp⟩]
        have hp0 : (p : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
        field_simp
        ring
      _ = (r.totient : ℝ) := by
        rw [Nat.totient_eq_div_primeFactors_mul,
          Nat.prod_primeFactors_of_squarefree hr, Nat.div_self (Nat.pos_of_ne_zero hr.ne_zero), one_mul,
          Nat.cast_prod]
        apply prod_congr rfl
        intro p hp
        rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
        norm_num
  · rw [if_neg heq]
    have hsets : r.primeFactors ≠ r'.primeFactors := by
      intro h
      apply heq
      rw [← Nat.prod_primeFactors_of_squarefree hr,
        ← Nat.prod_primeFactors_of_squarefree hr', h]
    have hex : ∃ p ∈ r.primeFactors ∪ r'.primeFactors,
        ¬ (p ∈ r.primeFactors ∧ p ∈ r'.primeFactors) := by
      by_contra h
      push_neg at h
      apply hsets
      ext p
      constructor
      · intro hp
        exact (h p (mem_union_left _ hp)).2
      · intro hp
        exact (h p (mem_union_right _ hp)).1
    obtain ⟨p, hp, hbad⟩ := hex
    apply prod_eq_zero hp
    rw [if_neg hbad]
    have hprime : p.Prime := by
      rcases mem_union.mp hp with h | h
      · exact Nat.prime_of_mem_primeFactors h
      · exact Nat.prime_of_mem_primeFactors h
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hprime.ne_zero
    field_simp
    ring

/-- Jutila 1977 page 49, Lemma 3, with coefficients indexed by prime subsets.
Expanding the finite Euler product gives the diagonal totient identity.
The product of primes in a subset is the corresponding squarefree divisor. -/
theorem pseudcharacter_kernel_sum {r r' : ℕ}
    (hr : Squarefree r) (hr' : Squarefree r') :
    (∑ u ∈ (r.primeFactors ∪ r'.primeFactors).powerset,
      (∏ p ∈ u, (if p ∈ r.primeFactors ∧ p ∈ r'.primeFactors
        then ((1 - (p : ℝ)) ^ 2 - 1) else -(p : ℝ))) /
        (∏ p ∈ u, (p : ℝ))) =
      if r = r' then (r.totient : ℝ) else 0 := by
  have h := pseudcharacter_euler_orthogonality hr hr'
  rw [Finset.prod_one_add] at h
  simpa only [Finset.prod_div_distrib] using h

/-- Jutila 1977 page 49, Lemma 3, the absolute coefficient bound.
Prime subsets index the nonzero coefficients of the finite Euler polynomial.
No squarefree assumption on the two moduli is needed for this product bound. -/
theorem pseudcharacter_kernel_absolute (r r' : ℕ) :
    (∑ u ∈ (r.primeFactors ∪ r'.primeFactors).powerset,
      |∏ p ∈ u, (if p ∈ r.primeFactors ∧ p ∈ r'.primeFactors
        then ((1 - (p : ℝ)) ^ 2 - 1) else -(p : ℝ))|) ≤
      (∏ p ∈ r.primeFactors, ((p : ℝ) + 1)) *
        (∏ p ∈ r'.primeFactors, ((p : ℝ) + 1)) := by
  classical
  let A := r.primeFactors
  let B := r'.primeFactors
  let c : ℕ → ℝ := fun p => if p ∈ A ∧ p ∈ B
    then (1 - (p : ℝ)) ^ 2 - 1 else -(p : ℝ)
  change (∑ u ∈ (A ∪ B).powerset, |∏ p ∈ u, c p|) ≤ _
  simp_rw [Finset.abs_prod]
  rw [← Finset.prod_one_add]
  have hlocal : ∀ p ∈ A ∪ B, 1 + |c p| ≤
      (if p ∈ A then (p : ℝ) + 1 else 1) *
        (if p ∈ B then (p : ℝ) + 1 else 1) := by
    intro p hp
    have hprime : p.Prime := by
      rcases mem_union.mp hp with h | h
      · exact Nat.prime_of_mem_primeFactors h
      · exact Nat.prime_of_mem_primeFactors h
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    by_cases hA : p ∈ A <;> by_cases hB : p ∈ B
    · have hc : 0 ≤ (1 - (p : ℝ)) ^ 2 - 1 := by nlinarith
      simp only [c, hA, hB, and_self, if_true, abs_of_nonneg hc]
      nlinarith
    · simp [c, hA, hB, abs_of_nonneg (show (0 : ℝ) ≤ p from Nat.cast_nonneg p), add_comm]
    · simp [c, hA, hB, abs_of_nonneg (show (0 : ℝ) ≤ p from Nat.cast_nonneg p), add_comm]
    · exact (False.elim ((mem_union.mp hp).elim hA hB))
  calc
    _ ≤ ∏ p ∈ A ∪ B,
        ((if p ∈ A then (p : ℝ) + 1 else 1) *
          (if p ∈ B then (p : ℝ) + 1 else 1)) :=
      Finset.prod_le_prod₀ (fun _ _ => by positivity) hlocal
    _ = (∏ p ∈ A, ((p : ℝ) + 1)) * (∏ p ∈ B, ((p : ℝ) + 1)) := by
      rw [prod_mul_distrib]
      congr 1
      · rw [prod_union_eq_left (fun p hp hnot => if_neg hnot)]
        apply prod_congr rfl
        intro p hp
        rw [if_pos hp]
      · rw [prod_union_eq_right (fun p hp hnot => if_neg hnot)]
        apply prod_congr rfl
        intro p hp
        rw [if_pos hp]

end LeanLab.LPZ2007.Pseudo407

#print axioms LeanLab.LPZ2007.Pseudo407.pseudcharacter_euler_orthogonality

#print axioms LeanLab.LPZ2007.Pseudo407.pseudcharacter_kernel_sum

#print axioms LeanLab.LPZ2007.Pseudo407.pseudcharacter_kernel_absolute
