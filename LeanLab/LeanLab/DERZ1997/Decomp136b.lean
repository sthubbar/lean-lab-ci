/-
P0011 page 100, Section 2, positivity of the weighted prime-triple count.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.DERZ1997.Statements

namespace LeanLab.DERZ1997.Decomp136b

/-- P0011 page 100, the finite set of ordered prime triples in equation 1. -/
noncomputable def primeTriples (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (N + 1)).product
    ((Finset.range (N + 1)).product (Finset.range (N + 1)))).filter
      (fun t => t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧ t.1 + t.2.1 + t.2.2 = N)

/-- P0011 page 100, J counts ordered triples with logarithmic weights. -/
noncomputable def weightedJ (N : ℕ) : ℝ :=
  ∑ t ∈ primeTriples N, Real.log t.1 * Real.log t.2.1 * Real.log t.2.2

/-- LEAF. P0011 page 100, equation 1 and the definition of J.
Membership in the finite support is exactly an ordered prime representation. -/
theorem mem_primeTriples (N : ℕ) (t : ℕ × ℕ × ℕ) :
    t ∈ primeTriples N ↔
      t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧ t.1 + t.2.1 + t.2.2 = N := by
  rcases t with ⟨p, q, r⟩
  simp only [primeTriples, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨by omega, by omega, by omega⟩, h⟩

/-- LEAF. P0011 page 100, all logarithmic weights in J are positive. -/
theorem weight_pos (N : ℕ) (t : ℕ × ℕ × ℕ) (ht : t ∈ primeTriples N) :
    0 < Real.log t.1 * Real.log t.2.1 * Real.log t.2.2 := by
  obtain ⟨hp, hq, hr, _⟩ := (mem_primeTriples N t).mp ht
  exact mul_pos (mul_pos
    (Real.log_pos (by exact_mod_cast hp.one_lt))
    (Real.log_pos (by exact_mod_cast hq.one_lt)))
    (Real.log_pos (by exact_mod_cast hr.one_lt))

/-- LEAF. P0011 page 100, the sentence after J, via positivity of a finite sum. -/
theorem weightedJ_pos_iff_nonempty (N : ℕ) :
    0 < weightedJ N ↔ (primeTriples N).Nonempty := by
  unfold weightedJ
  rw [Finset.sum_pos_iff_of_nonneg (fun t ht => (weight_pos N t ht).le)]
  constructor
  · rintro ⟨t, ht, _⟩
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, ht, weight_pos N t ht⟩

/-- P0011 page 100, the sentence after J, assembled without a sorry in this proof. -/
theorem ternary_of_weightedJ_pos (N : ℕ) (hJ : 0 < weightedJ N) : IsTernarySum N := by
  obtain ⟨t, ht⟩ := (weightedJ_pos_iff_nonempty N).mp hJ
  exact ⟨t.1, t.2.1, t.2.2, (mem_primeTriples N t).mp ht⟩

/-- The paper allows 2 in each prime coordinate. -/
example : (2, 2, 2) ∈ primeTriples 6 := by
  rw [mem_primeTriples]
  norm_num

/-- A concrete positive weighted count. -/
example : 0 < weightedJ 6 := by
  apply (weightedJ_pos_iff_nonempty 6).mpr
  refine ⟨(2, 2, 2), ?_⟩
  rw [mem_primeTriples]
  norm_num

end LeanLab.DERZ1997.Decomp136b
