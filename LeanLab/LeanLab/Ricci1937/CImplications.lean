import LeanLab.Ricci1937.TheoremsCD

/-!
Ricci 1937, page 83, the reduction of Theorem C part 1 to part 2.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every prime multiplicity is at most the total number of prime factors. -/
lemma factorization_le_length (x p : ℕ) : x.factorization p ≤ x.primeFactorsList.length := by
  rw [← Nat.primeFactorsList_count_eq]
  exact List.count_le_length

/-- Page 83: the exponent at s = 3g is exactly one third. -/
lemma c2_exponent_three_mul {g : ℕ} (hg : 1 ≤ g) :
    (((3 * g : ℕ) : ℝ) - g) / (2 * (3 * g : ℕ)) = (1 : ℝ) / 3 := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  push_cast
  field_simp
  ring

/-- Page 83: the factor bound at s = 3g is exactly 3g - 1. -/
lemma c2_bound_three_mul {g : ℕ} (hg : 1 ≤ g) :
    (2 * (3 * g) * g - 1) / (3 * g - g) = 3 * g - 1 := by
  have hden : 3 * g - g = 2 * g := by omega
  rw [hden]
  have hnum : 2 * (3 * g) * g - 1 + 1 = 2 * (3 * g) * g := by
    have : 0 < 2 * (3 * g) * g := by positivity
    omega
  have hk : 3 * g - 1 + 1 = 3 * g := by omega
  apply Nat.div_eq_of_lt_le
  · nlinarith
  · rw [hk]
    nlinarith

/-- The two predicates agree at s = 3g. The exponent restriction is automatic. -/
lemma c1_iff_c2_three_mul {g n x : ℕ} (hg : 1 ≤ g) :
    AlmostGT (3 * g - 1) (((n : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) x ↔
      AlmostGT ((2 * (3 * g) * g - 1) / (3 * g - g))
        (((n : ℕ) : ℝ) ^ ((((3 * g : ℕ) : ℝ) - g) / (2 * (3 * g : ℕ)))) x ∧
      ∀ p ∈ x.primeFactors, x.factorization p < 3 * g := by
  rw [c2_bound_three_mul hg, c2_exponent_three_mul hg]
  constructor
  · intro h
    exact ⟨h, fun p _ => lt_of_le_of_lt (factorization_le_length x p)
      (lt_of_le_of_lt h.2.1 (by omega))⟩
  · exact And.left

/-- The counted sets agree, so both sides of the count estimate transfer. -/
lemma c1_count_eq_c2_three_mul (P : Polynomial ℤ) (hP : CHyp P) (ξ : ℕ) :
    #{n ∈ Icc (1 : ℕ) ξ | AlmostGT (3 * P.natDegree - 1)
        (((n : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) (Fval P n)} =
    #{n ∈ Icc (1 : ℕ) ξ | AlmostGT
        ((2 * (3 * P.natDegree) * P.natDegree - 1) / (3 * P.natDegree - P.natDegree))
        (((n : ℕ) : ℝ) ^ ((((3 * P.natDegree : ℕ) : ℝ) - P.natDegree) /
          (2 * (3 * P.natDegree : ℕ)))) (Fval P n) ∧
        ∀ p ∈ (Fval P n).primeFactors, (Fval P n).factorization p < 3 * P.natDegree} := by
  congr 1
  ext n
  simp only [mem_filter]
  rw [c1_iff_c2_three_mul hP.1]

/-- Page 83. CONDITIONAL ON Theorem C part 2. -/
theorem theoremC1_of_C2 (hC2 : TheoremC2) : TheoremC1 := by
  intro P hP
  obtain ⟨a₁, a₂, ha₁, ha₂, a₃, h⟩ :=
    hC2 P hP (3 * P.natDegree) (by have := hP.1; omega) le_rfl
  refine ⟨a₁, a₂, ha₁, ha₂, a₃, fun ξ hξ => ?_⟩
  simpa only [c1_count_eq_c2_three_mul P hP ξ] using h ξ hξ

/-- The polynomial hypotheses have the concrete instance P = X. -/
example : CHyp (Polynomial.X : Polynomial ℤ) := by
  refine ⟨by simp, Polynomial.monic_X.isPrimitive, Polynomial.irreducible_X, by simp⟩

example : (2 * (3 * 1) * 1 - 1) / (3 * 1 - 1) = (2 : ℕ) := by norm_num

example : (15 : ℕ).factorization 3 ≤ (15 : ℕ).primeFactorsList.length :=
  factorization_le_length 15 3

end
end LeanLab.Ricci1937
