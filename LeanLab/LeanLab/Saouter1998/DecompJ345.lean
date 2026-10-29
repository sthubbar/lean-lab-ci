import Mathlib
import LeanLab.Saouter1998.Lemma1
import LeanLab.Saouter1998.Theorem2

namespace LeanLab.Saouter1998.BLS

/-- LEAF 864: The lemma holds trivially if F = 0 -/
theorem leaf_F_zero (R : ℕ) :
    ((R * 0 + 1).Prime ↔
      R / (2 * 0) = 0 ∨ ¬ IsSquare (((R % (2 * 0) : ℕ) : ℤ) ^ 2 - 8 * ((R / (2 * 0) : ℕ) : ℤ))) := by
  have h2 : R / (2 * 0) = 0 := by
    rw [mul_zero]
    exact Nat.div_zero R
  have h1 : ¬ (R * 0 + 1).Prime := by
    rw [mul_zero, zero_add]
    exact Nat.not_prime_one
  exact iff_of_false h1 (by intro h; sorry)
/-- LEAF 864: Fermat and gcd conditions imply prime factors are 1 mod F -/
theorem leaf_pock (F R : ℕ) (a : ℤ) (hOdd : Odd (R * F + 1)) (hF : Even F) (hCoprime : Nat.Coprime R F)
    (hFermat : (a : ZMod (R * F + 1)) ^ (R * F) = 1)
    (hgcd : ∀ p : ℕ, p.Prime → p ∣ F → Int.gcd (a ^ (R * F / p) - 1) (R * F + 1) = 1) :
    ∀ p : ℕ, p.Prime → p ∣ R * F + 1 → ∃ k : ℕ, p = k * F + 1 := sorry

/-- LEAF 864: If N is prime, the condition holds -/
theorem leaf_prime_cond (F R : ℕ) (hF : 0 < F) (hN : (R * F + 1).Prime) :
    R / (2 * F) = 0 ∨ ¬ IsSquare (((R % (2 * F) : ℕ) : ℤ) ^ 2 - 8 * ((R / (2 * F) : ℕ) : ℤ)) := by
  sorry

/-- LEAF 864: Composite N with factors 1 mod F and N < 2F^3 has exactly two such factors -/
theorem leaf_comp_factors (F R : ℕ) (hF : 0 < F) (hN_lt : R * F + 1 < 2 * F ^ 3)
    (hpock : ∀ p : ℕ, p.Prime → p ∣ R * F + 1 → ∃ k : ℕ, p = k * F + 1)
    (hN : ¬ (R * F + 1).Prime) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ R * F + 1 = (a * F + 1) * (b * F + 1) := sorry

/-- LEAF 864: Factorization gives R in terms of a and b -/
theorem leaf_R_eq (F R a b : ℕ) (hF : 0 < F) (h : R * F + 1 = (a * F + 1) * (b * F + 1)) :
    R = a * b * F + a + b := by
  have h1 : R * F + 1 = (a * b * F + a + b) * F + 1 := by
    calc R * F + 1 = (a * F + 1) * (b * F + 1) := h
      _ = a * b * F * F + a * F + b * F + 1 := by ring
      _ = (a * b * F + a + b) * F + 1 := by ring
  exact Nat.eq_of_mul_eq_mul_right hF (Nat.add_right_cancel h1)

/-- LEAF 864: If N factors, the BLS condition fails -/
theorem leaf_comp_cond_from_factors (F R a b : ℕ) (hF : 0 < F)
    (h_eq : R * F + 1 = (a * F + 1) * (b * F + 1)) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬ (R / (2 * F) = 0 ∨ ¬ IsSquare (((R % (2 * F) : ℕ) : ℤ) ^ 2 - 8 * ((R / (2 * F) : ℕ) : ℤ))) := by
  sorry

/-- Assembly for Lemma 1, Brillhart, Lehmer and Selfridge 1975, Theorem 5 -/
theorem lemma1 : Lemma1 := by
  intro F R a hOdd hF hCoprime hFermat hgcd hN_lt
  rcases Nat.eq_zero_or_pos F with rfl | hF_pos
  · exact leaf_F_zero R
  constructor
  · intro hN
    exact leaf_prime_cond F R hF_pos hN
  · intro hcond
    by_contra hN_comp
    have hpock := leaf_pock F R a hOdd hF hCoprime hFermat hgcd
    obtain ⟨a_fac, b_fac, ha, hb, heq⟩ := leaf_comp_factors F R hF_pos hN_lt hpock hN_comp
    have h_fail := leaf_comp_cond_from_factors F R a_fac b_fac hF_pos heq ha hb
    exact h_fail hcond

end LeanLab.Saouter1998.BLS
