/-
FALSE. The leaf prime_phase_periodic442 of Linnik1951/SPLIT_prime_class_split442 is false
as formalized, and a repaired form is proved here.

In the leaf the residue of the prime is written ((p : ℕ) % q : ℝ). Lean elaborates that
remainder at type ℝ, as the remainder of the casts in the Euclidean domain structure of
the real field, and in a field the remainder of x by a nonzero y is 0. So the right side of
the leaf is exp of minus 2 pi i z p alone and the leaf says that exp of minus 2 pi i a p
over q is 1 for every a, every prime p and every q at least 2. That fails at q = 3, a = 1,
p = 2, z = 0, where the left side is exp of minus 4 pi i over 3.

The intended identity, with the residue of p modulo q taken in the natural numbers and then
cast to ℝ, is true and is proved below as prime_phase_periodic442_natmod.
This file imports the leaf file only so that the negated statement elaborates in the same
environment; no theorem here uses the leaf.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_prime_class_split442

namespace LeanLab.Linnik1951

/-- In the real field the Euclidean remainder by a nonzero number is zero. -/
theorem real_mod_eq_zero442 (x y : ℝ) (hy : y ≠ 0) : x % y = 0 := by
  rw [EuclideanDomain.mod_eq_sub_mul_div, mul_div_cancel₀ _ hy, sub_self]

/-- FALSE witness for prime_phase_periodic442: its statement, universally quantified, fails at
q = 3, a = 1, z = 0 and the prime 2, since the real remainder is zero and exp of minus 4 pi i
over 3 is not 1. -/
theorem not_prime_phase_periodic442 : ¬ (∀ (q : ℕ) (_hq : 2 ≤ q) (a : ℕ) (z : ℝ) (p : Nat.Primes),
    Complex.exp ((-(2 * Real.pi * ((a : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) =
      Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (((p : ℕ) % q) : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) := by
  intro h
  have h1 := h 3 (by norm_num) 1 0 ⟨2, Nat.prime_two⟩
  have hm : ((2 : ℕ) : ℝ) % ((3 : ℕ) : ℝ) = 0 := real_mod_eq_zero442 _ _ (by norm_num)
  simp only [hm, mul_zero, zero_div, neg_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, add_zero, one_mul] at h1
  rw [Complex.exp_eq_one_iff] at h1
  obtain ⟨n, hn⟩ := h1
  have him := congrArg Complex.im hn
  simp at him
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hn' : (n : ℝ) = -(2 / 3) := by
    field_simp at him
    linarith
  have h3 : (3 : ℝ) * n = -2 := by rw [hn']; ring
  have h3' : (3 : ℤ) * n = -2 := by exact_mod_cast h3
  omega

/-- Repaired residue class periodicity of the prime phase, a new statement next to the false
leaf, not a change of it: with the residue of p modulo q taken in the natural numbers, the
phase at a/q + z is the phase at a times that residue over q times the phase at z, since
a times p over q differs from a times the residue over q by the integer a times p div q. -/
theorem prime_phase_periodic442_natmod (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (z : ℝ) (p : Nat.Primes) :
    Complex.exp ((-(2 * Real.pi * ((a : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) =
      Complex.exp ((-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) / (q : ℝ))) : ℝ) *
        Complex.I) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hdiv : ((p : ℕ) : ℝ) = (q : ℝ) * (((p : ℕ) / q : ℕ) : ℝ) + (((p : ℕ) % q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod (p : ℕ) q).symm
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = a * ((p : ℕ) / q) := ⟨_, rfl⟩
  have hsplit : (-(2 * Real.pi * ((a : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) =
      (-(2 * Real.pi * (((a : ℝ) * ((((p : ℕ) % q : ℕ)) : ℝ)) / (q : ℝ))) : ℝ) +
        (-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) + (-(2 * Real.pi * (k : ℝ))) := by
    have e : (k : ℝ) = (a : ℝ) * (((p : ℕ) / q : ℕ) : ℝ) := by
      rw [hk]; push_cast; ring
    rw [e, hdiv]
    field_simp
    ring
  rw [hsplit]
  push_cast
  rw [add_mul, add_mul, Complex.exp_add, Complex.exp_add]
  have h1 : Complex.exp (-(2 * (Real.pi : ℂ) * (k : ℂ)) * Complex.I) = 1 := by
    have : -(2 * (Real.pi : ℂ) * (k : ℂ)) * Complex.I =
        ((-(k : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  rw [h1, mul_one]

end LeanLab.Linnik1951

#print axioms LeanLab.Linnik1951.real_mod_eq_zero442
#print axioms LeanLab.Linnik1951.not_prime_phase_periodic442
#print axioms LeanLab.Linnik1951.prime_phase_periodic442_natmod
