import Mathlib

/-!
Audit of an inherited leaf against P0075 page 13, Lemma A.1 part 1.
The paper splits at the prime with index n0. It does not split at prime value n0.
AI wrote this Lean code. Goldbach is open.
-/
open Real
namespace LeanLab.ChirreHagen2025.CutoffAudit272

/-- Lab audit of P0075 page 13. For every natural N at least eight, Bertrand gives
an actual prime between N and twice N. No index n above N can satisfy n log n below
that prime, since log n is at least two. This refutes the prime-value cutoff claim. -/
theorem no_prime_value_cutoff (N : ℕ) (hN : 8 ≤ N) :
    ¬ (∀ p : Nat.Primes, N < (p : ℕ) →
      ∃ n : ℕ, N < n ∧ (n : ℝ) * Real.log (n : ℝ) < (p : ℝ)) := by
  intro h
  obtain ⟨p, hp, hNp, hpN⟩ := Nat.exists_prime_lt_and_le_two_mul N (by omega)
  obtain ⟨n, hn, hnp⟩ := h ⟨p, hp⟩ hNp
  have hn8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 8 ≤ n by omega)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < (2 : ℝ) ^ 3)
    (show (2 : ℝ) ^ 3 ≤ (n : ℝ) from
      calc (2 : ℝ) ^ 3 = 8 := by norm_num
           _ ≤ (n : ℝ) := hn8)
  rw [Real.log_pow] at hlog
  have hlog2 : (2 : ℝ) ≤ Real.log (n : ℝ) := by
    norm_num at hlog
    linarith [Real.log_two_gt_d9]
  have hpN' : (p : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hpN
  have hn' : (N : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (α := ℝ) n)
  change (n : ℝ) * Real.log (n : ℝ) < (p : ℝ) at hnp
  nlinarith

/-- Lab audit of P0075 page 13, at the inherited cutoff 26355867.
This negates DecompJ867.leaf_prime_lower_bound after substituting its fixed n0.
The paper uses prime index n0, so this is a QUESTION about the inherited Lean leaf. -/
theorem not_inherited_leaf_prime_lower_bound :
    ¬ (∀ p : Nat.Primes, 26355867 < (p : ℕ) →
      ∃ n : ℕ, 26355867 < n ∧ (n : ℝ) * Real.log (n : ℝ) < (p : ℝ)) := by
  exact no_prime_value_cutoff 26355867 (by norm_num)

/-- Lab audit of P0075 page 14, Lemma A.1 parts 2 and 3.
The bound 0.982 supplies no numerical route to 0.8053 from equality and comparison.
The paper evaluates the part 2 sum separately by the method of part 1. -/
theorem part3_numeric_insufficient :
    ¬ (∀ a b c : ℝ, a = b → b ≤ c → c < 0.982 → a < 0.8053) := by
  intro h
  have hbad := h 0.9 0.9 0.9 rfl (le_refl _) (by norm_num)
  norm_num at hbad

end LeanLab.ChirreHagen2025.CutoffAudit272
