/-
AI wrote this Lean code for CODEX task427.
Cohen and Lenstra 1987 page 108, Algorithm 1.3 final trial division.
Reuse the existing square bound criterion and Mathlib list iteration.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Primality395
import Mathlib.Data.List.Iterate

namespace LeanLab.DtRS1998.Primality427

/-- Cohen and Lenstra 1987 page 108, step l1.
Repeated modular multiplication enumerates the power residues. -/
theorem iterate_mul_mod (n s i : ℕ) :
    (fun r : ℕ => r * n % s)^[i] (1 % s) = n ^ i % s := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Nat.pow_succ, Nat.mod_mul_mod]

/-- Cohen and Lenstra 1987 page 108, final trial division.
CONDITIONAL ON the divisor congruences and finite residue check.
The square bound and every prime divisor premise remain explicit. -/
theorem prime_of_iterate_trials {n s t : ℕ} (hn : 2 ≤ n) (hs : n < s ^ 2)
    (horbit : ∀ p : ℕ, p.Prime → p ∣ n →
      ∃ i : ℕ, i < t ∧ p % s = n ^ i % s)
    (htrial : (List.iterate (fun r : ℕ => r * n % s) (1 % s) t).all
      (fun r => decide (r ∣ n → r = 1 ∨ r = n)) = true) : n.Prime := by
  apply Primality395.prime_of_residue_trials hn hs horbit
  intro i hi hd
  have hm : n ^ i % s ∈ List.iterate (fun r : ℕ => r * n % s) (1 % s) t := by
    apply List.mem_iterate.mpr
    exact ⟨i, hi, (iterate_mul_mod n s i).symm⟩
  exact (of_decide_eq_true (List.all_eq_true.mp htrial _ hm)) hd

/-- Cohen and Lenstra 1987 page 108, a nonempty small trial instance.
The residue list for n equal to 7 and modulus 3 is the singleton 1. -/
theorem iterate_trials_instance : (7 : ℕ).Prime := by
  apply prime_of_iterate_trials (s := 3) (t := 1) (by decide) (by decide)
  · intro p hp hd
    have heq : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd
    subst p
    exact ⟨0, by decide, by decide⟩
  · decide

#print axioms iterate_mul_mod
#print axioms prime_of_iterate_trials
#print axioms iterate_trials_instance

end LeanLab.DtRS1998.Primality427
