/-
AI wrote this Lean code for CODEX task395.
P0037 Section 5.1 page 211 cites Cohen and Lenstra 1987.
The final trial division step below follows that source page 108.
No cyclotomic congruence input is proved here.
Binary Goldbach is open.
-/
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

namespace LeanLab.DtRS1998.Primality395

/-- Cohen and Lenstra 1987 page 108, Algorithm 1.3 final trial division.
CONDITIONAL ON the supplied prime divisor congruences and trial checks.
If the modulus exceeds the square root and all represented divisors are
one or the candidate itself, then the candidate is prime. -/
theorem prime_of_residue_trials {n s t : ℕ} (hn : 2 ≤ n) (hs : n < s ^ 2)
    (horbit : ∀ p : ℕ, p.Prime → p ∣ n →
      ∃ i : ℕ, i < t ∧ p % s = n ^ i % s)
    (htrial : ∀ i : ℕ, i < t → n ^ i % s ∣ n →
      n ^ i % s = 1 ∨ n ^ i % s = n) : n.Prime := by
  by_contra hnp
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hdiv : n.minFac ∣ n := Nat.minFac_dvd n
  have hsquare := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
  have hsmall : n.minFac < s := by nlinarith
  obtain ⟨i, hi, hres⟩ := horbit n.minFac hp hdiv
  rw [Nat.mod_eq_of_lt hsmall] at hres
  have hd : n ^ i % s ∣ n := by rwa [← hres]
  rcases htrial i hi hd with hone | heq
  · have htwo := hp.two_le
    omega
  · have hlt := (Nat.not_prime_iff_minFac_lt hn).mp hnp
    omega

/-- Cohen and Lenstra 1987 page 108, a concrete instance of every premise.
For n equal to 7, modulus 3 and one represented residue, the trial is 1. -/
theorem residue_trials_instance : (7 : ℕ).Prime := by
  apply prime_of_residue_trials (n := 7) (s := 3) (t := 1) (by decide) (by decide)
  · intro p hp hd
    have heq : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd
    subst p
    exact ⟨0, by decide, by decide⟩
  · intro i hi hd
    have heq : i = 0 := by omega
    subst i
    exact Or.inl (by decide)

/-- Cohen and Lenstra 1987 page 108, final trial division as a finite test.
CONDITIONAL ON the supplied prime divisor congruences and Boolean check. -/
theorem prime_of_residue_bool {n s t : ℕ} (hn : 2 ≤ n) (hs : n < s ^ 2)
    (horbit : ∀ p : ℕ, p.Prime → p ∣ n →
      ∃ i : ℕ, i < t ∧ p % s = n ^ i % s)
    (htest : (List.range t).all (fun i => decide
      (n ^ i % s ∣ n → n ^ i % s = 1 ∨ n ^ i % s = n)) = true) : n.Prime := by
  apply prime_of_residue_trials hn hs horbit
  intro i hi hd
  exact (of_decide_eq_true
    (List.all_eq_true.mp htest i (List.mem_range.mpr hi))) hd

/-- Cohen and Lenstra 1987 page 108, a nonempty Boolean trial instance.
Candidate 13 uses modulus 4 and exponent range containing zero. -/
theorem residue_bool_instance : (13 : ℕ).Prime := by
  apply prime_of_residue_bool (n := 13) (s := 4) (t := 1) (by decide) (by decide)
  · intro p hp hd
    have heq : p = 13 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd
    subst p
    exact ⟨0, by decide, by decide⟩
  · decide

/-- Cohen and Lenstra 1987 page 108, scope check for Remark 1.5.
The cube modulus bound alone does not suffice for our elementary criterion.
The source improvement also requires its extra divisor enumeration algorithm. -/
theorem cube_bound_insufficient :
    169 < (6 : ℕ) ^ 3 ∧
    (∀ p : ℕ, p.Prime → p ∣ 169 →
      ∃ i : ℕ, i < 1 ∧ p % 6 = 169 ^ i % 6) ∧
    (List.range 1).all (fun i => decide
      (169 ^ i % 6 ∣ 169 → 169 ^ i % 6 = 1 ∨ 169 ^ i % 6 = 169)) = true ∧
    ¬ (169 : ℕ).Prime := by
  refine ⟨by decide, ?_, by decide, by norm_num⟩
  intro p hp hd
  have hd13 : p ∣ 13 := hp.dvd_of_dvd_pow (show p ∣ (13 : ℕ) ^ 2 from hd)
  have heq : p = 13 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd13
  subst p
  exact ⟨0, by decide, by decide⟩

#print axioms prime_of_residue_trials
#print axioms residue_trials_instance
#print axioms prime_of_residue_bool
#print axioms residue_bool_instance
#print axioms cube_bound_insufficient

end LeanLab.DtRS1998.Primality395
