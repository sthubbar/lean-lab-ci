import LeanLab.ExceptionalSet.ExceptionalCorrection465

/-!
The elementary conductor shape implication before P0082 display22.
The classification of primitive real characters is an explicit input.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.Supply465
open Finset

/-- P0082 page363 case ii c. If every prime above three dividing an odd
squarefree u divides m, then u divides three m. -/
theorem odd_squarefree_dvd_three_mul (u m : ℕ) (hu : Odd u) (hs : Squarefree u)
    (hp : ∀ p : ℕ, p.Prime → p ∣ u → 3 < p → p ∣ m) : u ∣ 3 * m := by
  by_cases hm : m = 0
  · simp [hm]
  rw [← Nat.prod_primeFactors_of_squarefree hs]
  apply (Nat.prod_primeFactors_dvd_iff (by omega : 3 * m ≠ 0)).mpr
  intro p hpu
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hpu
  apply Nat.mem_primeFactors.mpr
  refine ⟨hpp, ?_, by omega⟩
  by_cases hp3 : p = 3
  · subst p
    exact dvd_mul_right 3 m
  · have hp2 : p ≠ 2 := by intro h; subst p; exact hu.not_two_dvd_nat hpd
    have hpgt : 3 < p := by have := hpp.two_le; omega
    exact dvd_mul_of_dvd_right (hp p hpp hpd hpgt) 3

/-- P0082 page363 case ii c. The printed conductor shape and empty
prime product imply r at most twenty four times gcd m r. CONDITIONAL ON
the explicit conductor shape, with no character classification supplied. -/
theorem conductor_large_gcd (r m k u : ℕ) (hr : r = 2 ^ k * u) (hk : k ≤ 3)
    (hu : Odd u) (hs : Squarefree u)
    (hp : ∀ p : ℕ, p.Prime → p ∣ u → 3 < p → p ∣ m) :
    r ≤ 24 * Nat.gcd m r := by
  have hud := odd_squarefree_dvd_three_mul u m hu hs hp
  have htwo : 2 ^ k ∣ 8 := by
    refine ⟨2 ^ (3 - k), ?_⟩
    rw [← pow_add, Nat.add_sub_of_le hk]
    norm_num
  have hrdiv : r ∣ 24 * m := by
    rw [hr]
    convert mul_dvd_mul htwo hud using 1 <;> ring
  have hg : r ∣ 24 * Nat.gcd m r := by
    obtain ⟨c, hc⟩ := dvd_mul_gcd_of_dvd_mul hrdiv
    exact ⟨c, by simpa only [gcd_eq_nat_gcd, Nat.gcd_comm] using hc⟩
  have hrpos : 0 < r := by rw [hr]; exact mul_pos (by positivity) (Nat.pos_of_ne_zero hs.ne_zero)
  have hgp : 0 < Nat.gcd m r := Nat.gcd_pos_of_pos_right m hrpos
  exact Nat.le_of_dvd (by positivity) hg

/-- P0082 page363 display21 and its following paragraph. For a conductor
of the printed shape, gcd below r over twenty four forces a prime above
three in the conductor that does not divide m. CONDITIONAL ON that shape. -/
theorem conductor_prime_witness (r m k u : ℕ) (hr : r = 2 ^ k * u) (hk : k ≤ 3)
    (hu : Odd u) (hs : Squarefree u) (hsmall : 24 * Nat.gcd m r < r) :
    ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ p ∣ m := by
  by_contra hnone
  push_neg at hnone
  have hp : ∀ p : ℕ, p.Prime → p ∣ u → 3 < p → p ∣ m := by
    intro p hpp hpu hp3
    apply hnone p hpp
    · rw [hr]
      exact dvd_mul_of_dvd_right hpu _
    · exact hp3
  have := conductor_large_gcd r m k u hr hk hu hs hp
  omega
end LeanLab.ExceptionalSet.Supply465
