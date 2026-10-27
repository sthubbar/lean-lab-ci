/-
# R-0035, T3 MOONSHOT: equidistribution of Goldbach representations in residue classes

Unit U-1332, PC run 20261021T0203Z-29730. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

The route: split the ordered count r(N) = #{p ≤ N : p, N - p prime} by the class of p mod q,
r(N; q, a), and try to reach r(N) > 0 from equidistribution of the pairs among the admissible
classes, those a with gcd(a, q) = gcd(N - a, q) = 1. This file proves the bookkeeping and the
two facts that block it.

PROVED here, unconditional:
* `sum_classes`: for q ≥ 1, Σ_{a < q} r(N; q, a) = r(N).
* `goldbach_iff_r_pos`: N is a sum of two primes iff r(N) > 0.
* `goldbach_of_class_pos`: one positive class already gives N = p + p'.
* `relative_vacuous`: r(N) = 0 forces r(N; q, a) = 0 for every q, a, so every relative
  statement r(N; q, a) = (1 + o(1)) r(N) / φ₂ holds at a counterexample N; it carries no
  information about r(N) > 0.
* `bad_class_le_one`: if gcd(a, q) > 1 then r(N; q, a) ≤ 1; the inadmissible classes hold at
  most the single prime gcd(a, q).
* `vacuity_ten`, `vacuity_sum`: r(10; 4, 3) = 2, from 3 + 7 and 7 + 3, and the class sum at
  N = 10, q = 4 is r(10) = 3.
-/
import LeanLab.Common.Goldbach

namespace LeanLab.R0035

open Finset

/-- Ordered Goldbach count of `N`. -/
def r (N : ℕ) : ℕ := ((range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime)).card

/-- Ordered Goldbach count of `N` with the first prime in the class `a` mod `q`. -/
def rq (N q a : ℕ) : ℕ :=
  ((range (N + 1)).filter (fun p => (p.Prime ∧ (N - p).Prime) ∧ p % q = a)).card

theorem sum_classes (N q : ℕ) (hq : 0 < q) : ∑ a ∈ range q, rq N q a = r N := by
  unfold r rq
  rw [card_eq_sum_card_fiberwise (f := fun p => p % q) (t := range q)]
  · refine sum_congr rfl fun a _ => ?_
    rw [filter_filter]
  · intro p _
    simpa using Nat.mod_lt p hq

theorem goldbach_iff_r_pos (N : ℕ) : 0 < r N ↔ IsGoldbachSum N := by
  unfold r
  rw [card_pos]
  constructor
  · rintro ⟨p, hp⟩
    rw [mem_filter, mem_range] at hp
    exact ⟨p, N - p, hp.2.1, hp.2.2, by omega⟩
  · rintro ⟨p, p', hp, hp', rfl⟩
    exact ⟨p, by rw [mem_filter, mem_range]; exact ⟨by omega, hp, by simpa using hp'⟩⟩

theorem rq_le_r (N q a : ℕ) : rq N q a ≤ r N := by
  unfold r rq
  rw [← filter_filter]
  exact card_filter_le _ _

theorem goldbach_of_class_pos (N q a : ℕ) (h : 0 < rq N q a) : IsGoldbachSum N :=
  (goldbach_iff_r_pos N).1 (lt_of_lt_of_le h (rq_le_r N q a))

theorem relative_vacuous (N q a : ℕ) (h : r N = 0) : rq N q a = 0 := by
  have := rq_le_r N q a
  omega

theorem bad_class_le_one (N q a : ℕ) (h : 1 < Nat.gcd a q) : rq N q a ≤ 1 := by
  unfold rq
  apply card_le_one.2
  intro p hp p' hp'
  have key : ∀ x, (x.Prime ∧ (N - x).Prime) ∧ x % q = a → x = Nat.gcd a q := by
    rintro x ⟨⟨hx, -⟩, hxa⟩
    have h1 : Nat.gcd a q ∣ x := by
      have : x = q * (x / q) + a := by rw [← hxa]; exact (Nat.div_add_mod x q).symm
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_left (Nat.gcd_dvd_right a q) _) (Nat.gcd_dvd_left a q)
    rcases (Nat.dvd_prime hx).1 h1 with h2 | h2
    · omega
    · exact h2.symm
  rw [mem_filter] at hp hp'
  rw [key p hp.2, key p' hp'.2]

theorem vacuity_ten : rq 10 4 3 = 2 := by decide

theorem vacuity_sum : ∑ a ∈ range 4, rq 10 4 a = 3 := by
  rw [sum_classes 10 4 (by norm_num)]; decide

end LeanLab.R0035
