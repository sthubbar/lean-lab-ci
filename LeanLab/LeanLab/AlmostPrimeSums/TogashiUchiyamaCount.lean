/-
AI-written Lean code, Claude, 2026-10-21, CLOUD 20261021T0217Z-cloud56, unit U-6803.
P0072 Togashi and Uchiyama 1964, the elementary counting steps of Lemma 5, p. 65, and of
Section 5, pp. 67 to 68, read from papers/P0072.pdf.

PROVED here, the combinatorial parts the paper states without proof:
* `lemma5_double_count`, p. 65: "Clearly S₂ is not greater than 1/(r+1) Σ_{z<q≤z₁} S(q)".
  If D a q means q divides a, the number of a in A with at least r + 1 of the q in Q
  dividing them, times r + 1, is at most Σ_{q ∈ Q} #{a ∈ A : D a q}.
* `section5_inclusion`, p. 67: S ≥ S₁ - S₂ - S₃, as #A ≤ #(A minus B minus C) + #B + #C.
* `omega_le_three_of_sieved`, `section5_final`, pp. 67 to 68: if 0 < n < N, every prime
  factor p of n(N - n) has p⁶ > N, that is p > N^{1/6} = z, and n(N - n) has at most two
  prime factors p with p³ ≤ N, that is p ≤ N^{1/3} = z₁, counted with multiplicity, then
  Ω(n) ≤ 3 and Ω(N - n) ≤ 3. The paper's "at most two distinct primes q in (z, z₁] and
  no q²" gives the multiplicity count ≤ 2.
The sieve bounds of Lemmas 4 and 5 stay cited. Goldbach is open.
-/
import Mathlib

open Finset

namespace LeanLab.AlmostPrimeSums.TogashiUchiyamaCount

/-- Lemma 5 double count: (r+1) S₂ ≤ Σ_q S(q). -/
theorem lemma5_double_count {α β : Type*} [DecidableEq β] (A : Finset α) (Q : Finset β)
    (D : α → β → Prop) [∀ a q, Decidable (D a q)] (r : ℕ) :
    (r + 1) * (A.filter (fun a => r + 1 ≤ (Q.filter (fun q => D a q)).card)).card ≤
      ∑ q ∈ Q, (A.filter (fun a => D a q)).card := by
  have hR : ∑ q ∈ Q, (A.filter (fun a => D a q)).card =
      ∑ a ∈ A, (Q.filter (fun q => D a q)).card := by
    simp only [card_filter]
    exact Finset.sum_comm
  rw [hR, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  calc ∑ _a ∈ A.filter (fun a => r + 1 ≤ (Q.filter (fun q => D a q)).card), (r + 1)
      ≤ ∑ a ∈ A.filter (fun a => r + 1 ≤ (Q.filter (fun q => D a q)).card),
          (Q.filter (fun q => D a q)).card :=
        Finset.sum_le_sum (fun a ha => (Finset.mem_filter.mp ha).2)
    _ ≤ ∑ a ∈ A, (Q.filter (fun q => D a q)).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- Section 5: S ≥ S₁ - S₂ - S₃ in the form #A ≤ #S + #B + #C. -/
theorem section5_inclusion {α : Type*} [DecidableEq α] (A B C : Finset α) :
    A.card ≤ (A.filter (fun a => a ∉ B ∧ a ∉ C)).card + B.card + C.card := by
  have h1 : A ⊆ A.filter (fun a => a ∉ B ∧ a ∉ C) ∪ B ∪ C := by
    intro a ha
    by_cases hB : a ∈ B
    · simp [hB]
    · by_cases hC : a ∈ C
      · simp [hC]
      · simp [ha, hB, hC]
  calc A.card ≤ (A.filter (fun a => a ∉ B ∧ a ∉ C) ∪ B ∪ C).card := card_le_card h1
    _ ≤ (A.filter (fun a => a ∉ B ∧ a ∉ C) ∪ B).card + C.card := card_union_le _ _
    _ ≤ _ := by have := card_union_le (A.filter (fun a => a ∉ B ∧ a ∉ C)) B; omega

/-- Product bound over a list: each x has x⁶ > N, and x⁶ ≥ (N+1)² when x³ > N. -/
lemma list_prod_bound (N : ℕ) : ∀ L : List ℕ, (∀ x ∈ L, N < x ^ 6) →
    (N + 1) ^ (L.countP (fun x => x ^ 3 ≤ N) + 2 * L.countP (fun x => ¬ x ^ 3 ≤ N)) ≤
      L.prod ^ 6 := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons x L ih =>
    intro hL
    have hx : N < x ^ 6 := hL x (by simp)
    have ihL := ih (fun y hy => hL y (by simp [hy]))
    by_cases h : x ^ 3 ≤ N
    · have e1 : (x :: L).countP (fun x => x ^ 3 ≤ N) = L.countP (fun x => x ^ 3 ≤ N) + 1 := by
        simp [List.countP_cons, h]
      have e2 : (x :: L).countP (fun x => ¬ x ^ 3 ≤ N) = L.countP (fun x => ¬ x ^ 3 ≤ N) := by
        simp [List.countP_cons, h]
      rw [e1, e2, List.prod_cons, mul_pow]
      have e3 : L.countP (fun x => x ^ 3 ≤ N) + 1 + 2 * L.countP (fun x => ¬ x ^ 3 ≤ N)
          = (L.countP (fun x => x ^ 3 ≤ N) + 2 * L.countP (fun x => ¬ x ^ 3 ≤ N)) + 1 := by ring
      rw [e3, pow_succ, mul_comm (x ^ 6)]
      exact Nat.mul_le_mul ihL hx
    · have e1 : (x :: L).countP (fun x => x ^ 3 ≤ N) = L.countP (fun x => x ^ 3 ≤ N) := by
        simp [List.countP_cons, h]
      have e2 : (x :: L).countP (fun x => ¬ x ^ 3 ≤ N) = L.countP (fun x => ¬ x ^ 3 ≤ N) + 1 := by
        simp [List.countP_cons, h]
      rw [e1, e2, List.prod_cons, mul_pow]
      have hx3 : N + 1 ≤ x ^ 3 := by omega
      have hx6 : (N + 1) ^ 2 ≤ x ^ 6 := by
        rw [show x ^ 6 = (x ^ 3) ^ 2 by ring]; exact Nat.pow_le_pow_left hx3 2
      have e3 : L.countP (fun x => x ^ 3 ≤ N) + 2 * (L.countP (fun x => ¬ x ^ 3 ≤ N) + 1)
          = (L.countP (fun x => x ^ 3 ≤ N) + 2 * L.countP (fun x => ¬ x ^ 3 ≤ N)) + 2 := by ring
      rw [e3, pow_add, mul_comm (x ^ 6)]
      exact Nat.mul_le_mul ihL hx6

/-- The core count: 0 < n < N, all prime factors above N^{1/6}, at most two of them, with
multiplicity, at most N^{1/3}; then Ω(n) ≤ 3. -/
theorem omega_le_three_of_sieved {N n : ℕ} (hn0 : 0 < n) (hnN : n < N)
    (hbig : ∀ p ∈ n.primeFactorsList, N < p ^ 6)
    (hmid : n.primeFactorsList.countP (fun p => p ^ 3 ≤ N) ≤ 2) :
    ArithmeticFunction.cardFactors n ≤ 3 := by
  rw [ArithmeticFunction.cardFactors_apply]
  set L := n.primeFactorsList with hLdef
  have hprod : L.prod = n := Nat.prod_primeFactorsList hn0.ne'
  have hb := list_prod_bound N L hbig
  rw [hprod] at hb
  have hlt : n ^ 6 < (N + 1) ^ 6 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have he : L.countP (fun x => x ^ 3 ≤ N) + 2 * L.countP (fun x => ¬ x ^ 3 ≤ N) < 6 :=
    (Nat.pow_lt_pow_iff_right (by omega)).mp (lt_of_le_of_lt hb hlt)
  have hlen := L.length_eq_countP_add_countP (fun x => decide (x ^ 3 ≤ N))
  simp only [decide_not] at hlen he hmid ⊢
  have hlen' : L.length = L.countP (fun x => decide (x ^ 3 ≤ N)) +
      L.countP (fun x => !decide (x ^ 3 ≤ N)) := hlen
  omega

/-- Section 5, the final step: the conditions defining S on a = n(N - n) give
Ω(n) ≤ 3 and Ω(N - n) ≤ 3. -/
theorem section5_final {N n : ℕ} (hn0 : 0 < n) (hnN : n < N)
    (hbig : ∀ p ∈ (n * (N - n)).primeFactorsList, N < p ^ 6)
    (hmid : (n * (N - n)).primeFactorsList.countP (fun p => p ^ 3 ≤ N) ≤ 2) :
    ArithmeticFunction.cardFactors n ≤ 3 ∧ ArithmeticFunction.cardFactors (N - n) ≤ 3 := by
  have ha : n * (N - n) ≠ 0 := Nat.mul_ne_zero hn0.ne' (by omega)
  have s1 := Nat.primeFactorsList_sublist_of_dvd (Dvd.intro _ rfl) ha
  have s2 := Nat.primeFactorsList_sublist_of_dvd (Dvd.intro_left _ rfl) ha
  constructor
  · exact omega_le_three_of_sieved hn0 hnN (fun p hp => hbig p (s1.subset hp))
      (le_trans s1.countP_le hmid)
  · exact omega_le_three_of_sieved (by omega) (by omega) (fun p hp => hbig p (s2.subset hp))
      (le_trans s2.countP_le hmid)

/-- The paper's form of the middle condition, p. 67: at most two distinct primes q ≤ N^{1/3}
divide a, and no such q has q² ∣ a; then such primes number at most two with multiplicity. -/
theorem mid_count_le_two {a N : ℕ} (ha : a ≠ 0)
    (hdist : (a.primeFactors.filter (fun q => q ^ 3 ≤ N)).card ≤ 2)
    (hsq : ∀ q ∈ a.primeFactors, q ^ 3 ≤ N → ¬ q ^ 2 ∣ a) :
    a.primeFactorsList.countP (fun p => p ^ 3 ≤ N) ≤ 2 := by
  rw [List.countP_eq_length_filter]
  have hnd : (a.primeFactorsList.filter (fun p => p ^ 3 ≤ N)).Nodup := by
    rw [List.nodup_iff_count_le_one]
    intro q
    by_cases hq : q ∈ a.primeFactorsList.filter (fun p => p ^ 3 ≤ N)
    · have hqL : q ∈ a.primeFactorsList := (List.mem_filter.mp hq).1
      have hP : q ^ 3 ≤ N := by simpa using (List.mem_filter.mp hq).2
      have hqp : q.Prime := Nat.prime_of_mem_primeFactorsList hqL
      have h1 := List.Sublist.count_le q
        (List.filter_sublist (p := fun p => decide (p ^ 3 ≤ N)) (l := a.primeFactorsList))
      rw [Nat.primeFactorsList_count_eq] at h1
      by_contra hc
      apply hsq q ((Nat.mem_primeFactors_of_ne_zero ha).mpr
        ⟨hqp, Nat.dvd_of_mem_primeFactorsList hqL⟩) hP
      exact (hqp.pow_dvd_iff_le_factorization ha).mpr (by omega)
    · rw [List.count_eq_zero_of_not_mem hq]; omega
  rw [← List.toFinset_card_of_nodup hnd]
  refine le_trans (Finset.card_le_card ?_) hdist
  intro q hq
  rw [List.mem_toFinset, List.mem_filter] at hq
  rw [Finset.mem_filter, Nat.mem_primeFactors_of_ne_zero ha]
  exact ⟨⟨Nat.prime_of_mem_primeFactorsList hq.1, Nat.dvd_of_mem_primeFactorsList hq.1⟩,
    by simpa using hq.2⟩

/-- Section 5 final step in the paper's words: no prime p ≤ N^{1/6} divides n(N - n), at most
two distinct primes q ≤ N^{1/3} divide it and no q² does; then Ω(n) ≤ 3 and Ω(N - n) ≤ 3. -/
theorem section5_final_paper {N n : ℕ} (hn0 : 0 < n) (hnN : n < N)
    (hbig : ∀ p ∈ (n * (N - n)).primeFactors, N < p ^ 6)
    (hdist : ((n * (N - n)).primeFactors.filter (fun q => q ^ 3 ≤ N)).card ≤ 2)
    (hsq : ∀ q ∈ (n * (N - n)).primeFactors, q ^ 3 ≤ N → ¬ q ^ 2 ∣ n * (N - n)) :
    ArithmeticFunction.cardFactors n ≤ 3 ∧ ArithmeticFunction.cardFactors (N - n) ≤ 3 := by
  have ha : n * (N - n) ≠ 0 := Nat.mul_ne_zero hn0.ne' (by omega)
  refine section5_final hn0 hnN (fun p hp => hbig p ?_) (mid_count_le_two ha hdist hsq)
  exact (Nat.mem_primeFactors_of_ne_zero ha).mpr
    ⟨Nat.prime_of_mem_primeFactorsList hp, Nat.dvd_of_mem_primeFactorsList hp⟩

/-- Vacuity check: the hypotheses of `section5_final` are satisfiable, N = 100, n = 11,
N - n = 89. -/
example : ArithmeticFunction.cardFactors 11 ≤ 3 ∧ ArithmeticFunction.cardFactors (100 - 11) ≤ 3 := by
  have hp : (11 * 89).primeFactorsList.Perm ([11] ++ [89]) := by
    have := Nat.perm_primeFactorsList_mul (a := 11) (b := 89) (by norm_num) (by norm_num)
    rwa [Nat.primeFactorsList_prime (by norm_num : Nat.Prime 11),
      Nat.primeFactorsList_prime (by norm_num : Nat.Prime 89)] at this
  refine section5_final (N := 100) (n := 11) (by norm_num) (by norm_num) ?_ ?_
  · show ∀ p ∈ (11 * 89).primeFactorsList, 100 < p ^ 6
    intro p hp'
    have := hp.mem_iff.mp hp'
    simp at this
    rcases this with rfl | rfl <;> norm_num
  · show (11 * 89).primeFactorsList.countP (fun p => p ^ 3 ≤ 100) ≤ 2
    rw [hp.countP_eq]; decide

end LeanLab.AlmostPrimeSums.TogashiUchiyamaCount

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaCount.lemma5_double_count
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaCount.section5_inclusion
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaCount.omega_le_three_of_sieved
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaCount.section5_final
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaCount.mid_count_le_two
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaCount.section5_final_paper
