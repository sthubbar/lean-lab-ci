/-
AI wrote this Lean code for the route burst of 2026-11-12, step second_family.
P0037 Section 5.2, printed page 212, and Table 2, printed page 214.
Pieces of the paper's argument for the second interval family of Theorem 2,
the intervals [10^(10 i), 10^(10 i) + 10^9] for i = 20 to 30.
This file imports only Task71Paper, so Decomp121b can import it without a cycle.
The two Table 2 certificate lemmas are OPEN computations. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task71Paper

namespace LeanLab.DtRS1998.Decomp121bSecond

open LeanLab Task71.Paper

/-- P0037 Section 5.2 page 212, the sieve over the bit array of even numbers in
[B, B + 10^9], with the method of page 207: if a list of primes q is such that for
every even e = B + 2 j in the interval some q in the list has q ≤ e and e - q prime,
then every even e in the interval is a sum of two primes.
PROVED. -/
theorem interval_of_table2_certificate {B L : ℕ} {qs : List ℕ} (hB : Even B)
    (hq : ∀ q ∈ qs, q.Prime)
    (hcheck : (List.range (L / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true) :
    IntervalSum B L := by
  intro n hlo hhi hn
  have hdiff : Even (n - B) := even_iff_two_dvd.mpr
    (Nat.dvd_sub (even_iff_two_dvd.mp hn) (even_iff_two_dvd.mp hB))
  obtain ⟨j, hj⟩ := hdiff
  have hn_eq : n = B + 2 * j := by omega
  have hjL : j < L / 2 + 1 := by omega
  obtain ⟨q, hmem, hgood⟩ := List.any_eq_true.mp
    (List.all_eq_true.mp hcheck j (List.mem_range.mpr hjL))
  have hpair := of_decide_eq_true hgood
  refine ⟨q, n - q, hq q hmem, ?_, ?_⟩
  · simpa [hn_eq] using hpair.2
  · exact Nat.add_sub_of_le (by simpa [hn_eq] using hpair.1)

/-- P0037 Section 5.2 page 212, heading: the left endpoints B = 10^(10 i) are even,
so the bit array of page 212 indexes exactly the even numbers B + 2 j.
PROVED. -/
theorem table2_base_even (i : ℕ) (hi : 1 ≤ i) : Even (10 ^ (10 * i)) := by
  have h : 10 * i = (10 * i - 1) + 1 := by omega
  rw [h, pow_succ]
  exact (even_iff_two_dvd.mpr (by norm_num : (2 : ℕ) ∣ 10)).mul_left _

/-- LEAF: P0037 Section 5.2 page 212 and Table 2 page 214, rows log10 B = 200 to 250.
Phase one, sieve plus Miller Rabin to bases 2, 3, 5, 7, produced a list q1, ..., qNq;
phase two, ECPP, certified each entry prime. Page 212 states Nq varies from 222 up
to 231, and Table 2 prints Nq = 224, 222, 222, 228, 228, 231 for these rows.
OPEN: the prime lists and ECPP certificates are not in the lab. -/
theorem table2_certificates_lower :
    ∀ i : ℕ, 20 ≤ i → i ≤ 25 →
      ∃ qs : List ℕ, qs.length ≤ 231 ∧ (∀ q ∈ qs, q.Prime) ∧
        (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
          qs.any (fun q => decide
            (q ≤ 10 ^ (10 * i) + 2 * j ∧ (10 ^ (10 * i) + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF: P0037 Section 5.2 page 212 and Table 2 page 214, rows log10 B = 260 to 300.
Same two phase method; Table 2 prints Nq = 226, 223, 225, 226, 227 for these rows,
within the page 212 range 222 to 231.
OPEN: the prime lists and ECPP certificates are not in the lab. -/
theorem table2_certificates_upper :
    ∀ i : ℕ, 26 ≤ i → i ≤ 30 →
      ∃ qs : List ℕ, qs.length ≤ 231 ∧ (∀ q ∈ qs, q.Prime) ∧
        (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
          qs.any (fun q => decide
            (q ≤ 10 ^ (10 * i) + 2 * j ∧ (10 ^ (10 * i) + 2 * j - q).Prime))) = true := by
  sorry

#print axioms interval_of_table2_certificate
#print axioms table2_base_even
#print axioms table2_certificates_lower
#print axioms table2_certificates_upper

end LeanLab.DtRS1998.Decomp121bSecond
