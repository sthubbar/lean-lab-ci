/-
AI wrote this Lean code for CODEX task270.
P0037 Sections 2 and 5.1, pages 207 and 211, Table 1 on page 213.
The open leaves request finite prime lists and Boolean coverage certificates.
The first family is assembled without using the old cited leaf.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task71Paper
import LeanLab.DtRS1998.Task294Row85
import LeanLab.DtRS1998.Task294Row80
import LeanLab.DtRS1998.Task294Row75

namespace LeanLab.DtRS1998.Decomp270a

open LeanLab Task71.Paper

/-- P0037 page 207, the displayed recurrence for the sets F.
A prime list and a successful finite offset check certify the interval.
This is CONDITIONAL ON the supplied certificate. -/
theorem interval_of_certificate {B L : ℕ} {qs : List ℕ} (hB : Even B)
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

/-- P0037 page 207, a concrete instance of the finite certificate hypotheses.
The list 3, 5 covers the even integers 6, 8, 10. -/
theorem certificate_instance :
    (∀ q ∈ ([3, 5] : List ℕ), q.Prime) ∧
    (List.range (4 / 2 + 1)).all (fun j =>
      ([3, 5] : List ℕ).any
        (fun q => decide (q ≤ 6 + 2 * j ∧ (6 + 2 * j - q).Prime))) = true := by
  decide +kernel

/-- P0037 page 207, the same certificate gives a nonempty interval instance. -/
theorem interval_instance : IntervalSum 6 4 :=
  interval_of_certificate (by decide) certificate_instance.1 certificate_instance.2

/-- LEAF. P0037 Section 5.1 page 211, unnumbered interval display,
Table 1 page 213, row 10^75. At most 224 certified primes between
10^75 - 55779 and 10^75 cover every even offset through 10^8.
The prime list and finite sieve certificate are OPEN. -/
theorem certificate75 :
    ∃ qs : List ℕ, qs.length ≤ 224 ∧
      (∀ q ∈ qs, q.Prime ∧ 10 ^ 75 - 55779 ≤ q ∧ q ≤ 10 ^ 75) ∧
      (List.range (10 ^ 8 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 75 + 2 * j ∧ (10 ^ 75 + 2 * j - q).Prime))) = true := by
  exact Task294.T75.certificate

/-- LEAF. P0037 Section 5.1 page 211, unnumbered interval display,
Table 1 page 213, row 10^80. At most 206 certified primes between
10^80 - 56907 and 10^80 cover every even offset through 10^8.
The prime list and finite sieve certificate are OPEN. -/
theorem certificate80 :
    ∃ qs : List ℕ, qs.length ≤ 206 ∧
      (∀ q ∈ qs, q.Prime ∧ 10 ^ 80 - 56907 ≤ q ∧ q ≤ 10 ^ 80) ∧
      (List.range (10 ^ 8 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 80 + 2 * j ∧ (10 ^ 80 + 2 * j - q).Prime))) = true := by
  exact Task294.T80.certificate

/-- LEAF. P0037 Section 5.1 page 211, unnumbered interval display,
Table 1 page 213, row 10^85. At most 203 certified primes between
10^85 - 52919 and 10^85 cover every even offset through 10^8.
The prime list and finite sieve certificate are OPEN. -/
theorem certificate85 :
    ∃ qs : List ℕ, qs.length ≤ 203 ∧
      (∀ q ∈ qs, q.Prime ∧ 10 ^ 85 - 52919 ≤ q ∧ q ≤ 10 ^ 85) ∧
      (List.range (10 ^ 8 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 85 + 2 * j ∧ (10 ^ 85 + 2 * j - q).Prime))) = true := by
  exact Task294.T85.certificate

/-- LEAF. P0037 Section 5.1 page 211, unnumbered interval display,
Table 1 page 213, row 10^90. At most 209 certified primes between
10^90 - 65981 and 10^90 cover every even offset through 10^8.
The prime list and finite sieve certificate are OPEN. -/
theorem certificate90 :
    ∃ qs : List ℕ, qs.length ≤ 209 ∧
      (∀ q ∈ qs, q.Prime ∧ 10 ^ 90 - 65981 ≤ q ∧ q ≤ 10 ^ 90) ∧
      (List.range (10 ^ 8 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 90 + 2 * j ∧ (10 ^ 90 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 5.1 page 211, unnumbered interval display,
Table 1 page 213, row 10^95. At most 207 certified primes between
10^95 - 64011 and 10^95 cover every even offset through 10^8.
The prime list and finite sieve certificate are OPEN. -/
theorem certificate95 :
    ∃ qs : List ℕ, qs.length ≤ 207 ∧
      (∀ q ∈ qs, q.Prime ∧ 10 ^ 95 - 64011 ≤ q ∧ q ≤ 10 ^ 95) ∧
      (List.range (10 ^ 8 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 95 + 2 * j ∧ (10 ^ 95 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 5.1 page 211, unnumbered interval display,
Table 1 page 213, row 10^100. At most 250 certified primes between
10^100 - 68969 and 10^100 cover every even offset through 10^8.
The prime list and finite sieve certificate are OPEN. -/
theorem certificate100 :
    ∃ qs : List ℕ, qs.length ≤ 250 ∧
      (∀ q ∈ qs, q.Prime ∧ 10 ^ 100 - 68969 ≤ q ∧ q ≤ 10 ^ 100) ∧
      (List.range (10 ^ 8 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 100 + 2 * j ∧ (10 ^ 100 + 2 * j - q).Prime))) = true := by
  sorry

/-- CONDITIONAL ON the six open Table 1 certificates.
P0037 Section 5.1 pages 211 to 213.
This is the exact statement of Decomp121b.first_family_remaining. -/
theorem first_family_remaining :
    ∀ i : ℕ, 15 ≤ i → i ≤ 20 → IntervalSum (10 ^ (5 * i)) (10 ^ 8) := by
  intro i hlo hhi
  interval_cases i
  · obtain ⟨qs, _, hq, hc⟩ := certificate75
    exact interval_of_certificate (by decide) (fun q h => (hq q h).1) hc
  · obtain ⟨qs, _, hq, hc⟩ := certificate80
    exact interval_of_certificate (by decide) (fun q h => (hq q h).1) hc
  · obtain ⟨qs, _, hq, hc⟩ := certificate85
    exact interval_of_certificate (by decide) (fun q h => (hq q h).1) hc
  · obtain ⟨qs, _, hq, hc⟩ := certificate90
    exact interval_of_certificate (by decide) (fun q h => (hq q h).1) hc
  · obtain ⟨qs, _, hq, hc⟩ := certificate95
    exact interval_of_certificate (by decide) (fun q h => (hq q h).1) hc
  · obtain ⟨qs, _, hq, hc⟩ := certificate100
    exact interval_of_certificate (by decide) (fun q h => (hq q h).1) hc

#print axioms interval_of_certificate

#print axioms certificate_instance

#print axioms interval_instance

#print axioms certificate75

#print axioms certificate80

#print axioms certificate85

#print axioms certificate90

#print axioms certificate95

#print axioms certificate100

#print axioms first_family_remaining

end LeanLab.DtRS1998.Decomp270a
