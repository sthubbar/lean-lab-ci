/-
AI wrote this Lean code for CODEX task654.
P0037 Section 5.2 page 212, regenerated candidate at index 202.
Every modular witness and every auxiliary prime is checked in Lean.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Pock

namespace LeanLab.DtRS1998.Recut654Prime202

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- The auxiliary Pocklington records for this candidate. -/
def factorChain : List Big.Cert := [(1031, 14, [(2, 1), (5, 1), (103, 1)]),
  (2063, 5, [(2, 1), (1031, 1)]),
  (18803, 5, [(2, 1), (7, 1), (17, 1), (79, 1)]),
  (4987, 2, [(2, 1), (3, 2), (277, 1)]),
  (6600244631, 13, [(2, 1), (5, 1), (7, 2), (37, 1), (73, 1), (4987, 1)]),
  (13397, 2, [(2, 2), (17, 1), (197, 1)]),
  (187559, 7, [(2, 1), (7, 1), (13397, 1)]),
  (375119, 17, [(2, 1), (187559, 1)]),
  (99031417, 47, [(2, 3), (3, 1), (11, 1), (375119, 1)]),
  (8318639029, 2, [(2, 2), (3, 1), (7, 1), (99031417, 1)]),
  (5477, 2, [(2, 2), (37, 2)]),
  (21803, 2, [(2, 1), (11, 1), (991, 1)]),
  (2005877, 2, [(2, 2), (23, 1), (21803, 1)]),
  (20302476031993, 5, [(2, 3), (3, 1), (7, 1), (11, 1), (5477, 1), (2005877, 1)]),
  (469011061, 2, [(2, 2), (3, 4), (5, 1), (7, 1), (59, 1), (701, 1)]),
  (41375217779299, 2, [(2, 1), (3, 2), (13, 2), (29, 1), (469011061, 1)]),
  (17359, 3, [(2, 1), (3, 1), (11, 1), (263, 1)]),
  (4383807143, 7, [(2, 1), (11, 1), (13, 1), (883, 1), (17359, 1)]),
  (271796042867, 2, [(2, 1), (31, 1), (4383807143, 1)]),
  (15284178674582879, 31, [(2, 1), (31, 1), (907, 1), (271796042867, 1)]),
  (122273429396663033, 3, [(2, 3), (15284178674582879, 1)])]

/-- Every listed auxiliary number is prime by its own Pocklington witness. -/
theorem factor_primes : ∀ p ∈ factorChain.map Prod.fst, p.Prime := by
  intro p hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact Big.chainP_sound factorChain [] (by simp) (by decide +kernel) c hc

/-- The factored part for certificate node 0. -/
def factors_0 : List (ℕ × ℕ) := [(2, 2), (73, 2), (157, 1), (20302476031993, 1)]

/-- Certificate node 0 is prime by its explicit modular witnesses. -/
theorem prime_node_0 : (67944509918380157717 : ℕ).Prime := by
  have hprimes : ∀ x ∈ factors_0, x.1.Prime := by
    intro x hx
    simp only [factors_0, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
  exact Big.pock 67944509918380157717 2 66 factors_0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hprimes (by decide +kernel) (by decide +kernel)

/-- The factored part for certificate node 1. -/
def factors_1 : List (ℕ × ℕ) := [(2, 2), (5, 3), (13, 1), (2063, 1), (6600244631, 1), (8318639029, 1), (41375217779299, 1), (122273429396663033, 1), (67944509918380157717, 1)]

/-- Certificate node 1 is prime by its explicit modular witnesses. -/
theorem prime_node_1 : (12662619693412651983092870185355427072174399728513433773232741482488863225979643572580869820671979901890022615438772434996441803866151044792750903477915124992718993676287725109721599643420629501 : ℕ).Prime := by
  have hprimes : ∀ x ∈ factors_1, x.1.Prime := by
    intro x hx
    simp only [factors_1, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact prime_node_0
  apply Recut654Pock.prime_of_factor_divisibility 12662619693412651983092870185355427072174399728513433773232741482488863225979643572580869820671979901890022615438772434996441803866151044792750903477915124992718993676287725109721599643420629501 253076402686628191279482583065537035463593220036501180116213638930539754479500 121570562418418728477382972975955835753521301576519078082252141312940704315700
    (by decide +kernel) (by decide +kernel)
  · exact Recut654Pock.factor_congruence 12662619693412651983092870185355427072174399728513433773232741482488863225979643572580869820671979901890022615438772434996441803866151044792750903477915124992718993676287725109721599643420629501 3 642 factors_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hprimes
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

/-- The factored part for certificate node 2. -/
def factors_2 : List (ℕ × ℕ) := [(2, 2), (3, 1), (5, 1), (7, 1), (18803, 1), (12662619693412651983092870185355427072174399728513433773232741482488863225979643572580869820671979901890022615438772434996441803866151044792750903477915124992718993676287725109721599643420629501, 1)]

/-- Certificate node 2 is prime by its explicit modular witnesses. -/
theorem prime_node_2 : (100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000533067261 : ℕ).Prime := by
  have hprimes : ∀ x ∈ factors_2, x.1.Prime := by
    intro x hx
    simp only [factors_2, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact LeanLab.primeB_sound (by decide +kernel)
    · exact factor_primes _ (by decide +kernel)
    · exact prime_node_1
  exact Big.pock 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000533067261 13 665 factors_2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hprimes (by decide +kernel) (by decide +kernel)

/-- LEAF: The regenerated candidate at index 202 is prime. -/
theorem candidate202_prime : (10 ^ 200 + 533067261 : ℕ).Prime := prime_node_2

end LeanLab.DtRS1998.Recut654Prime202
