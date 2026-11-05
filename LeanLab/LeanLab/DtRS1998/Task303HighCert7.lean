/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert6

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K7 : List ℕ := [5581, 387781, 38681627]

/-- Pocklington entries for chunk 7, page 210. -/
def S7 : List Big.Cert := [(89999999998123, 3, [(2, 1), (3, 1), (387781, 1), (38681627, 1)]),
  (89999999998049, 3, [(2, 5), (7, 1), (17, 1), (23, 1), (313, 1)]),
  (1381, 2, [(2, 2), (3, 1), (5, 1)]),
  (24859, 2, [(2, 1), (3, 2), (1381, 1)]),
  (1211653, 2, [(2, 2), (3, 3), (13, 1)]),
  (542168674687, 5, [(2, 1), (3, 2), (24859, 1), (1211653, 1)]),
  (89999999998043, 2, [(2, 1), (83, 1), (542168674687, 1)]),
  (15679, 11, [(2, 1), (3, 2), (13, 1)]),
  (89999999998001, 3, [(2, 4), (5, 3), (15679, 1)]),
  (130457, 3, [(2, 3), (23, 1), (709, 1)]),
  (89999999997931, 2, [(2, 1), (3, 2), (5, 1), (11, 1), (130457, 1)]),
  (2549, 2, [(2, 2), (7, 2)]),
  (5099, 2, [(2, 1), (2549, 1)]),
  (601732991, 17, [(2, 1), (5, 1), (5099, 1)]),
  (89999999997889, 17, [(2, 6), (3, 1), (19, 1), (41, 1), (601732991, 1)]),
  (146521, 23, [(2, 3), (3, 2), (5, 1), (11, 1)]),
  (89999999997863, 7, [(2, 1), (127, 1), (146521, 1)]),
  (1619, 2, [(2, 1), (809, 1)]),
  (1171, 2, [(2, 1), (3, 2), (5, 1)]),
  (351301, 13, [(2, 2), (3, 1), (5, 2), (1171, 1)]),
  (1137512639, 7, [(2, 1), (1619, 1), (351301, 1)]),
  (978260869541, 2, [(2, 2), (5, 1), (43, 1), (1137512639, 1)]),
  (89999999997773, 2, [(2, 2), (23, 1), (978260869541, 1)]),
  (89999999997751, 3, [(2, 1), (3, 3), (5, 3), (163, 1), (409, 1)]),
  (89999999997709, 2, [(2, 2), (3, 1), (17, 1), (61, 1), (139, 1), (5581, 1)]),
  (1093, 5, [(2, 2), (3, 1), (7, 1)]),
  (50940359, 13, [(2, 1), (7, 1), (1093, 1)]),
  (1935733643, 2, [(2, 1), (19, 1), (50940359, 1)]),
  (89999999997643, 5, [(2, 1), (3, 4), (7, 1), (41, 1), (1935733643, 1)]),
  (1901, 2, [(2, 2), (5, 2)])]

/-- Kernel acceptance of chunk 7, page 210. -/
theorem chain7 : Big.chainP K7 S7 = true := by decide +kernel

/-- Each entry of chunk 7 is prime, page 210. -/
theorem primes7 : ∀ c ∈ S7, c.1.Prime := by
  apply Big.chainP_sound S7 K7 ?_ chain7
  intro p hp
  have hm : K7.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2
  · exact primes3 c h3
  · exact primes4 c h4
  · exact primes5 c h5
  · exact primes6 c h6

#print axioms chain7
#print axioms primes7

end LeanLab.DtRS1998.Task303.High
