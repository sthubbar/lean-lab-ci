/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert9

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K10 : List ℕ := [114130931]

/-- Pocklington entries for chunk 10, page 210. -/
def S10 : List Big.Cert := [(517241379293, 2, [(2, 2), (11, 1), (103, 1), (114130931, 1)]),
  (89999999996983, 3, [(2, 1), (3, 1), (29, 1), (517241379293, 1)]),
  (89999999996969, 3, [(2, 3), (157, 1), (619, 1), (683, 1)]),
  (6053, 2, [(2, 2), (17, 1), (89, 1)]),
  (4999999999829, 2, [(2, 2), (41, 2), (6053, 1)]),
  (89999999996923, 2, [(2, 1), (3, 2), (4999999999829, 1)]),
  (10831, 7, [(2, 1), (3, 1), (5, 1), (19, 2)]),
  (4154741021, 2, [(2, 2), (5, 1), (19, 1), (53, 1), (67, 1)]),
  (89999999996903, 5, [(2, 1), (10831, 1), (4154741021, 1)]),
  (107509, 6, [(2, 2), (3, 1), (17, 2)]),
  (51604321, 7, [(2, 5), (3, 1), (5, 1), (107509, 1)]),
  (4499999999843, 2, [(2, 1), (59, 1), (739, 1), (51604321, 1)]),
  (89999999996861, 2, [(2, 2), (5, 1), (4499999999843, 1)]),
  (34722222221, 3, [(2, 2), (5, 1), (7, 2), (17, 1), (19, 1)]),
  (5624999999803, 2, [(2, 1), (3, 4), (34722222221, 1)]),
  (89999999996849, 3, [(2, 4), (5624999999803, 1)]),
  (89999999996833, 7, [(2, 5), (3, 4), (34722222221, 1)]),
  (5197, 7, [(2, 2), (3, 1), (433, 1)]),
  (51971, 2, [(2, 1), (5, 1), (5197, 1)]),
  (288622501, 2, [(2, 2), (3, 1), (5, 4), (29, 1)]),
  (89999999996827, 2, [(2, 1), (3, 1), (51971, 1), (288622501, 1)]),
  (1583, 5, [(2, 1), (7, 1), (113, 1)]),
  (4523, 5, [(2, 1), (7, 1), (17, 1)]),
  (54277, 5, [(2, 2), (3, 1), (4523, 1)]),
  (22036463, 5, [(2, 1), (7, 1), (29, 1), (54277, 1)]),
  (89999999996821, 2, [(2, 2), (3, 1), (5, 1), (43, 1), (1583, 1), (22036463, 1)]),
  (113147, 2, [(2, 1), (11, 1), (37, 1)]),
  (89999999996741, 2, [(2, 2), (5, 1), (41, 1), (113147, 1)]),
  (6163, 3, [(2, 1), (3, 1), (13, 1)]),
  (121889, 3, [(2, 5), (13, 1)])]

/-- Kernel acceptance of chunk 10, page 210. -/
theorem chain10 : Big.chainP K10 S10 = true := by decide +kernel

/-- Each entry of chunk 10 is prime, page 210. -/
theorem primes10 : ∀ c ∈ S10, c.1.Prime := by
  apply Big.chainP_sound S10 K10 ?_ chain10
  intro p hp
  have hm : K10.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9)))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2
  · exact primes3 c h3
  · exact primes4 c h4
  · exact primes5 c h5
  · exact primes6 c h6
  · exact primes7 c h7
  · exact primes8 c h8
  · exact primes9 c h9

#print axioms chain10
#print axioms primes10

end LeanLab.DtRS1998.Task303.High
