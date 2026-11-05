/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert10

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K11 : List ℕ := [1831, 6163, 7477, 121889]

/-- Pocklington entries for chunk 11, page 210. -/
def S11 : List Big.Cert := [(46805377, 7, [(2, 7), (3, 1), (121889, 1)]),
  (22499999999179, 2, [(2, 1), (3, 1), (13, 1), (6163, 1), (46805377, 1)]),
  (89999999996717, 2, [(2, 2), (22499999999179, 1)]),
  (17669, 2, [(2, 2), (7, 1), (631, 1)]),
  (89999999996707, 2, [(2, 1), (3, 2), (113, 1), (17669, 1)]),
  (299999999989, 26, [(2, 2), (3, 2), (13, 1), (7477, 1)]),
  (89999999996701, 2, [(2, 2), (3, 1), (5, 2), (299999999989, 1)]),
  (416666666651, 6, [(2, 1), (5, 2), (13, 1), (7477, 1)]),
  (7499999999719, 3, [(2, 1), (3, 2), (416666666651, 1)]),
  (89999999996629, 2, [(2, 2), (3, 1), (7499999999719, 1)]),
  (6997, 5, [(2, 2), (3, 1), (11, 1)]),
  (1175497, 5, [(2, 3), (3, 1), (7, 1), (6997, 1)]),
  (13513513513, 5, [(2, 3), (3, 1), (479, 1), (1175497, 1)]),
  (8999999999659, 3, [(2, 1), (3, 2), (37, 1), (13513513513, 1)]),
  (89999999996591, 11, [(2, 1), (5, 1), (8999999999659, 1)]),
  (89999999996581, 6, [(2, 2), (3, 2), (5, 1), (37, 1), (13513513513, 1)]),
  (8951, 13, [(2, 1), (5, 2), (179, 1)]),
  (179021, 2, [(2, 2), (5, 1), (8951, 1)]),
  (7536426059, 2, [(2, 1), (7, 1), (31, 1), (97, 1), (179021, 1)]),
  (89999999996579, 2, [(2, 1), (7, 1), (853, 1), (7536426059, 1)]),
  (4061371841, 3, [(2, 6), (5, 1), (853, 1)]),
  (89999999996561, 6, [(2, 4), (5, 1), (277, 1), (4061371841, 1)]),
  (1319, 13, [(2, 1), (659, 1)]),
  (31657, 5, [(2, 3), (3, 1), (1319, 1)]),
  (95723, 2, [(2, 1), (11, 1), (19, 1)]),
  (157942951, 6, [(2, 1), (3, 1), (5, 2), (11, 1), (95723, 1)]),
  (89999999996527, 6, [(2, 1), (3, 2), (31657, 1), (157942951, 1)]),
  (18311, 13, [(2, 1), (5, 1), (1831, 1)]),
  (51198733, 2, [(2, 2), (3, 2), (13, 1), (31, 1)]),
  (89999999996449, 23, [(2, 5), (3, 1), (18311, 1), (51198733, 1)])]

/-- Kernel acceptance of chunk 11, page 210. -/
theorem chain11 : Big.chainP K11 S11 = true := by decide +kernel

/-- Each entry of chunk 11 is prime, page 210. -/
theorem primes11 : ∀ c ∈ S11, c.1.Prime := by
  apply Big.chainP_sound S11 K11 ?_ chain11
  intro p hp
  have hm : K11.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
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
  · exact primes10 c h10

#print axioms chain11
#print axioms primes11

end LeanLab.DtRS1998.Task303.High
