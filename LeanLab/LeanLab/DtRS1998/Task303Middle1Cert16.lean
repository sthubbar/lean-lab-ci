/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle1Cert15

namespace LeanLab.DtRS1998.Task303.Middle1

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K16 : List ℕ := [7898894153]

/-- Pocklington entries for chunk 16, page 210. -/
def S16 : List Big.Cert := [(19999999995397, 2, [(2, 2), (3, 1), (211, 1), (7898894153, 1)]),
  (16241597, 2, [(2, 2), (7, 1), (17, 1), (149, 1)]),
  (19999999995383, 5, [(2, 1), (11, 1), (223, 1), (251, 1), (16241597, 1)]),
  (19999999995361, 17, [(2, 5), (3, 1), (5, 1), (7, 1), (11, 2), (797, 1)]),
  (1459, 3, [(2, 1), (3, 6)]),
  (4951, 6, [(2, 1), (3, 2), (5, 2)]),
  (1891283, 2, [(2, 1), (191, 1), (4951, 1)]),
  (3427004797, 2, [(2, 2), (3, 1), (151, 1), (1891283, 1)]),
  (19999999995293, 2, [(2, 2), (1459, 1), (3427004797, 1)]),
  (833333333137, 15, [(2, 4), (3, 1), (607, 1), (701, 1)]),
  (19999999995289, 7, [(2, 3), (3, 1), (833333333137, 1)]),
  (52747, 3, [(2, 1), (3, 1), (59, 1)]),
  (1793399, 11, [(2, 1), (17, 1), (52747, 1)]),
  (238095238039, 3, [(2, 1), (3, 1), (7, 1), (29, 1), (109, 1), (1793399, 1)]),
  (19999999995277, 5, [(2, 2), (3, 1), (7, 1), (238095238039, 1)]),
  (186311, 13, [(2, 1), (5, 1), (31, 1), (601, 1)]),
  (676681553, 3, [(2, 4), (227, 1), (186311, 1)]),
  (1353363107, 2, [(2, 1), (676681553, 1)]),
  (19999999995247, 3, [(2, 1), (3, 2), (821, 1), (1353363107, 1)]),
  (21211, 2, [(2, 1), (3, 1), (5, 1), (7, 1)]),
  (1439, 7, [(2, 1), (719, 1)]),
  (189949, 14, [(2, 2), (3, 1), (11, 1), (1439, 1)]),
  (6458267, 2, [(2, 1), (17, 1), (189949, 1)]),
  (19999999995203, 2, [(2, 1), (73, 1), (21211, 1), (6458267, 1)]),
  (100767851, 2, [(2, 1), (5, 2), (719, 1)]),
  (19999999995077, 2, [(2, 2), (29, 2), (59, 1), (100767851, 1)]),
  (2203, 5, [(2, 1), (3, 1), (367, 1)]),
  (19999999995029, 2, [(2, 2), (107, 1), (739, 1), (2203, 1)]),
  (2719, 3, [(2, 1), (3, 2), (151, 1)]),
  (217391304293, 2, [(2, 2), (293, 1), (2719, 1)])]

/-- Kernel acceptance of chunk 16, page 210. -/
theorem chain16 : Big.chainP K16 S16 = true := by decide +kernel

/-- Each entry of chunk 16 is prime, page 210. -/
theorem primes16 : ∀ c ∈ S16, c.1.Prime := by
  apply Big.chainP_sound S16 K16 ?_ chain16
  intro p hp
  have hm : K16.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10 ++ (S11 ++ (S12 ++ (S13 ++ (S14 ++ (S15)))))))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
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
  · exact primes11 c h11
  · exact primes12 c h12
  · exact primes13 c h13
  · exact primes14 c h14
  · exact primes15 c h15

#print axioms chain16
#print axioms primes16

end LeanLab.DtRS1998.Task303.Middle1
