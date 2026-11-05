/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert8

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K9 : List ℕ := [1601, 1232377]

/-- Pocklington entries for chunk 9, page 210. -/
def S9 : List Big.Cert := [(399999997447, 3, [(2, 1), (3, 1), (7, 2), (43, 1), (1601, 1)]),
  (29129, 3, [(2, 3), (11, 1), (331, 1)]),
  (407807, 5, [(2, 1), (7, 1), (29129, 1)]),
  (7340527, 3, [(2, 1), (3, 2), (407807, 1)]),
  (3508771907, 2, [(2, 1), (239, 1), (7340527, 1)]),
  (399999997399, 15, [(2, 1), (3, 1), (19, 1), (3508771907, 1)]),
  (2537749, 2, [(2, 2), (3, 2), (157, 1)]),
  (399999997381, 6, [(2, 2), (3, 1), (5, 1), (37, 1), (71, 1), (2537749, 1)]),
  (50849, 3, [(2, 5), (7, 1), (227, 1)]),
  (1966607, 5, [(2, 1), (29, 1), (41, 1)]),
  (399999997373, 2, [(2, 2), (50849, 1), (1966607, 1)]),
  (87950747, 2, [(2, 1), (13, 1), (499, 1)]),
  (399999997357, 6, [(2, 2), (3, 1), (379, 1), (87950747, 1)]),
  (1459, 3, [(2, 1), (3, 6)]),
  (399999997339, 15, [(2, 1), (3, 1), (67, 1), (233, 1), (1459, 1)]),
  (116371, 10, [(2, 1), (3, 3), (5, 1), (431, 1)]),
  (1396453, 2, [(2, 2), (3, 1), (116371, 1)]),
  (399999997321, 39, [(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (31, 1), (1396453, 1)]),
  (2777777759, 7, [(2, 1), (7, 2), (23, 1), (1232377, 1)]),
  (399999997297, 10, [(2, 4), (3, 2), (2777777759, 1)]),
  (5482907, 2, [(2, 1), (11, 1), (13, 1), (19, 1)]),
  (399999997279, 3, [(2, 1), (3, 3), (7, 1), (193, 1), (5482907, 1)]),
  (1181, 7, [(2, 2), (5, 1), (59, 1)]),
  (399999997259, 2, [(2, 1), (31, 1), (139, 1), (1181, 1)]),
  (131371, 2, [(2, 1), (3, 1), (5, 1), (29, 1)]),
  (3253, 2, [(2, 2), (3, 1), (271, 1)]),
  (761203, 3, [(2, 1), (3, 2), (13, 1), (3253, 1)]),
  (399999997253, 2, [(2, 2), (131371, 1), (761203, 1)]),
  (21661, 2, [(2, 2), (3, 1), (5, 1), (19, 2)]),
  (399999997249, 7, [(2, 6), (3, 1), (21661, 1)])]

/-- Kernel acceptance of chunk 9, page 210. -/
theorem chain9 : Big.chainP K9 S9 = true := by decide +kernel

/-- Each entry of chunk 9 is prime, page 210. -/
theorem primes9 : ∀ c ∈ S9, c.1.Prime := by
  apply Big.chainP_sound S9 K9 ?_ chain9
  intro p hp
  have hm : K9.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2
  · exact primes3 c h3
  · exact primes4 c h4
  · exact primes5 c h5
  · exact primes6 c h6
  · exact primes7 c h7
  · exact primes8 c h8

#print axioms chain9
#print axioms primes9

end LeanLab.DtRS1998.Task303.Low
