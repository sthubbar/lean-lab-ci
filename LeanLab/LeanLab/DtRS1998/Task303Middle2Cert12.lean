/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle2Cert11

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K12 : List ℕ := [9967, 501655463]

/-- Pocklington entries for chunk 12, page 210. -/
def S12 : List Big.Cert := [(9999999999443, 2, [(2, 1), (9967, 1), (501655463, 1)]),
  (59999999996659, 3, [(2, 1), (3, 1), (9999999999443, 1)]),
  (18691, 3, [(2, 1), (3, 1), (5, 1), (7, 1)]),
  (59999999996539, 2, [(2, 1), (3, 4), (7, 1), (29, 1), (18691, 1)]),
  (1543, 5, [(2, 1), (3, 1), (257, 1)]),
  (6173, 2, [(2, 2), (1543, 1)]),
  (1619957881, 19, [(2, 3), (3, 4), (5, 1), (17, 1)]),
  (59999999996479, 3, [(2, 1), (3, 1), (6173, 1), (1619957881, 1)]),
  (1279, 3, [(2, 1), (3, 2), (71, 1)]),
  (38371, 10, [(2, 1), (3, 1), (5, 1), (1279, 1)]),
  (230227, 7, [(2, 1), (3, 1), (38371, 1)]),
  (1843657817, 5, [(2, 3), (7, 1), (11, 1), (13, 1), (230227, 1)]),
  (2499999999853, 2, [(2, 2), (3, 1), (113, 1), (1843657817, 1)]),
  (59999999996473, 7, [(2, 3), (3, 1), (2499999999853, 1)]),
  (19009, 23, [(2, 6), (3, 3)]),
  (59999999996401, 7, [(2, 4), (3, 1), (5, 2), (19009, 1)]),
  (59999999996389, 6, [(2, 2), (3, 1), (19, 1), (37, 1), (47, 1), (131, 1)]),
  (1187, 2, [(2, 1), (593, 1)]),
  (19211, 6, [(2, 1), (5, 1), (17, 1)]),
  (8424599831, 7, [(2, 1), (5, 1), (19211, 1)]),
  (59999999996383, 10, [(2, 1), (3, 1), (1187, 1), (8424599831, 1)]),
  (55373, 2, [(2, 2), (109, 1)]),
  (6019781, 2, [(2, 2), (5, 1), (13, 3)]),
  (3333333333131, 2, [(2, 1), (5, 1), (55373, 1), (6019781, 1)]),
  (59999999996359, 3, [(2, 1), (3, 2), (3333333333131, 1)]),
  (9817, 5, [(2, 3), (3, 1), (409, 1)]),
  (59999999996333, 2, [(2, 2), (11, 1), (43, 1), (9817, 1)]),
  (13249, 7, [(2, 6), (3, 2)]),
  (96161243, 2, [(2, 1), (19, 1), (191, 1), (13249, 1)]),
  (576967459, 19, [(2, 1), (3, 1), (96161243, 1)])]

/-- Kernel acceptance of chunk 12, page 210. -/
theorem chain12 : Big.chainP K12 S12 = true := by decide +kernel

/-- Each entry of chunk 12 is prime, page 210. -/
theorem primes12 : ∀ c ∈ S12, c.1.Prime := by
  apply Big.chainP_sound S12 K12 ?_ chain12
  intro p hp
  have hm : K12.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10 ++ (S11)))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
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

#print axioms chain12
#print axioms primes12

end LeanLab.DtRS1998.Task303.Middle2
