/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle1Cert14

namespace LeanLab.DtRS1998.Task303.Middle1

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K15 : List ℕ := [1279, 7933]

/-- Pocklington entries for chunk 15, page 210. -/
def S15 : List Big.Cert := [(19999999995757, 5, [(2, 2), (3, 1), (11, 1), (19, 1), (7933, 1)]),
  (6917, 2, [(2, 2), (7, 1), (13, 1)]),
  (7719373, 2, [(2, 2), (3, 2), (31, 1), (6917, 1)]),
  (19999999995733, 2, [(2, 2), (3, 2), (79, 1), (911, 1), (7719373, 1)]),
  (19999999995589, 2, [(2, 2), (3, 2), (163, 1), (1279, 1)]),
  (96997, 2, [(2, 2), (3, 1), (59, 1)]),
  (5858230813, 5, [(2, 2), (3, 1), (7, 1), (719, 1), (96997, 1)]),
  (19999999995583, 3, [(2, 1), (3, 1), (569, 1), (5858230813, 1)]),
  (1901719, 3, [(2, 1), (3, 5), (7, 1)]),
  (19017191, 7, [(2, 1), (5, 1), (1901719, 1)]),
  (38034383, 5, [(2, 1), (19017191, 1)]),
  (532481363, 2, [(2, 1), (7, 1), (38034383, 1)]),
  (15974440891, 3, [(2, 1), (3, 1), (5, 1), (532481363, 1)]),
  (19999999995533, 2, [(2, 2), (313, 1), (15974440891, 1)]),
  (356287, 5, [(2, 1), (3, 1), (7, 1), (17, 1)]),
  (6413167, 3, [(2, 1), (3, 2), (356287, 1)]),
  (19999999995529, 13, [(2, 3), (3, 1), (7, 1), (19, 1), (977, 1), (6413167, 1)]),
  (3103801, 19, [(2, 3), (3, 1), (5, 2), (7, 1)]),
  (111736837, 14, [(2, 2), (3, 2), (3103801, 1)]),
  (446947349, 2, [(2, 2), (111736837, 1)]),
  (893894699, 2, [(2, 1), (446947349, 1)]),
  (19999999995427, 2, [(2, 1), (3, 2), (11, 1), (113, 1), (893894699, 1)]),
  (69313, 10, [(2, 6), (3, 1), (19, 2)]),
  (2799552071, 14, [(2, 1), (5, 1), (7, 1), (577, 1), (69313, 1)]),
  (106382978699, 2, [(2, 1), (19, 1), (2799552071, 1)]),
  (19999999995413, 2, [(2, 2), (47, 1), (106382978699, 1)]),
  (476190476081, 3, [(2, 4), (5, 1), (11, 2), (797, 1)]),
  (19999999995403, 3, [(2, 1), (3, 1), (7, 1), (476190476081, 1)]),
  (987361769, 3, [(2, 3), (17, 1), (419, 1)]),
  (7898894153, 3, [(2, 3), (987361769, 1)])]

/-- Kernel acceptance of chunk 15, page 210. -/
theorem chain15 : Big.chainP K15 S15 = true := by decide +kernel

/-- Each entry of chunk 15 is prime, page 210. -/
theorem primes15 : ∀ c ∈ S15, c.1.Prime := by
  apply Big.chainP_sound S15 K15 ?_ chain15
  intro p hp
  have hm : K15.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10 ++ (S11 ++ (S12 ++ (S13 ++ (S14))))))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
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

#print axioms chain15
#print axioms primes15

end LeanLab.DtRS1998.Task303.Middle1
