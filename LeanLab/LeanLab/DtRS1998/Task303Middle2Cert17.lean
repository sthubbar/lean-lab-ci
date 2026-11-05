/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle2Cert16

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K17 : List ℕ := [2089, 3737323, 434782608661]

/-- Pocklington entries for chunk 17, page 210. -/
def S17 : List Big.Cert := [(59999999995219, 7, [(2, 1), (3, 1), (23, 1), (434782608661, 1)]),
  (32512043, 2, [(2, 1), (43, 1), (257, 1)]),
  (59999999995211, 2, [(2, 1), (5, 1), (11, 1), (19, 1), (883, 1), (32512043, 1)]),
  (45959, 7, [(2, 1), (11, 1), (2089, 1)]),
  (12583, 5, [(2, 1), (3, 3), (233, 1)]),
  (72528413, 2, [(2, 2), (11, 1), (131, 1), (12583, 1)]),
  (59999999995207, 3, [(2, 1), (3, 2), (45959, 1), (72528413, 1)]),
  (510777403, 2, [(2, 1), (3, 1), (101, 1), (113, 1)]),
  (3064664419, 2, [(2, 1), (3, 1), (510777403, 1)]),
  (59999999995183, 5, [(2, 1), (3, 1), (13, 1), (251, 1), (3064664419, 1)]),
  (2143, 3, [(2, 1), (3, 2), (7, 1)]),
  (8573, 2, [(2, 2), (2143, 1)]),
  (102877, 2, [(2, 2), (3, 1), (8573, 1)]),
  (177771457, 7, [(2, 6), (3, 3), (102877, 1)]),
  (714285714227, 2, [(2, 1), (7, 2), (41, 1), (177771457, 1)]),
  (59999999995069, 2, [(2, 2), (3, 1), (7, 1), (714285714227, 1)]),
  (49751243777, 3, [(2, 10), (13, 1), (3737323, 1)]),
  (59999999995063, 6, [(2, 1), (3, 2), (67, 1), (49751243777, 1)]),
  (336227, 2, [(2, 1), (11, 1), (17, 1), (29, 1)]),
  (182839, 21, [(2, 1), (3, 1), (31, 1), (983, 1)]),
  (44612717, 2, [(2, 2), (61, 1), (182839, 1)]),
  (59999999995037, 2, [(2, 2), (336227, 1), (44612717, 1)]),
  (52083333329, 3, [(2, 4), (13, 1), (67, 1), (3737323, 1)]),
  (59999999995009, 17, [(2, 7), (3, 2), (52083333329, 1)]),
  (77611, 2, [(2, 1), (3, 1), (5, 1), (13, 1)]),
  (627562547, 5, [(2, 1), (13, 1), (311, 1), (77611, 1)]),
  (42674253197, 2, [(2, 2), (17, 1), (627562547, 1)]),
  (59999999994983, 5, [(2, 1), (19, 1), (37, 1), (42674253197, 1)]),
  (5443, 2, [(2, 1), (3, 1), (907, 1)]),
  (9999999999161, 3, [(2, 3), (5, 1), (331, 1), (5443, 1)])]

/-- Kernel acceptance of chunk 17, page 210. -/
theorem chain17 : Big.chainP K17 S17 = true := by decide +kernel

/-- Each entry of chunk 17 is prime, page 210. -/
theorem primes17 : ∀ c ∈ S17, c.1.Prime := by
  apply Big.chainP_sound S17 K17 ?_ chain17
  intro p hp
  have hm : K17.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10 ++ (S11 ++ (S12 ++ (S13 ++ (S14 ++ (S15 ++ (S16))))))))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16
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
  · exact primes16 c h16

#print axioms chain17
#print axioms primes17

end LeanLab.DtRS1998.Task303.Middle2
