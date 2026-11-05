/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle2Cert15

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K16 : List ℕ := [3737323, 4448359, 2139495079]

/-- Pocklington entries for chunk 16, page 210. -/
def S16 : List Big.Cert := [(59999999995477, 2, [(2, 2), (3, 2), (19, 1), (41, 1), (2139495079, 1)]),
  (15959, 11, [(2, 1), (79, 1)]),
  (69622853, 3, [(2, 2), (13, 1), (29, 1), (137, 1)]),
  (59999999995459, 2, [(2, 1), (3, 3), (15959, 1), (69622853, 1)]),
  (11261, 2, [(2, 2), (5, 1), (563, 1)]),
  (84033613439, 17, [(2, 1), (109, 1), (11261, 1)]),
  (59999999995447, 5, [(2, 1), (3, 1), (7, 1), (17, 1), (84033613439, 1)]),
  (41210263, 3, [(2, 1), (3, 3), (269, 1)]),
  (54644808739, 2, [(2, 1), (3, 1), (13, 1), (17, 1), (41210263, 1)]),
  (59999999995423, 3, [(2, 1), (3, 2), (61, 1), (54644808739, 1)]),
  (39062499997, 5, [(2, 2), (3, 1), (13, 1), (67, 1), (3737323, 1)]),
  (59999999995393, 7, [(2, 9), (3, 1), (39062499997, 1)]),
  (4643, 5, [(2, 1), (11, 1), (211, 1)]),
  (92861, 2, [(2, 2), (5, 1), (4643, 1)]),
  (185723, 2, [(2, 1), (92861, 1)]),
  (80765441, 3, [(2, 9), (5, 1), (7, 1)]),
  (59999999995373, 2, [(2, 2), (185723, 1), (80765441, 1)]),
  (2657, 3, [(2, 5), (83, 1)]),
  (2677, 2, [(2, 2), (3, 1), (223, 1)]),
  (1536599, 7, [(2, 1), (7, 1), (41, 1), (2677, 1)]),
  (67610357, 2, [(2, 2), (11, 1), (1536599, 1)]),
  (59999999995367, 5, [(2, 1), (167, 1), (2657, 1), (67610357, 1)]),
  (45631, 3, [(2, 1), (3, 3), (5, 1)]),
  (401644063, 3, [(2, 1), (3, 3), (163, 1), (45631, 1)]),
  (59999999995319, 13, [(2, 1), (113, 1), (661, 1), (401644063, 1)]),
  (32822757109, 6, [(2, 2), (3, 2), (19, 1), (23, 1), (109, 1)]),
  (59999999995253, 2, [(2, 2), (457, 1), (32822757109, 1)]),
  (7127, 5, [(2, 1), (7, 1), (509, 1)]),
  (59999999995231, 7, [(2, 1), (3, 1), (5, 1), (41, 1), (7127, 1)]),
  (434782608661, 2, [(2, 2), (3, 3), (5, 1), (181, 1), (4448359, 1)])]

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

end LeanLab.DtRS1998.Task303.Middle2
