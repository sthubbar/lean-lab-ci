/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle2Cert13

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K14 : List ℕ := [2089, 2141]

/-- Pocklington entries for chunk 14, page 210. -/
def S14 : List Big.Cert := [(1637, 2, [(2, 2), (409, 1)]),
  (5827, 2, [(2, 1), (3, 1), (971, 1)]),
  (34963, 2, [(2, 1), (3, 1), (5827, 1)]),
  (54542281, 53, [(2, 3), (3, 1), (5, 1), (13, 1), (34963, 1)]),
  (327253687, 3, [(2, 1), (3, 1), (54542281, 1)]),
  (9163103237, 5, [(2, 2), (7, 1), (327253687, 1)]),
  (59999999995877, 2, [(2, 2), (1637, 1), (9163103237, 1)]),
  (2647, 3, [(2, 1), (3, 3)]),
  (59999999995861, 2, [(2, 2), (3, 1), (5, 1), (53, 1), (277, 1), (2647, 1)]),
  (193099897, 5, [(2, 3), (3, 3), (11, 1), (67, 1)]),
  (59999999995841, 3, [(2, 6), (5, 1), (971, 1), (193099897, 1)]),
  (7721173, 5, [(2, 2), (3, 2), (139, 1)]),
  (142857142847, 5, [(2, 1), (11, 1), (29, 2), (7721173, 1)]),
  (857142857083, 2, [(2, 1), (3, 1), (142857142847, 1)]),
  (59999999995811, 2, [(2, 1), (5, 1), (7, 1), (857142857083, 1)]),
  (128461, 10, [(2, 2), (3, 1), (5, 1), (2141, 1)]),
  (572387, 2, [(2, 1), (137, 1), (2089, 1)]),
  (13737289, 7, [(2, 3), (3, 1), (572387, 1)]),
  (59999999995787, 2, [(2, 1), (17, 1), (128461, 1), (13737289, 1)]),
  (14430014429, 2, [(2, 2), (293, 1), (443, 1)]),
  (59999999995783, 6, [(2, 1), (3, 3), (7, 1), (11, 1), (14430014429, 1)]),
  (3631, 15, [(2, 1), (3, 1), (5, 1), (11, 2)]),
  (14737, 10, [(2, 4), (3, 1), (307, 1)]),
  (235793, 3, [(2, 4), (14737, 1)]),
  (1712328767, 5, [(2, 1), (3631, 1), (235793, 1)]),
  (1499999999893, 5, [(2, 2), (3, 1), (73, 1), (1712328767, 1)]),
  (59999999995721, 6, [(2, 3), (5, 1), (1499999999893, 1)]),
  (278086763, 2, [(2, 1), (43, 1), (823, 1)]),
  (5561735261, 2, [(2, 2), (5, 1), (278086763, 1)]),
  (59999999995669, 2, [(2, 2), (3, 1), (29, 1), (31, 1), (5561735261, 1)])]

/-- Kernel acceptance of chunk 14, page 210. -/
theorem chain14 : Big.chainP K14 S14 = true := by decide +kernel

/-- Each entry of chunk 14 is prime, page 210. -/
theorem primes14 : ∀ c ∈ S14, c.1.Prime := by
  apply Big.chainP_sound S14 K14 ?_ chain14
  intro p hp
  have hm : K14.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10 ++ (S11 ++ (S12 ++ (S13)))))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
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

#print axioms chain14
#print axioms primes14

end LeanLab.DtRS1998.Task303.Middle2
