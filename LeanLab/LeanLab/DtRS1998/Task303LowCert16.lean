/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert15

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K16 : List ℕ := [272759, 8398421]

/-- Pocklington entries for chunk 16, page 210. -/
def S16 : List Big.Cert := [(9029, 2, [(2, 2), (37, 1)]),
  (18059, 2, [(2, 1), (9029, 1)]),
  (1083541, 2, [(2, 2), (3, 1), (5, 1), (18059, 1)]),
  (399999995561, 3, [(2, 3), (5, 1), (11, 1), (839, 1), (1083541, 1)]),
  (1279, 3, [(2, 1), (3, 2), (71, 1)]),
  (399999995513, 3, [(2, 3), (13, 1), (257, 1), (1279, 1)]),
  (8123, 2, [(2, 1), (31, 1), (131, 1)]),
  (4924289, 3, [(2, 7), (17, 1), (31, 1)]),
  (399999995471, 13, [(2, 1), (5, 1), (8123, 1), (4924289, 1)]),
  (364963499, 2, [(2, 1), (59, 1), (991, 1)]),
  (729926999, 7, [(2, 1), (364963499, 1)]),
  (399999995453, 2, [(2, 2), (137, 1), (729926999, 1)]),
  (399999995393, 3, [(2, 9), (71, 1), (151, 1)]),
  (399999995389, 2, [(2, 2), (3, 5), (7, 2), (8398421, 1)]),
  (185185183, 3, [(2, 1), (3, 1), (7, 1), (13, 1), (17, 1), (71, 1)]),
  (4444444393, 10, [(2, 3), (3, 1), (185185183, 1)]),
  (399999995371, 2, [(2, 1), (3, 2), (5, 1), (4444444393, 1)]),
  (1571, 2, [(2, 1), (5, 1), (157, 1)]),
  (11779, 2, [(2, 1), (3, 1), (13, 1), (151, 1)]),
  (9093389, 2, [(2, 2), (193, 1), (11779, 1)]),
  (399999995333, 3, [(2, 2), (7, 1), (1571, 1), (9093389, 1)]),
  (36549707, 2, [(2, 1), (67, 1), (272759, 1)]),
  (219298243, 2, [(2, 1), (3, 1), (36549707, 1)]),
  (16666666469, 2, [(2, 2), (19, 1), (219298243, 1)]),
  (399999995257, 10, [(2, 3), (3, 1), (16666666469, 1)]),
  (11743, 3, [(2, 1), (3, 1), (19, 1)]),
  (70459, 3, [(2, 1), (3, 1), (11743, 1)]),
  (1550099, 2, [(2, 1), (11, 1), (70459, 1)]),
  (12400793, 3, [(2, 3), (1550099, 1)]),
  (24801587, 2, [(2, 1), (12400793, 1)])]

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

end LeanLab.DtRS1998.Task303.Low
