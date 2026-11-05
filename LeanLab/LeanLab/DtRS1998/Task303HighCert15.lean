/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert14

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K15 : List ℕ := [2638986629]

/-- Pocklington entries for chunk 15, page 210. -/
def S15 : List Big.Cert := [(17539, 2, [(2, 1), (3, 1), (37, 1)]),
  (175391, 13, [(2, 1), (5, 1), (17539, 1)]),
  (35078201, 3, [(2, 3), (5, 2), (175391, 1)]),
  (33885542167, 3, [(2, 1), (3, 1), (7, 1), (23, 1), (35078201, 1)]),
  (89999999995553, 3, [(2, 5), (83, 1), (33885542167, 1)]),
  (432451133, 2, [(2, 2), (29, 1), (281, 1)]),
  (957446808463, 6, [(2, 1), (3, 3), (41, 1), (432451133, 1)]),
  (89999999995523, 2, [(2, 1), (47, 1), (957446808463, 1)]),
  (89999999995501, 2, [(2, 2), (3, 2), (5, 3), (7, 1), (97, 1), (193, 1)]),
  (2142857142749, 2, [(2, 2), (7, 1), (29, 1), (2638986629, 1)]),
  (89999999995459, 3, [(2, 1), (3, 1), (7, 1), (2142857142749, 1)]),
  (2753, 3, [(2, 6)]),
  (89999999995457, 3, [(2, 6), (19, 1), (179, 1), (2753, 1)]),
  (1259, 2, [(2, 1), (17, 1), (37, 1)]),
  (1344113, 3, [(2, 4), (7, 1), (11, 1)]),
  (27075812273, 3, [(2, 4), (1259, 1), (1344113, 1)]),
  (89999999995453, 2, [(2, 2), (3, 1), (277, 1), (27075812273, 1)]),
  (93139, 2, [(2, 1), (3, 1), (19, 2)]),
  (13412017, 5, [(2, 4), (3, 2), (93139, 1)]),
  (80472103, 19, [(2, 1), (3, 1), (13412017, 1)]),
  (374999999981, 2, [(2, 2), (5, 1), (233, 1), (80472103, 1)]),
  (89999999995441, 17, [(2, 4), (3, 1), (5, 1), (374999999981, 1)]),
  (89999999995429, 6, [(2, 2), (3, 3), (41, 1), (47, 1), (432451133, 1)]),
  (1409, 3, [(2, 7)]),
  (2819, 2, [(2, 1), (1409, 1)]),
  (5639, 7, [(2, 1), (2819, 1)]),
  (11279, 7, [(2, 1), (5639, 1)]),
  (40909090907, 2, [(2, 1), (157, 1), (11279, 1)]),
  (4499999999771, 2, [(2, 1), (5, 1), (11, 1), (40909090907, 1)]),
  (89999999995421, 2, [(2, 2), (5, 1), (4499999999771, 1)])]

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

end LeanLab.DtRS1998.Task303.High
