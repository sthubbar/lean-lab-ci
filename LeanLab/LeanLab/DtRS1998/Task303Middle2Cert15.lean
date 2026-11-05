/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle2Cert14

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K15 : List ℕ := [1217]

/-- Pocklington entries for chunk 15, page 210. -/
def S15 : List Big.Cert := [(59999999995643, 2, [(2, 1), (7, 1), (97, 1), (547, 1), (941, 1)]),
  (4448359, 3, [(2, 1), (3, 9)]),
  (111111111103, 3, [(2, 1), (3, 1), (23, 1), (181, 1), (4448359, 1)]),
  (5999999999563, 2, [(2, 1), (3, 3), (111111111103, 1)]),
  (59999999995631, 13, [(2, 1), (5, 1), (5999999999563, 1)]),
  (7521421, 10, [(2, 2), (3, 1), (5, 1), (67, 1)]),
  (1173341677, 2, [(2, 2), (3, 1), (13, 1), (7521421, 1)]),
  (110294117639, 23, [(2, 1), (47, 1), (1173341677, 1)]),
  (29999999997809, 3, [(2, 4), (17, 1), (110294117639, 1)]),
  (59999999995619, 2, [(2, 1), (29999999997809, 1)]),
  (2339, 2, [(2, 1), (7, 1), (167, 1)]),
  (18713, 3, [(2, 3), (2339, 1)]),
  (254237288117, 2, [(2, 2), (7, 2), (18713, 1)]),
  (59999999995613, 2, [(2, 2), (59, 1), (254237288117, 1)]),
  (37870181, 3, [(2, 2), (5, 1), (433, 1)]),
  (2272210861, 2, [(2, 2), (3, 1), (5, 1), (37870181, 1)]),
  (59999999995567, 5, [(2, 1), (3, 4), (163, 1), (2272210861, 1)]),
  (153343, 5, [(2, 1), (3, 2), (7, 1), (1217, 1)]),
  (2964426877, 5, [(2, 2), (3, 3), (179, 1), (153343, 1)]),
  (11857707509, 2, [(2, 2), (2964426877, 1)]),
  (59999999995541, 2, [(2, 2), (5, 1), (11, 1), (23, 1), (11857707509, 1)]),
  (9923, 2, [(2, 1), (11, 2)]),
  (59999999995501, 6, [(2, 2), (3, 1), (5, 3), (37, 1), (9923, 1)]),
  (2801, 3, [(2, 4), (5, 2)]),
  (33056977, 5, [(2, 4), (3, 1), (17, 2)]),
  (10710460549, 2, [(2, 2), (3, 4), (33056977, 1)]),
  (59999999995499, 2, [(2, 1), (2801, 1), (10710460549, 1)]),
  (1093, 5, [(2, 2), (3, 1), (7, 1)]),
  (50940359, 13, [(2, 1), (7, 1), (1093, 1)]),
  (2139495079, 3, [(2, 1), (3, 1), (7, 1), (50940359, 1)])]

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

end LeanLab.DtRS1998.Task303.Middle2
