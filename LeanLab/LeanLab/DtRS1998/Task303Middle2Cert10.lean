/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle2Cert9

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K10 : List ℕ := [4133]

/-- Pocklington entries for chunk 10, page 210. -/
def S10 : List Big.Cert := [(5701, 2, [(2, 2), (3, 1), (5, 2)]),
  (159629, 3, [(2, 2), (7, 1), (5701, 1)]),
  (2638986629, 2, [(2, 2), (4133, 1), (159629, 1)]),
  (2142857142749, 2, [(2, 2), (7, 1), (29, 1), (2638986629, 1)]),
  (4285714285499, 2, [(2, 1), (2142857142749, 1)]),
  (59999999996987, 2, [(2, 1), (7, 1), (4285714285499, 1)]),
  (44483, 2, [(2, 1), (23, 1), (967, 1)]),
  (1067593, 5, [(2, 3), (3, 1), (44483, 1)]),
  (6405559, 6, [(2, 1), (3, 1), (1067593, 1)]),
  (9999999999497, 3, [(2, 3), (13, 1), (17, 1), (883, 1), (6405559, 1)]),
  (59999999996983, 5, [(2, 1), (3, 1), (9999999999497, 1)]),
  (432451133, 2, [(2, 2), (29, 1), (281, 1)]),
  (14999999999239, 6, [(2, 1), (3, 2), (41, 1), (47, 1), (432451133, 1)]),
  (59999999996957, 2, [(2, 2), (14999999999239, 1)]),
  (28813, 2, [(2, 2), (3, 1), (7, 4)]),
  (59999999996933, 2, [(2, 2), (71, 1), (157, 1), (28813, 1)]),
  (51907, 11, [(2, 1), (3, 1), (41, 1)]),
  (207629, 2, [(2, 2), (51907, 1)]),
  (3737323, 2, [(2, 1), (3, 2), (207629, 1)]),
  (19531249999, 6, [(2, 1), (3, 1), (13, 1), (67, 1), (3737323, 1)]),
  (59999999996929, 13, [(2, 10), (3, 1), (19531249999, 1)]),
  (1087, 3, [(2, 1), (3, 1), (181, 1)]),
  (4349, 2, [(2, 2), (1087, 1)]),
  (8699, 2, [(2, 1), (4349, 1)]),
  (2141, 2, [(2, 2), (5, 1), (107, 1)]),
  (4283, 2, [(2, 1), (2141, 1)]),
  (5225261, 2, [(2, 2), (5, 1), (61, 1), (4283, 1)]),
  (3448672261, 2, [(2, 2), (3, 1), (5, 1), (11, 1), (5225261, 1)]),
  (59999999996879, 13, [(2, 1), (8699, 1), (3448672261, 1)]),
  (282847, 5, [(2, 1), (3, 1), (17, 1), (47, 1)])]

/-- Kernel acceptance of chunk 10, page 210. -/
theorem chain10 : Big.chainP K10 S10 = true := by decide +kernel

/-- Each entry of chunk 10 is prime, page 210. -/
theorem primes10 : ∀ c ∈ S10, c.1.Prime := by
  apply Big.chainP_sound S10 K10 ?_ chain10
  intro p hp
  have hm : K10.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9)))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
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

#print axioms chain10
#print axioms primes10

end LeanLab.DtRS1998.Task303.Middle2
