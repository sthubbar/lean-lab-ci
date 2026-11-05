/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert13

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K14 : List ℕ := [51907]

/-- Pocklington entries for chunk 14, page 210. -/
def S14 : List Big.Cert := [(207629, 2, [(2, 2), (51907, 1)]),
  (3737323, 2, [(2, 1), (3, 2), (207629, 1)]),
  (18028846153, 5, [(2, 3), (3, 2), (67, 1), (3737323, 1)]),
  (89999999995777, 5, [(2, 7), (3, 1), (13, 1), (18028846153, 1)]),
  (4421, 3, [(2, 2), (5, 1), (13, 1)]),
  (3923, 2, [(2, 1), (37, 1)]),
  (94153, 5, [(2, 3), (3, 1), (3923, 1)]),
  (130496059, 2, [(2, 1), (3, 2), (7, 1), (11, 1), (94153, 1)]),
  (10178692603, 7, [(2, 1), (3, 1), (13, 1), (130496059, 1)]),
  (89999999995727, 5, [(2, 1), (4421, 1), (10178692603, 1)]),
  (3447483337, 5, [(2, 3), (3, 3), (11, 1), (103, 1)]),
  (89999999995723, 2, [(2, 1), (3, 1), (19, 1), (229, 1), (3447483337, 1)]),
  (18371, 11, [(2, 1), (5, 1), (11, 1), (167, 1)]),
  (89999999995699, 10, [(2, 1), (3, 4), (13, 1), (53, 1), (18371, 1)]),
  (1721, 3, [(2, 3), (5, 1), (43, 1)]),
  (1363636363571, 2, [(2, 1), (5, 1), (13, 1), (457, 1), (1721, 1)]),
  (89999999995687, 6, [(2, 1), (3, 1), (11, 1), (1363636363571, 1)]),
  (1361, 3, [(2, 4), (5, 1)]),
  (89999999995649, 3, [(2, 8), (29, 1), (1361, 1)]),
  (1033, 5, [(2, 3), (3, 1), (43, 1)]),
  (4133, 2, [(2, 2), (1033, 1)]),
  (5701, 2, [(2, 2), (3, 1), (5, 2)]),
  (159629, 3, [(2, 2), (7, 1), (5701, 1)]),
  (2638986629, 2, [(2, 2), (4133, 1), (159629, 1)]),
  (459183673447, 3, [(2, 1), (3, 1), (29, 1), (2638986629, 1)]),
  (89999999995613, 2, [(2, 2), (7, 2), (459183673447, 1)]),
  (9311, 7, [(2, 1), (5, 1), (7, 2)]),
  (9329623, 5, [(2, 1), (3, 1), (167, 1), (9311, 1)]),
  (205251707, 2, [(2, 1), (11, 1), (9329623, 1)]),
  (89999999995603, 5, [(2, 1), (3, 1), (107, 1), (683, 1), (205251707, 1)])]

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

end LeanLab.DtRS1998.Task303.High
