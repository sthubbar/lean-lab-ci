/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle2Cert4

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K5 : List ℕ := [1697, 1847]

/-- Pocklington entries for chunk 5, page 210. -/
def S5 : List Big.Cert := [(59999999998531, 2, [(2, 1), (3, 1), (5, 1), (23, 1), (1697, 1), (1847, 1)]),
  (3209, 3, [(2, 3), (401, 1)]),
  (1699, 3, [(2, 1), (3, 1), (283, 1)]),
  (246018599, 7, [(2, 1), (7, 1), (1699, 1)]),
  (59999999998517, 2, [(2, 2), (19, 1), (3209, 1), (246018599, 1)]),
  (43457, 3, [(2, 6), (7, 1)]),
  (76223579, 2, [(2, 1), (877, 1), (43457, 1)]),
  (59999999998483, 14, [(2, 1), (3, 4), (43, 1), (113, 1), (76223579, 1)]),
  (59999999998453, 2, [(2, 2), (3, 1), (29, 1), (149, 1), (919, 1)]),
  (8467, 2, [(2, 1), (3, 1), (17, 1)]),
  (13039181, 2, [(2, 2), (5, 1), (7, 1), (11, 1), (8467, 1)]),
  (59999999998397, 2, [(2, 2), (31, 1), (43, 1), (863, 1), (13039181, 1)]),
  (3889, 11, [(2, 4), (3, 5)]),
  (70003, 2, [(2, 1), (3, 2), (3889, 1)]),
  (59999999998373, 2, [(2, 2), (7, 1), (167, 1), (70003, 1)]),
  (1423, 3, [(2, 1), (3, 2), (79, 1)]),
  (59999999998361, 3, [(2, 3), (5, 1), (389, 1), (1423, 1)]),
  (30773, 3, [(2, 2), (7, 2)]),
  (430823, 5, [(2, 1), (7, 1), (30773, 1)]),
  (861647, 5, [(2, 1), (430823, 1)]),
  (15509647, 17, [(2, 1), (3, 2), (861647, 1)]),
  (59999999998321, 13, [(2, 4), (3, 5), (5, 1), (199, 1), (15509647, 1)]),
  (10657, 7, [(2, 5), (3, 2)]),
  (181818181813, 2, [(2, 2), (3, 1), (131, 1), (10657, 1)]),
  (59999999998291, 10, [(2, 1), (3, 1), (5, 1), (11, 1), (181818181813, 1)]),
  (29999999999129, 3, [(2, 3), (79, 1), (113, 1), (307, 1)]),
  (59999999998259, 2, [(2, 1), (29999999999129, 1)]),
  (3733, 2, [(2, 2), (3, 1), (311, 1)]),
  (245901639337, 5, [(2, 3), (3, 1), (19, 2), (3733, 1)]),
  (59999999998229, 2, [(2, 2), (61, 1), (245901639337, 1)])]

/-- Kernel acceptance of chunk 5, page 210. -/
theorem chain5 : Big.chainP K5 S5 = true := by decide +kernel

/-- Each entry of chunk 5 is prime, page 210. -/
theorem primes5 : ∀ c ∈ S5, c.1.Prime := by
  apply Big.chainP_sound S5 K5 ?_ chain5
  intro p hp
  have hm : K5.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2
  · exact primes3 c h3
  · exact primes4 c h4

#print axioms chain5
#print axioms primes5

end LeanLab.DtRS1998.Task303.Middle2
