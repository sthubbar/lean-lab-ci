/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle2Cert6

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K7 : List ℕ := [11939]

/-- Pocklington entries for chunk 7, page 210. -/
def S7 : List Big.Cert := [(3719, 7, [(2, 1), (11, 1), (13, 2)]),
  (66943, 3, [(2, 1), (3, 2), (3719, 1)]),
  (3079379, 2, [(2, 1), (23, 1), (66943, 1)]),
  (441176470573, 2, [(2, 2), (3, 1), (11939, 1), (3079379, 1)]),
  (59999999997929, 3, [(2, 3), (17, 1), (441176470573, 1)]),
  (42701, 3, [(2, 2), (5, 2), (7, 1)]),
  (234186553, 5, [(2, 3), (3, 4), (19, 1), (23, 1)]),
  (59999999997919, 3, [(2, 1), (3, 1), (42701, 1), (234186553, 1)]),
  (1701397, 2, [(2, 2), (3, 2), (167, 1)]),
  (59999999997787, 3, [(2, 1), (3, 1), (1701397, 1)]),
  (3253, 2, [(2, 2), (3, 1), (271, 1)]),
  (32531, 2, [(2, 1), (5, 1), (3253, 1)]),
  (65063, 5, [(2, 1), (32531, 1)]),
  (130127, 5, [(2, 1), (65063, 1)]),
  (230544007, 3, [(2, 1), (3, 1), (7, 1), (11, 1), (569, 1)]),
  (59999999997779, 2, [(2, 1), (130127, 1), (230544007, 1)]),
  (1747, 2, [(2, 1), (3, 2), (97, 1)]),
  (17471, 11, [(2, 1), (5, 1), (1747, 1)]),
  (59999999997733, 2, [(2, 2), (3, 1), (233, 1), (17471, 1)]),
  (177113, 5, [(2, 3), (13, 2)]),
  (42345847, 3, [(2, 1), (3, 2), (109, 1), (113, 1)]),
  (59999999997689, 3, [(2, 3), (177113, 1), (42345847, 1)]),
  (4045307443, 3, [(2, 1), (3, 1), (11, 1), (19, 1), (229, 1)]),
  (24271844659, 2, [(2, 1), (3, 1), (4045307443, 1)]),
  (97087378637, 2, [(2, 2), (24271844659, 1)]),
  (59999999997667, 2, [(2, 1), (3, 1), (103, 1), (97087378637, 1)]),
  (2633, 3, [(2, 3), (7, 1)]),
  (59999999997653, 3, [(2, 2), (11, 1), (13, 1), (31, 1), (2633, 1)]),
  (2383, 5, [(2, 1), (3, 1), (397, 1)]),
  (28597, 2, [(2, 2), (3, 1), (2383, 1)])]

/-- Kernel acceptance of chunk 7, page 210. -/
theorem chain7 : Big.chainP K7 S7 = true := by decide +kernel

/-- Each entry of chunk 7 is prime, page 210. -/
theorem primes7 : ∀ c ∈ S7, c.1.Prime := by
  apply Big.chainP_sound S7 K7 ?_ chain7
  intro p hp
  have hm : K7.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2
  · exact primes3 c h3
  · exact primes4 c h4
  · exact primes5 c h5
  · exact primes6 c h6

#print axioms chain7
#print axioms primes7

end LeanLab.DtRS1998.Task303.Middle2
