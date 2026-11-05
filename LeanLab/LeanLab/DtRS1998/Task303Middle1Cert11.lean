/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle1Cert10

namespace LeanLab.DtRS1998.Task303.Middle1

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K11 : List ℕ := [1487, 1999999999729]

/-- Pocklington entries for chunk 11, page 210. -/
def S11 : List Big.Cert := [(19999999997291, 2, [(2, 1), (5, 1), (1999999999729, 1)]),
  (19999999997209, 13, [(2, 3), (3, 2), (7, 1), (11, 1), (293, 1), (443, 1)]),
  (5235602093, 2, [(2, 2), (7, 1), (41, 1), (1487, 1)]),
  (10471204187, 2, [(2, 1), (5235602093, 1)]),
  (19999999997171, 2, [(2, 1), (5, 1), (191, 1), (10471204187, 1)]),
  (10061, 3, [(2, 2), (5, 1), (503, 1)]),
  (41048881, 21, [(2, 4), (3, 1), (5, 1), (17, 1), (10061, 1)]),
  (24875621887, 5, [(2, 1), (3, 1), (101, 1), (41048881, 1)]),
  (19999999997149, 6, [(2, 2), (3, 1), (67, 1), (24875621887, 1)]),
  (1453, 2, [(2, 2), (3, 1), (11, 2)]),
  (19999999997137, 10, [(2, 4), (3, 2), (53, 1), (1453, 1)]),
  (1283, 2, [(2, 1), (641, 1)]),
  (458484251, 2, [(2, 1), (5, 3), (7, 1), (19, 1)]),
  (19999999997123, 2, [(2, 1), (17, 1), (1283, 1), (458484251, 1)]),
  (3727, 3, [(2, 1), (3, 4)]),
  (3592829, 2, [(2, 2), (241, 1), (3727, 1)]),
  (16103059579, 2, [(2, 1), (3, 3), (83, 1), (3592829, 1)]),
  (19999999997119, 6, [(2, 1), (3, 3), (23, 1), (16103059579, 1)]),
  (2381, 3, [(2, 2), (5, 1), (7, 1)]),
  (28573, 2, [(2, 2), (3, 1), (2381, 1)]),
  (347161951, 6, [(2, 1), (3, 5), (5, 2), (28573, 1)]),
  (19999999997111, 17, [(2, 1), (5, 1), (7, 1), (823, 1), (347161951, 1)]),
  (30509, 2, [(2, 2), (29, 1), (263, 1)]),
  (11410367, 5, [(2, 1), (11, 1), (17, 1), (30509, 1)]),
  (8375209379, 2, [(2, 1), (367, 1), (11410367, 1)]),
  (19999999997053, 2, [(2, 2), (3, 1), (199, 1), (8375209379, 1)]),
  (2383, 5, [(2, 1), (3, 1), (397, 1)]),
  (3869993, 3, [(2, 3), (7, 1), (29, 1), (2383, 1)]),
  (1563477173, 2, [(2, 2), (101, 1), (3869993, 1)]),
  (19999999997017, 5, [(2, 3), (3, 1), (13, 1), (41, 1), (1563477173, 1)])]

/-- Kernel acceptance of chunk 11, page 210. -/
theorem chain11 : Big.chainP K11 S11 = true := by decide +kernel

/-- Each entry of chunk 11 is prime, page 210. -/
theorem primes11 : ∀ c ∈ S11, c.1.Prime := by
  apply Big.chainP_sound S11 K11 ?_ chain11
  intro p hp
  have hm : K11.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
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

#print axioms chain11
#print axioms primes11

end LeanLab.DtRS1998.Task303.Middle1
