/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle1Cert16

namespace LeanLab.DtRS1998.Task303.Middle1

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K17 : List ℕ := [217391304293]

/-- Pocklington entries for chunk 17, page 210. -/
def S17 : List Big.Cert := [(19999999994957, 2, [(2, 2), (23, 1), (217391304293, 1)]),
  (6121, 7, [(2, 3), (3, 2), (5, 1)]),
  (61211, 2, [(2, 1), (5, 1), (6121, 1)]),
  (1637, 2, [(2, 2), (409, 1)]),
  (16633, 5, [(2, 3), (3, 3)]),
  (54456443, 2, [(2, 1), (1637, 1), (16633, 1)]),
  (19999999994839, 3, [(2, 1), (3, 1), (61211, 1), (54456443, 1)]),
  (25013, 2, [(2, 2), (13, 2)]),
  (19999999994809, 22, [(2, 3), (3, 1), (461, 1), (25013, 1)]),
  (1747, 2, [(2, 1), (3, 2), (97, 1)]),
  (5823091, 3, [(2, 1), (3, 4), (5, 1), (7, 1)]),
  (19999999994783, 5, [(2, 1), (983, 1), (1747, 1), (5823091, 1)]),
  (1319, 13, [(2, 1), (659, 1)]),
  (19999999994131, 11, [(2, 1), (3, 2), (5, 1), (13, 1), (17, 1), (211, 1), (1319, 1)]),
  (3307, 2, [(2, 1), (3, 1), (19, 1)]),
  (19999999994081, 3, [(2, 5), (5, 1), (131, 1), (3307, 1)]),
  (4409, 3, [(2, 3), (19, 1)]),
  (8819, 2, [(2, 1), (4409, 1)]),
  (705521, 3, [(2, 4), (5, 1), (8819, 1)]),
  (5644169, 3, [(2, 3), (705521, 1)]),
  (959508731, 2, [(2, 1), (5, 1), (17, 1), (5644169, 1)]),
  (5757052387, 3, [(2, 1), (3, 1), (959508731, 1)]),
  (19999999992439, 3, [(2, 1), (3, 2), (193, 1), (5757052387, 1)])]

/-- Kernel acceptance of chunk 17, page 210. -/
theorem chain17 : Big.chainP K17 S17 = true := by decide +kernel

/-- Each entry of chunk 17 is prime, page 210. -/
theorem primes17 : ∀ c ∈ S17, c.1.Prime := by
  apply Big.chainP_sound S17 K17 ?_ chain17
  intro p hp
  have hm : K17.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10 ++ (S11 ++ (S12 ++ (S13 ++ (S14 ++ (S15 ++ (S16))))))))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16
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
  · exact primes16 c h16

#print axioms chain17
#print axioms primes17

end LeanLab.DtRS1998.Task303.Middle1
