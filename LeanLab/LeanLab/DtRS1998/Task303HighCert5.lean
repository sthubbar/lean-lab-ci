/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert4

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K5 : List ℕ := [1283, 1291, 2129, 87481]

/-- Pocklington entries for chunk 5, page 210. -/
def S5 : List Big.Cert := [(263157894733, 2, [(2, 2), (3, 1), (87481, 1)]),
  (89999999998687, 3, [(2, 1), (3, 2), (19, 1), (263157894733, 1)]),
  (1237, 2, [(2, 2), (3, 1), (103, 1)]),
  (264705882349, 7, [(2, 2), (3, 1), (179, 1), (1237, 1)]),
  (89999999998661, 3, [(2, 2), (5, 1), (17, 1), (264705882349, 1)]),
  (10247, 5, [(2, 1), (47, 1), (109, 1)]),
  (89999999998633, 5, [(2, 3), (3, 2), (337, 1), (10247, 1)]),
  (1948558067, 2, [(2, 1), (7, 1), (13, 1), (257, 1)]),
  (14999999999767, 3, [(2, 1), (3, 1), (1283, 1), (1948558067, 1)]),
  (89999999998603, 2, [(2, 1), (3, 1), (14999999999767, 1)]),
  (6397, 2, [(2, 2), (3, 1), (13, 1)]),
  (89999999998537, 10, [(2, 3), (3, 1), (433, 1), (6397, 1)]),
  (1789, 6, [(2, 2), (3, 1), (149, 1)]),
  (89999999998481, 3, [(2, 4), (5, 1), (11, 3), (13, 1), (1789, 1)]),
  (641551, 7, [(2, 1), (3, 1), (5, 2), (7, 1)]),
  (89999999998429, 2, [(2, 2), (3, 1), (13, 1), (641551, 1)]),
  (7561, 13, [(2, 3), (3, 3)]),
  (13765677577, 5, [(2, 3), (3, 1), (7, 1), (7561, 1)]),
  (89999999998427, 2, [(2, 1), (7, 1), (467, 1), (13765677577, 1)]),
  (27173913043, 2, [(2, 1), (3, 1), (547, 1), (2129, 1)]),
  (89999999998417, 13, [(2, 4), (3, 2), (23, 1), (27173913043, 1)]),
  (18149, 2, [(2, 2), (13, 1), (349, 1)]),
  (36299, 2, [(2, 1), (18149, 1)]),
  (4646273, 3, [(2, 7), (36299, 1)]),
  (120803099, 2, [(2, 1), (13, 1), (4646273, 1)]),
  (89999999998387, 2, [(2, 1), (3, 1), (227, 1), (547, 1), (120803099, 1)]),
  (485417, 3, [(2, 3), (47, 1), (1291, 1)]),
  (92703799, 6, [(2, 1), (3, 3), (11, 1), (239, 1)]),
  (89999999998367, 5, [(2, 1), (485417, 1), (92703799, 1)]),
  (1117, 2, [(2, 2), (3, 2)])]

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

end LeanLab.DtRS1998.Task303.High
