/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert6

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K7 : List ℕ := [28933, 384029]

/-- Pocklington entries for chunk 7, page 210. -/
def S7 : List Big.Cert := [(66666666343, 3, [(2, 1), (3, 1), (28933, 1), (384029, 1)]),
  (399999998059, 2, [(2, 1), (3, 1), (66666666343, 1)]),
  (11057, 3, [(2, 4), (691, 1)]),
  (154799, 7, [(2, 1), (7, 1), (11057, 1)]),
  (324149107, 2, [(2, 1), (3, 1), (349, 1), (154799, 1)]),
  (399999998039, 11, [(2, 1), (617, 1), (324149107, 1)]),
  (1879, 6, [(2, 1), (3, 1), (313, 1)]),
  (3499, 2, [(2, 1), (3, 1), (11, 1)]),
  (7095973, 2, [(2, 2), (3, 1), (13, 2), (3499, 1)]),
  (399999998011, 2, [(2, 1), (3, 1), (5, 1), (1879, 1), (7095973, 1)]),
  (2029, 2, [(2, 2), (3, 1), (13, 2)]),
  (399999997993, 5, [(2, 3), (3, 1), (7, 1), (41, 1), (2029, 1)]),
  (399999997979, 2, [(2, 1), (7, 1), (103, 1), (229, 1), (277, 1)]),
  (2970091, 2, [(2, 1), (3, 2), (5, 1), (61, 1)]),
  (17820547, 2, [(2, 1), (3, 1), (2970091, 1)]),
  (399999997963, 5, [(2, 1), (3, 2), (29, 1), (43, 1), (17820547, 1)]),
  (399999997937, 3, [(2, 4), (7, 3), (11, 1), (761, 1)]),
  (833333329, 7, [(2, 4), (3, 2), (29, 1), (431, 1)]),
  (399999997921, 14, [(2, 5), (3, 1), (5, 1), (833333329, 1)]),
  (399999997849, 17, [(2, 3), (3, 1), (11, 1), (79, 1), (331, 1)]),
  (3539, 2, [(2, 1), (29, 1), (61, 1)]),
  (1187, 2, [(2, 1), (593, 1)]),
  (819031, 3, [(2, 1), (3, 1), (5, 1), (23, 1), (1187, 1)]),
  (399999997843, 2, [(2, 1), (3, 1), (23, 1), (3539, 1), (819031, 1)]),
  (1116439, 6, [(2, 1), (3, 1), (37, 1), (47, 1)]),
  (399999997799, 23, [(2, 1), (359, 1), (499, 1), (1116439, 1)]),
  (1109, 2, [(2, 2), (277, 1)]),
  (82067, 2, [(2, 1), (37, 1), (1109, 1)]),
  (2133743, 5, [(2, 1), (13, 1), (82067, 1)]),
  (399999997753, 5, [(2, 3), (3, 1), (73, 1), (107, 1), (2133743, 1)])]

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

end LeanLab.DtRS1998.Task303.Low
