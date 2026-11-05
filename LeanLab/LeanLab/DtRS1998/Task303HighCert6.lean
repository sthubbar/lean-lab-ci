/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert5

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K6 : List ℕ := [1117]

/-- Pocklington entries for chunk 6, page 210. -/
def S6 : List Big.Cert := [(31277, 2, [(2, 2), (7, 1), (1117, 1)]),
  (89999999998357, 2, [(2, 2), (3, 1), (7, 2), (37, 1), (31277, 1)]),
  (4391, 14, [(2, 1), (5, 1), (439, 1)]),
  (1423, 3, [(2, 1), (3, 2), (79, 1)]),
  (8539, 2, [(2, 1), (3, 1), (1423, 1)]),
  (21620749, 6, [(2, 2), (3, 1), (211, 1), (8539, 1)]),
  (89999999998333, 5, [(2, 2), (3, 1), (79, 1), (4391, 1), (21620749, 1)]),
  (8863, 3, [(2, 1), (3, 1), (7, 1), (211, 1)]),
  (136363636361, 3, [(2, 3), (5, 1), (7, 1), (8863, 1)]),
  (14999999999711, 11, [(2, 1), (5, 1), (11, 1), (136363636361, 1)]),
  (89999999998267, 2, [(2, 1), (3, 1), (14999999999711, 1)]),
  (89999999998261, 6, [(2, 2), (3, 1), (5, 1), (11, 1), (136363636361, 1)]),
  (6337, 10, [(2, 6), (3, 2)]),
  (1013921, 3, [(2, 5), (5, 1), (6337, 1)]),
  (8261428309, 6, [(2, 2), (3, 1), (7, 1), (97, 1), (1013921, 1)]),
  (89999999998247, 5, [(2, 1), (13, 1), (419, 1), (8261428309, 1)]),
  (40231, 3, [(2, 1), (3, 3), (5, 1)]),
  (2689, 13, [(2, 7)]),
  (451753, 5, [(2, 3), (3, 1), (7, 1), (2689, 1)]),
  (1118540429, 2, [(2, 2), (619, 1), (451753, 1)]),
  (89999999998199, 7, [(2, 1), (40231, 1), (1118540429, 1)]),
  (90641, 3, [(2, 4), (5, 1), (11, 1)]),
  (919643587, 3, [(2, 1), (3, 1), (19, 1), (89, 1), (90641, 1)]),
  (89999999998169, 3, [(2, 3), (13, 1), (941, 1), (919643587, 1)]),
  (16069, 2, [(2, 2), (3, 1), (13, 1)]),
  (89999999998151, 11, [(2, 1), (5, 2), (11, 1), (17, 1), (16069, 1)]),
  (387781, 2, [(2, 2), (3, 1), (5, 1), (23, 1)]),
  (3041, 3, [(2, 5), (5, 1)]),
  (364921, 11, [(2, 3), (3, 1), (5, 1), (3041, 1)]),
  (38681627, 2, [(2, 1), (53, 1), (364921, 1)])]

/-- Kernel acceptance of chunk 6, page 210. -/
theorem chain6 : Big.chainP K6 S6 = true := by decide +kernel

/-- Each entry of chunk 6 is prime, page 210. -/
theorem primes6 : ∀ c ∈ S6, c.1.Prime := by
  apply Big.chainP_sound S6 K6 ?_ chain6
  intro p hp
  have hm : K6.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5)))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5
  · exact primes0 c h0
  · exact primes1 c h1
  · exact primes2 c h2
  · exact primes3 c h3
  · exact primes4 c h4
  · exact primes5 c h5

#print axioms chain6
#print axioms primes6

end LeanLab.DtRS1998.Task303.High
