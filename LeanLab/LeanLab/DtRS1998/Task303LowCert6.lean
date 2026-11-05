/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowCert5

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K6 : List ℕ := [1427]

/-- Pocklington entries for chunk 6, page 210. -/
def S6 : List Big.Cert := [(140154169, 29, [(2, 3), (3, 1), (7, 1), (11, 1), (149, 1)]),
  (399999998327, 5, [(2, 1), (1427, 1), (140154169, 1)]),
  (2909, 2, [(2, 2), (727, 1)]),
  (321543407, 5, [(2, 1), (17, 1), (2909, 1)]),
  (399999998309, 2, [(2, 2), (311, 1), (321543407, 1)]),
  (399999998269, 6, [(2, 2), (3, 2), (13, 1), (37, 1), (197, 1)]),
  (66666666371, 2, [(2, 1), (5, 1), (17, 1), (43, 1), (47, 1)]),
  (399999998227, 2, [(2, 1), (3, 1), (66666666371, 1)]),
  (30553, 5, [(2, 3), (3, 1), (19, 1)]),
  (3273001, 22, [(2, 3), (3, 1), (5, 3)]),
  (399999998213, 2, [(2, 2), (30553, 1), (3273001, 1)]),
  (399999998191, 33, [(2, 1), (3, 1), (5, 1), (13, 1), (73, 1), (167, 1)]),
  (1021, 10, [(2, 2), (3, 1), (5, 1)]),
  (16657, 5, [(2, 4), (3, 1), (347, 1)]),
  (3264773, 2, [(2, 2), (7, 2), (16657, 1)]),
  (39177277, 5, [(2, 2), (3, 1), (3264773, 1)]),
  (399999998171, 2, [(2, 1), (5, 1), (1021, 1), (39177277, 1)]),
  (1231, 3, [(2, 1), (3, 1), (5, 1), (41, 1)]),
  (36931, 2, [(2, 1), (3, 1), (5, 1), (1231, 1)]),
  (221587, 3, [(2, 1), (3, 1), (36931, 1)]),
  (43431053, 3, [(2, 2), (7, 2), (221587, 1)]),
  (399999998131, 2, [(2, 1), (3, 1), (5, 1), (307, 1), (43431053, 1)]),
  (77201, 3, [(2, 4), (5, 2)]),
  (471698111, 11, [(2, 1), (5, 1), (13, 1), (47, 1), (77201, 1)]),
  (399999998129, 3, [(2, 4), (53, 1), (471698111, 1)]),
  (2083, 2, [(2, 1), (3, 1), (347, 1)]),
  (399999998093, 2, [(2, 2), (139, 1), (2083, 1)]),
  (2411, 6, [(2, 1), (5, 1), (241, 1)]),
  (28933, 2, [(2, 2), (3, 1), (2411, 1)]),
  (384029, 2, [(2, 2), (19, 1), (31, 1)])]

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

end LeanLab.DtRS1998.Task303.Low
