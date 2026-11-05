/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303Middle2Cert1

namespace LeanLab.DtRS1998.Task303.Middle2

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K2 : List ℕ := [81853]

/-- Pocklington entries for chunk 2, page 210. -/
def S2 : List Big.Cert := [(5381, 3, [(2, 2), (5, 1), (269, 1)]),
  (15271279, 6, [(2, 1), (3, 1), (11, 1), (43, 1), (5381, 1)]),
  (59999999999377, 5, [(2, 4), (3, 1), (81853, 1), (15271279, 1)]),
  (8513, 3, [(2, 6), (7, 1)]),
  (17027, 2, [(2, 1), (8513, 1)]),
  (136217, 3, [(2, 3), (17027, 1)]),
  (59999999999353, 10, [(2, 3), (3, 1), (7, 1), (19, 1), (136217, 1)]),
  (17837, 2, [(2, 2), (7, 3)]),
  (2089, 7, [(2, 3), (3, 2)]),
  (1136417, 3, [(2, 5), (17, 1), (2089, 1)]),
  (84094859, 2, [(2, 1), (37, 1), (1136417, 1)]),
  (59999999999321, 3, [(2, 3), (5, 1), (17837, 1), (84094859, 1)]),
  (151901, 12, [(2, 2), (5, 2), (7, 2)]),
  (92461, 2, [(2, 2), (3, 1), (5, 1), (23, 1)]),
  (554767, 3, [(2, 1), (3, 1), (92461, 1)]),
  (98748527, 5, [(2, 1), (89, 1), (554767, 1)]),
  (59999999999309, 2, [(2, 2), (151901, 1), (98748527, 1)]),
  (2351, 13, [(2, 1), (5, 2)]),
  (852514919, 7, [(2, 1), (23, 1), (2351, 1)]),
  (1304347826071, 3, [(2, 1), (3, 2), (5, 1), (17, 1), (852514919, 1)]),
  (59999999999267, 2, [(2, 1), (23, 1), (1304347826071, 1)]),
  (59999999999249, 3, [(2, 4), (41, 1), (83, 1), (541, 1)]),
  (59999999999239, 15, [(2, 1), (3, 3), (13, 1), (19, 1), (137, 1), (179, 1)]),
  (59999999999221, 2, [(2, 2), (3, 2), (5, 1), (17, 1), (23, 1), (852514919, 1)]),
  (1973, 2, [(2, 2), (17, 1)]),
  (33112582781, 2, [(2, 2), (5, 1), (139, 1), (1973, 1)]),
  (9999999999863, 5, [(2, 1), (151, 1), (33112582781, 1)]),
  (59999999999179, 10, [(2, 1), (3, 1), (9999999999863, 1)]),
  (4093, 2, [(2, 2), (3, 1), (11, 1)]),
  (900461, 2, [(2, 2), (5, 1), (11, 1), (4093, 1)])]

/-- Kernel acceptance of chunk 2, page 210. -/
theorem chain2 : Big.chainP K2 S2 = true := by decide +kernel

/-- Each entry of chunk 2 is prime, page 210. -/
theorem primes2 : ∀ c ∈ S2, c.1.Prime := by
  apply Big.chainP_sound S2 K2 ?_ chain2
  intro p hp
  have hm : K2.all (fun p => (S0 ++ (S1)).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1
  · exact primes0 c h0
  · exact primes1 c h1

#print axioms chain2
#print axioms primes2

end LeanLab.DtRS1998.Task303.Middle2
