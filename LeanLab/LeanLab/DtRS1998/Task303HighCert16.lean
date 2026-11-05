/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303HighCert15

namespace LeanLab.DtRS1998.Task303.High

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Earlier certified dependencies, page 210. -/
def K16 : List ℕ := [1583, 1721, 2638986629]

/-- Pocklington entries for chunk 16, page 210. -/
def S16 : List Big.Cert := [(89999999995417, 11, [(2, 3), (3, 1), (7, 2), (29, 1), (2638986629, 1)]),
  (1788553259, 2, [(2, 1), (19, 1), (59, 1), (463, 1)]),
  (35771065181, 2, [(2, 2), (5, 1), (1788553259, 1)]),
  (89999999995397, 2, [(2, 2), (17, 1), (37, 1), (35771065181, 1)]),
  (1193, 3, [(2, 3), (149, 1)]),
  (7159, 3, [(2, 1), (3, 1), (1193, 1)]),
  (20609161, 17, [(2, 3), (3, 1), (5, 1), (11, 1), (13, 1)]),
  (89999999995391, 13, [(2, 1), (5, 1), (61, 1), (7159, 1), (20609161, 1)]),
  (2741, 2, [(2, 2), (5, 1), (137, 1)]),
  (89999999995369, 11, [(2, 3), (3, 1), (109, 1), (131, 1), (2741, 1)]),
  (27271, 6, [(2, 1), (3, 3), (5, 1)]),
  (15544471, 3, [(2, 1), (3, 1), (5, 1), (19, 1), (27271, 1)]),
  (4352451881, 3, [(2, 3), (5, 1), (7, 1), (15544471, 1)]),
  (89999999995319, 7, [(2, 1), (7, 2), (211, 1), (4352451881, 1)]),
  (132763, 11, [(2, 1), (3, 1), (7, 1), (29, 1)]),
  (89999999995309, 2, [(2, 2), (3, 1), (13, 1), (132763, 1)]),
  (2003, 5, [(2, 1), (7, 1), (11, 1)]),
  (89999999995289, 3, [(2, 3), (23, 1), (263, 1), (2003, 1)]),
  (26449, 7, [(2, 4), (3, 1), (19, 1)]),
  (89999999995249, 13, [(2, 4), (3, 2), (7, 1), (37, 1), (26449, 1)]),
  (15901, 10, [(2, 2), (3, 1), (5, 2)]),
  (23008217, 3, [(2, 3), (7, 1), (11, 1), (41, 1)]),
  (89999999995183, 3, [(2, 1), (3, 1), (41, 1), (15901, 1), (23008217, 1)]),
  (3719, 7, [(2, 1), (11, 1), (13, 2)]),
  (602351, 7, [(2, 1), (5, 2), (7, 1), (1721, 1)]),
  (40322580643, 5, [(2, 1), (3, 2), (3719, 1), (602351, 1)]),
  (89999999995177, 5, [(2, 3), (3, 2), (31, 1), (40322580643, 1)]),
  (126641, 3, [(2, 4), (5, 1), (1583, 1)]),
  (89999999995121, 3, [(2, 4), (5, 1), (126641, 1)]),
  (44999999997503, 5, [(2, 1), (11, 1), (239, 1), (353, 1), (727, 1)])]

/-- Kernel acceptance of chunk 16, page 210. -/
theorem chain16 : Big.chainP K16 S16 = true := by decide +kernel

/-- Each entry of chunk 16 is prime, page 210. -/
theorem primes16 : ∀ c ∈ S16, c.1.Prime := by
  apply Big.chainP_sound S16 K16 ?_ chain16
  intro p hp
  have hm : K16.all (fun p => (S0 ++ (S1 ++ (S2 ++ (S3 ++ (S4 ++ (S5 ++ (S6 ++ (S7 ++ (S8 ++ (S9 ++ (S10 ++ (S11 ++ (S12 ++ (S13 ++ (S14 ++ (S15)))))))))))))))).any (fun c => c.1 == p)) = true := by decide +kernel
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hm p hp)
  have heq : c.1 = p := by simpa using he
  rw [← heq]
  simp only [List.mem_append] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
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

#print axioms chain16
#print axioms primes16

end LeanLab.DtRS1998.Task303.High
