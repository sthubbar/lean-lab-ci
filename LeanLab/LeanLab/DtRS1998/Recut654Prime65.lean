/-
AI wrote this Lean code for CODEX task654.
P0037 Section 5.2 page 212 and Table 2 page 214, regenerated candidate 65.
One Pocklington style certificate uses the cube-root size criterion.
This is one candidate, not the full qs20 primality leaf. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Pock

namespace LeanLab.DtRS1998.Recut654Prime65

open LeanLab.DtRS1998 LeanLab.Verifications.Pratt

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- The Pocklington chains for the small factors used by candidate 65. -/
def factorChain65 : List Big.Cert := [(22129, 19, [(2, 4), (3, 1), (461, 1)]),
  (12043, 2, [(2, 1), (3, 3), (223, 1)]),
  (786648761, 3, [(2, 3), (5, 1), (23, 1), (71, 1), (12043, 1)]),
  (7411363969, 34, [(2, 7), (3, 1), (23, 1), (53, 1), (71, 1), (223, 1)]),
  (1110523, 2, [(2, 1), (3, 1), (7, 1), (137, 1), (193, 1)]),
  (59968243, 11, [(2, 1), (3, 3), (1110523, 1)]),
  (248508398993, 3, [(2, 4), (7, 1), (37, 1), (59968243, 1)]),
  (3374297, 3, [(2, 3), (17, 1), (43, 1), (577, 1)]),
  (26994377, 3, [(2, 3), (3374297, 1)]),
  (8098313101, 2, [(2, 2), (3, 1), (5, 2), (26994377, 1)]),
  (7175105407487, 5, [(2, 1), (443, 1), (8098313101, 1)]),
  (2239, 3, [(2, 1), (3, 1), (373, 1)]),
  (12301, 2, [(2, 2), (3, 1), (5, 2), (41, 1)]),
  (3391, 3, [(2, 1), (3, 1), (5, 1), (113, 1)]),
  (1546297, 5, [(2, 3), (3, 1), (19, 1), (3391, 1)]),
  (5791970400384089, 3, [(2, 3), (17, 1), (2239, 1), (12301, 1), (1546297, 1)])]

/-- The certified factored part of candidate 65 minus one. -/
def factors65 : List (ℕ × ℕ) := [(2, 2), (7, 1), (23, 1), (83, 1), (113, 1), (22129, 1), (786648761, 1), (7411363969, 1), (248508398993, 1), (7175105407487, 1), (5791970400384089, 1)]

/-- Every factor-chain entry is prime by its own Pocklington witness. -/
theorem factorChain65_prime : ∀ c ∈ factorChain65, c.1.Prime := by
  exact Big.chainP_sound factorChain65 [] (by simp) (by decide +kernel)

/-- LEAF: Regenerated member 65 of qs20 is prime, with a single large-number witness.
The remaining members of the fixed list are not asserted here. -/
theorem candidate65_prime : (10 ^ 200 - 2560643 : ℕ).Prime := by
  have hprimes : ∀ x ∈ factors65, x.1.Prime := by
    have hm : factors65.all (fun x =>
        (factorChain65.map Prod.fst).contains x.1 || LeanLab.primeB x.1) = true := by
      decide +kernel
    intro x hx
    have hy := List.all_eq_true.mp hm x hx
    simp only [Bool.or_eq_true] at hy
    rcases hy with h | h
    · obtain ⟨c, hc, heq⟩ := List.mem_map.mp (List.contains_iff_mem.mp h)
      rw [← heq]
      exact factorChain65_prime c hc
    · exact LeanLab.primeB_sound h
  apply Recut654Pock.prime_of_factor_divisibility
    (10 ^ 200 - 2560643) 8047831735108538864173857380804347006207050204710241089993265228531764 4217136821368875060473777674533181253820361397641979396172742947575730
    (by decide +kernel) (by decide +kernel)
  · exact Recut654Pock.factor_congruence (10 ^ 200 - 2560643) 2 665 factors65
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hprimes
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Prime65
