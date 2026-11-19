/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3000000 through 3009999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3000000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8684288, 8643840, 8524160, 8507520, 7375104, 6917888, 4372992, 6093824, 2635008, 3850112, 8520320, 2568192, 3245184, 2400512, 6394368, 2849792, 6400128, 2553344, 2667648, 4762880, 3323904, 3650432, 3336960, 3002240, 7028352, 6821888, 3917184, 2614400, 3453312, 6639872, 2236928, 2991360, 2203520, 2904192, 6958464, 2197760, 1862400, 7152128, 5524352, 3648128, 3593088, 3974912, 2387712, 2275712, 3097728, 2007680, 1928064, 3491072, 2475264, 5307264, 2640128, 2280192, 2161920, 380928, 0]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8778075, 8779515]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (5, 2, [(2, 2)]),
  (17, 3, [(2, 4)]),
  (16661, 10, [(2, 2), (5, 1), (7, 2), (17, 1)]),
  (2099287, 7, [(2, 1), (3, 2), (7, 1), (16661, 1)]),
  (8397149, 2, [(2, 2), (2099287, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (13, 2, [(2, 2), (3, 1)]),
  (53, 2, [(2, 2), (13, 1)]),
  (52259, 2, [(2, 1), (17, 1), (29, 1), (53, 1)]),
  (2194879, 6, [(2, 1), (3, 1), (7, 1), (52259, 1)]),
  (8779517, 2, [(2, 2), (2194879, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(8778075, 380928), (8779515, 0)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8764931 + 2 * t ∧ (8764931 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8764931) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3000000
