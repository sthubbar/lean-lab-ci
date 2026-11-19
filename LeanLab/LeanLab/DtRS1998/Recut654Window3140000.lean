/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3140000 through 3149999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3140000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8684288, 8643840, 8524160, 5307264, 6400128, 6093824, 8507520, 2275712, 7028352, 6821888, 4762880, 3323904, 3650432, 4372992, 2667648, 8520320, 3850112, 6394368, 3917184, 6917888, 3336960, 2553344, 5220608, 3453312, 6285440, 2475264, 2070272, 2991360, 2537600, 2387712, 7375104, 2849792, 2912640, 7152128, 2268800, 3251712, 2568192, 2591360, 3245184, 2197760, 3097728, 2400512, 3002240, 2280192, 6639872, 2784000, 2640128, 2239872, 2161920, 6958464, 5524352, 3974912, 3593088, 2635008, 2614400, 639104, 654080, 204288, 0]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9045931, 9046171, 9048073, 9053611, 9057595, 9058485, 9058665]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (5, 2, [(2, 2)]),
  (31, 3, [(2, 1), (3, 1), (5, 1)]),
  (8406829, 10, [(2, 2), (3, 7), (31, 2)]),
  (13, 2, [(2, 2), (3, 1)]),
  (677, 2, [(2, 2), (13, 2)]),
  (7, 3, [(2, 1), (3, 1)]),
  (43, 3, [(2, 1), (3, 1), (7, 1)]),
  (1033, 5, [(2, 3), (3, 1), (43, 1)]),
  (8392093, 2, [(2, 2), (3, 1), (677, 1), (1033, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (233, 3, [(2, 3), (29, 1)]),
  (401, 3, [(2, 4), (5, 2)]),
  (8408971, 2, [(2, 1), (3, 2), (5, 1), (233, 1), (401, 1)]),
  (19, 2, [(2, 1), (3, 2)]),
  (17, 3, [(2, 4)]),
  (307, 5, [(2, 1), (3, 2), (17, 1)]),
  (699961, 7, [(2, 3), (3, 1), (5, 1), (19, 1), (307, 1)]),
  (8399533, 2, [(2, 2), (3, 1), (699961, 1)]),
  (37, 2, [(2, 2), (3, 2)]),
  (2887, 5, [(2, 1), (3, 1), (13, 1), (37, 1)]),
  (8418493, 2, [(2, 2), (3, 6), (2887, 1)]),
  (379, 2, [(2, 1), (3, 3), (7, 1)]),
  (73, 5, [(2, 3), (3, 2)]),
  (11681, 3, [(2, 5), (5, 1), (73, 1)]),
  (8854199, 7, [(2, 1), (379, 1), (11681, 1)]),
  (127, 3, [(2, 1), (3, 2), (7, 1)]),
  (53, 2, [(2, 2), (13, 1)]),
  (743, 5, [(2, 1), (7, 1), (53, 1)]),
  (1132333, 6, [(2, 2), (3, 1), (127, 1), (743, 1)]),
  (4529333, 2, [(2, 2), (1132333, 1)]),
  (9058667, 2, [(2, 1), (4529333, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9045931, 639104), (9046171, 654080), (9048073, 639104), (9053611, 654080), (9057595, 639104), (9058485, 204288), (9058665, 0)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9044931 + 2 * t ∧ (9044931 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9044931) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3140000
