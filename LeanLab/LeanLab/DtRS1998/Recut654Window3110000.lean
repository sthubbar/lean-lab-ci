/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3110000 through 3119999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3110000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8583296, 8542848, 8423168, 7274112, 8406528, 2174720, 6293376, 8419328, 2467200, 5992832, 3816192, 6720896, 6927360, 1906688, 3222912, 2748800, 4272000, 6184448, 6299136, 2452352, 5206272, 2135936, 3749120, 2890368, 2096768, 2566656, 2060928, 3547136, 3390080, 3150720, 1932800, 6857472, 2996736, 2811648, 2436608, 3873920, 2598528, 2901248, 5119616, 3144192, 2461568, 6538880, 2683008, 2138880, 2167808, 6816896, 3549440, 3352320, 2803200, 2513408, 1969280, 2374272, 538112, 77568, 0, 287616, 279936, 679040]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8884927, 8887305, 8891091, 8898003, 8900211, 8903161]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (43, 3, [(2, 1), (3, 1), (7, 1)]),
  (337, 10, [(2, 4), (3, 1), (7, 1)]),
  (8346817, 7, [(2, 6), (3, 2), (43, 1), (337, 1)]),
  (13, 2, [(2, 2), (3, 1)]),
  (53, 2, [(2, 2), (13, 1)]),
  (107, 2, [(2, 1), (53, 1)]),
  (5, 2, [(2, 2)]),
  (5881, 31, [(2, 3), (3, 1), (5, 1), (7, 2)]),
  (8809739, 2, [(2, 1), (7, 1), (107, 1), (5881, 1)]),
  (11, 2, [(2, 1), (5, 1)]),
  (23, 5, [(2, 1), (11, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (59, 2, [(2, 1), (29, 1)]),
  (317539, 2, [(2, 1), (3, 2), (13, 1), (23, 1), (59, 1)]),
  (8891093, 2, [(2, 2), (7, 1), (317539, 1)]),
  (17, 3, [(2, 4)]),
  (103, 5, [(2, 1), (3, 1), (17, 1)]),
  (20899, 2, [(2, 1), (3, 5), (43, 1)]),
  (8610389, 2, [(2, 2), (103, 1), (20899, 1)]),
  (61, 2, [(2, 2), (3, 1), (5, 1)]),
  (8620277, 2, [(2, 2), (7, 3), (61, 1), (103, 1)]),
  (67, 2, [(2, 1), (3, 1), (11, 1)]),
  (193, 5, [(2, 6), (3, 1)]),
  (1370687, 5, [(2, 1), (53, 1), (67, 1), (193, 1)]),
  (8224123, 3, [(2, 1), (3, 1), (1370687, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(8884927, 538112), (8887305, 77568), (8891091, 0), (8898003, 287616), (8900211, 279936), (8903161, 679040)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8883939 + 2 * t ∧ (8883939 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8883939) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3110000
