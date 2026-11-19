/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3130000 through 3139999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3130000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [9240704, 9063936, 9200256, 9076736, 3880320, 6650240, 2836608, 9080576, 6950784, 7196288, 3124608, 2956928, 7474304, 7931520, 4531328, 6956544, 3558656, 7584768, 3109760, 5863680, 3255936, 7378304, 4206848, 3224064, 3893376, 3147776, 2796288, 2626688, 2759936, 7514880, 2944128, 3196544, 4929408, 4406528, 3191424, 3094016, 2793344, 5777024, 4009728, 2754176, 3654144, 3031680, 2718336, 3406208, 5319296, 4473600, 4204544, 3676416, 3808128, 3118976, 3801600, 3460608, 2832128, 0, 1227264, 1210496, 1617920, 437120, 1979264]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9583491, 9584133, 9588547, 9589789, 9592729, 9597409]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (5, 2, [(2, 2)]),
  (11, 2, [(2, 1), (5, 1)]),
  (23, 5, [(2, 1), (11, 1)]),
  (47, 5, [(2, 1), (23, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (59, 2, [(2, 1), (29, 1)]),
  (2395873, 5, [(2, 5), (3, 3), (47, 1), (59, 1)]),
  (9583493, 2, [(2, 2), (2395873, 1)]),
  (17, 3, [(2, 4)]),
  (13, 2, [(2, 2), (3, 1)]),
  (2731, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1)]),
  (835687, 5, [(2, 1), (3, 2), (17, 1), (2731, 1)]),
  (8356871, 17, [(2, 1), (5, 1), (835687, 1)]),
  (577, 5, [(2, 6), (3, 2)]),
  (698171, 2, [(2, 1), (5, 1), (11, 2), (577, 1)]),
  (8378053, 2, [(2, 2), (3, 1), (698171, 1)]),
  (43, 3, [(2, 1), (3, 1), (7, 1)]),
  (173, 2, [(2, 2), (43, 1)]),
  (265729, 19, [(2, 9), (3, 1), (173, 1)]),
  (7971871, 3, [(2, 1), (3, 1), (5, 1), (265729, 1)]),
  (67, 2, [(2, 1), (3, 1), (11, 1)]),
  (4423, 3, [(2, 1), (3, 1), (11, 1), (67, 1)]),
  (9155611, 3, [(2, 1), (3, 2), (5, 1), (23, 1), (4423, 1)]),
  (151, 6, [(2, 1), (3, 1), (5, 2)]),
  (1511, 11, [(2, 1), (5, 1), (151, 1)]),
  (3023, 5, [(2, 1), (1511, 1)]),
  (42323, 2, [(2, 1), (7, 1), (3023, 1)]),
  (1269691, 14, [(2, 1), (3, 1), (5, 1), (42323, 1)]),
  (7618147, 3, [(2, 1), (3, 1), (1269691, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9583491, 0), (9584133, 1227264), (9588547, 1210496), (9589789, 1617920), (9592729, 437120), (9597409, 1979264)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9581347 + 2 * t ∧ (9581347 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9581347) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3130000
