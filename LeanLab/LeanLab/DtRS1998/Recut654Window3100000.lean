/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3100000 through 3109999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3100000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8891776, 8932224, 8772096, 6642304, 7276288, 6341760, 8755456, 2523648, 5555200, 8768256, 2801280, 2487808, 6648064, 6887808, 7165824, 3152128, 3571840, 6533376, 3739008, 3584896, 3898368, 2635648, 7069824, 3841024, 5010816, 3239296, 5468544, 7206400, 3160576, 2235264, 2816128, 5772288, 7400064, 7623040, 2947456, 2785536, 4165120, 4098048, 3896064, 4620928, 2862336, 2451456, 3493120, 2915584, 2484864, 3345664, 3031936, 2888064, 2409856, 2255616, 4222848, 3367936, 2723200, 2648448, 2516736, 193408, 998016, 0, 846208, 348928]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9216499, 9222071, 9225869, 9226243, 9231889, 9231907]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (13, 2, [(2, 2), (3, 1)]),
  (73, 5, [(2, 3), (3, 2)]),
  (5, 2, [(2, 2)]),
  (11, 2, [(2, 1), (5, 1)]),
  (2377, 5, [(2, 3), (3, 3), (11, 1)]),
  (9023093, 2, [(2, 2), (13, 1), (73, 1), (2377, 1)]),
  (17, 3, [(2, 4)]),
  (23, 5, [(2, 1), (11, 1)]),
  (3359, 11, [(2, 1), (23, 1), (73, 1)]),
  (6719, 11, [(2, 1), (3359, 1)]),
  (8224057, 5, [(2, 3), (3, 2), (17, 1), (6719, 1)]),
  (41, 6, [(2, 3), (5, 1)]),
  (739, 3, [(2, 1), (3, 2), (41, 1)]),
  (2957, 2, [(2, 2), (739, 1)]),
  (307529, 3, [(2, 3), (13, 1), (2957, 1)]),
  (9225871, 3, [(2, 1), (3, 1), (5, 1), (307529, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (71, 7, [(2, 1), (5, 1), (7, 1)]),
  (1279, 3, [(2, 1), (3, 2), (71, 1)]),
  (299287, 5, [(2, 1), (3, 2), (13, 1), (1279, 1)]),
  (8380037, 2, [(2, 2), (7, 1), (299287, 1)]),
  (199, 3, [(2, 1), (3, 2), (11, 1)]),
  (2029, 2, [(2, 2), (3, 1), (13, 2)]),
  (8882963, 2, [(2, 1), (11, 1), (199, 1), (2029, 1)]),
  (97, 5, [(2, 5), (3, 1)]),
  (1747, 2, [(2, 1), (3, 2), (97, 1)]),
  (83857, 5, [(2, 4), (3, 1), (1747, 1)]),
  (8385701, 2, [(2, 2), (5, 2), (83857, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9216499, 193408), (9222071, 998016), (9225869, 0), (9226243, 846208), (9231889, 348928), (9231907, 846208)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9212867 + 2 * t ∧ (9212867 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9212867) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3100000
