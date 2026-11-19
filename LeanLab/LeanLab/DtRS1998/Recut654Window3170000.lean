/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3170000 through 3179999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3170000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8932224, 8891776, 8772096, 6648064, 5555200, 2523648, 2528128, 6341760, 8755456, 8768256, 7276288, 2801280, 2723200, 7165824, 3898368, 3345664, 6887808, 4620928, 6533376, 3493120, 4098048, 7206400, 7069824, 3160576, 2862336, 6642304, 3896064, 3584896, 3250176, 3097728, 3571840, 3239296, 2648448, 2882944, 2785536, 2516736, 3841024, 5010816, 7623040, 7400064, 2409856, 3701248, 4222848, 3152128, 2451456, 3499648, 2888064, 2484864, 5468544, 3031936, 2915584, 2839296, 2810496, 2635648, 1309440, 0, 1104384, 426496, 247936, 998016, 128640]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9352919, 9357287, 9357659, 9357989, 9360961, 9364081, 9364895, 9365819, 9372659]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (5, 2, [(2, 2)]),
  (31, 3, [(2, 1), (3, 1), (5, 1)]),
  (1117, 2, [(2, 2), (3, 2), (31, 1)]),
  (11171, 2, [(2, 1), (5, 1), (1117, 1)]),
  (22343, 5, [(2, 1), (11171, 1)]),
  (8043481, 11, [(2, 3), (3, 2), (5, 1), (22343, 1)]),
  (13, 2, [(2, 2), (3, 1)]),
  (131, 2, [(2, 1), (5, 1), (13, 1)]),
  (12577, 10, [(2, 5), (3, 1), (131, 1)]),
  (9357289, 11, [(2, 3), (3, 1), (31, 1), (12577, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (43, 3, [(2, 1), (3, 1), (7, 1)]),
  (9357661, 22, [(2, 2), (3, 3), (5, 1), (13, 1), (31, 1), (43, 1)]),
  (19, 2, [(2, 1), (3, 2)]),
  (181, 2, [(2, 2), (3, 2), (5, 1)]),
  (1375601, 3, [(2, 4), (5, 2), (19, 1), (181, 1)]),
  (8253607, 3, [(2, 1), (3, 1), (1375601, 1)]),
  (601, 7, [(2, 3), (3, 1), (5, 2)]),
  (29, 2, [(2, 2), (7, 1)]),
  (929, 3, [(2, 5), (29, 1)]),
  (7433, 3, [(2, 3), (929, 1)]),
  (8934467, 2, [(2, 1), (601, 1), (7433, 1)]),
  (11, 2, [(2, 1), (5, 1)]),
  (23, 5, [(2, 1), (11, 1)]),
  (47, 5, [(2, 1), (23, 1)]),
  (373, 2, [(2, 2), (3, 1), (31, 1)]),
  (350621, 3, [(2, 2), (5, 1), (47, 1), (373, 1)]),
  (9116147, 2, [(2, 1), (13, 1), (350621, 1)]),
  (41, 6, [(2, 3), (5, 1)]),
  (83, 2, [(2, 1), (41, 1)]),
  (17431, 3, [(2, 1), (3, 1), (5, 1), (7, 1), (83, 1)]),
  (8366881, 11, [(2, 5), (3, 1), (5, 1), (17431, 1)]),
  (17, 3, [(2, 4)]),
  (283, 3, [(2, 1), (3, 1), (47, 1)]),
  (153953, 3, [(2, 5), (17, 1), (283, 1)]),
  (9237181, 2, [(2, 2), (3, 1), (5, 1), (153953, 1)]),
  (37, 2, [(2, 2), (3, 2)]),
  (149, 2, [(2, 2), (37, 1)]),
  (154067, 2, [(2, 1), (11, 1), (47, 1), (149, 1)]),
  (9244021, 6, [(2, 2), (3, 1), (5, 1), (154067, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9352919, 1309440), (9357287, 0), (9357659, 0), (9357989, 1104384), (9360961, 426496), (9364081, 247936), (9364895, 998016), (9365819, 128640), (9372659, 128640)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9352867 + 2 * t ∧ (9352867 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9352867) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3170000
