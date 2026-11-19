/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3010000 through 3019999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3010000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8932224, 8891776, 8772096, 8755456, 7623040, 6341760, 4620928, 8768256, 6648064, 2523648, 2528128, 3898368, 2176000, 2888064, 6642304, 5010816, 3160576, 4098048, 4165120, 2801280, 3571840, 2915584, 6533376, 7165824, 3841024, 7276288, 6887808, 2648448, 3152128, 2445696, 3345664, 2235264, 2723200, 2318208, 5555200, 2785536, 3499648, 7069824, 2947456, 2128896, 5468544, 4222848, 2409856, 2451456, 7206400, 5772288, 3584896, 3493120, 3031936, 2281728, 3896064, 3701248, 2882944, 2862336, 2188288, 348928, 247936, 379648, 0, 128640, 426496]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9034693, 9036529, 9038011, 9039439, 9040277, 9043589, 9048959, 9050761]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (5, 2, [(2, 2)]),
  (11, 2, [(2, 1), (5, 1)]),
  (23, 5, [(2, 1), (11, 1)]),
  (3, 2, [(2, 1)]),
  (31, 3, [(2, 1), (3, 1), (5, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (6091, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (29, 1)]),
  (8685767, 5, [(2, 1), (23, 1), (31, 1), (6091, 1)]),
  (17, 3, [(2, 4)]),
  (13, 2, [(2, 2), (3, 1)]),
  (79, 3, [(2, 1), (3, 1), (13, 1)]),
  (8059, 3, [(2, 1), (3, 1), (17, 1), (79, 1)]),
  (8687603, 7, [(2, 1), (7, 2), (11, 1), (8059, 1)]),
  (73, 5, [(2, 3), (3, 2)]),
  (43, 3, [(2, 1), (3, 1), (7, 1)]),
  (173, 2, [(2, 2), (43, 1)]),
  (30103, 3, [(2, 1), (3, 1), (29, 1), (173, 1)]),
  (8790077, 2, [(2, 2), (73, 1), (30103, 1)]),
  (37, 2, [(2, 2), (3, 2)]),
  (53, 2, [(2, 2), (13, 1)]),
  (541237, 5, [(2, 2), (3, 1), (23, 1), (37, 1), (53, 1)]),
  (8659793, 3, [(2, 4), (541237, 1)]),
  (19, 2, [(2, 1), (3, 2)]),
  (61, 2, [(2, 2), (3, 1), (5, 1)]),
  (115901, 2, [(2, 2), (5, 2), (19, 1), (61, 1)]),
  (9040279, 3, [(2, 1), (3, 1), (13, 1), (115901, 1)]),
  (1801, 11, [(2, 3), (3, 2), (5, 2)]),
  (8914951, 3, [(2, 1), (3, 2), (5, 2), (11, 1), (1801, 1)]),
  (101, 2, [(2, 2), (5, 2)]),
  (8920321, 13, [(2, 8), (3, 1), (5, 1), (23, 1), (101, 1)]),
  (59, 2, [(2, 1), (29, 1)]),
  (197, 2, [(2, 2), (7, 2)]),
  (8624267, 2, [(2, 1), (7, 1), (53, 1), (59, 1), (197, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9034693, 348928), (9036529, 348928), (9038011, 247936), (9039439, 379648), (9040277, 0), (9043589, 128640), (9048959, 128640), (9050761, 426496)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9032867 + 2 * t ∧ (9032867 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9032867) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3010000
