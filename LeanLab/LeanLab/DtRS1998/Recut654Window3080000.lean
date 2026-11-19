/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3080000 through 3089999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3080000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8932224, 8755456, 8772096, 7623040, 7276288, 6341760, 8768256, 6642304, 5555200, 6887808, 8891776, 7165824, 2487808, 2801280, 6648064, 4222848, 4620928, 2648448, 6533376, 3345664, 2816128, 2523648, 4165120, 2785536, 3160576, 3499648, 4098048, 2516736, 3571840, 2882944, 2445696, 5468544, 3367936, 3250176, 3493120, 2723200, 3898368, 7400064, 3896064, 7069824, 3841024, 3031936, 5010816, 3239296, 2635648, 3739008, 5772288, 3152128, 2409856, 7206400, 3701248, 2947456, 2888064, 2862336, 887040, 348928, 247936, 0]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9181979, 9182009, 9182353, 9183571, 9192437]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (5, 2, [(2, 2)]),
  (15361, 7, [(2, 10), (3, 1), (5, 1)]),
  (8294941, 2, [(2, 2), (3, 3), (5, 1), (15361, 1)]),
  (276499, 3, [(2, 1), (3, 2), (15361, 1)]),
  (8294971, 2, [(2, 1), (3, 1), (5, 1), (276499, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (11, 2, [(2, 1), (5, 1)]),
  (23, 5, [(2, 1), (11, 1)]),
  (163, 2, [(2, 1), (3, 4)]),
  (653, 2, [(2, 2), (163, 1)]),
  (3919, 3, [(2, 1), (3, 1), (653, 1)]),
  (8833427, 2, [(2, 1), (7, 2), (23, 1), (3919, 1)]),
  (47, 5, [(2, 1), (23, 1)]),
  (5171, 2, [(2, 1), (5, 1), (11, 1), (47, 1)]),
  (62053, 2, [(2, 2), (3, 1), (5171, 1)]),
  (2233909, 2, [(2, 2), (3, 2), (62053, 1)]),
  (8935637, 2, [(2, 2), (2233909, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (73, 5, [(2, 3), (3, 2)]),
  (293, 2, [(2, 2), (73, 1)]),
  (587, 2, [(2, 1), (293, 1)]),
  (510691, 2, [(2, 1), (3, 1), (5, 1), (29, 1), (587, 1)]),
  (9192439, 3, [(2, 1), (3, 2), (510691, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9181979, 887040), (9182009, 887040), (9182353, 348928), (9183571, 247936), (9192437, 0)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9172867 + 2 * t ∧ (9172867 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9172867) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3080000
