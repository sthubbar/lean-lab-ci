/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3050000 through 3059999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3050000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8932224, 8891776, 8772096, 7623040, 8755456, 8768256, 6642304, 2801280, 2487808, 3898368, 6648064, 6341760, 5555200, 2648448, 2235264, 3160576, 5772288, 2176000, 3250176, 3841024, 2188288, 6533376, 3152128, 7069824, 2635648, 2445696, 3367936, 2281728, 2409856, 2484864, 4165120, 3584896, 2785536, 2318208, 7400064, 2915584, 2723200, 2523648, 2862336, 7276288, 3896064, 7206400, 3345664, 2882944, 5468544, 3493120, 3239296, 2839296, 2528128, 7165824, 6887808, 4098048, 3097728, 2947456, 2810496, 1027968, 636544, 887040, 902016, 998016, 193408, 0, 1351680, 348928, 737280]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9117269, 9117529, 9122747, 9124061, 9124937, 9125951, 9126679, 9127229, 9129401, 9129659, 9131389, 9132191]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (13, 2, [(2, 2), (3, 1)]),
  (17, 3, [(2, 4)]),
  (137, 3, [(2, 3), (17, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (757, 2, [(2, 2), (3, 3), (7, 1)]),
  (8089303, 3, [(2, 1), (3, 1), (13, 1), (137, 1), (757, 1)]),
  (43, 3, [(2, 1), (3, 1), (7, 1)]),
  (73, 5, [(2, 3), (3, 2)]),
  (293, 2, [(2, 2), (73, 1)]),
  (587, 2, [(2, 1), (293, 1)]),
  (1060123, 2, [(2, 1), (3, 1), (7, 1), (43, 1), (587, 1)]),
  (4240493, 2, [(2, 2), (1060123, 1)]),
  (8480987, 2, [(2, 1), (4240493, 1)]),
  (5, 2, [(2, 2)]),
  (31, 3, [(2, 1), (3, 1), (5, 1)]),
  (131, 2, [(2, 1), (5, 1), (13, 1)]),
  (8235709, 2, [(2, 2), (3, 1), (13, 2), (31, 1), (131, 1)]),
  (163, 2, [(2, 1), (3, 4)]),
  (1201, 11, [(2, 4), (3, 1), (5, 2)]),
  (8222047, 3, [(2, 1), (3, 1), (7, 1), (163, 1), (1201, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (233, 3, [(2, 3), (29, 1)]),
  (467, 2, [(2, 1), (233, 1)]),
  (457661, 10, [(2, 2), (5, 1), (7, 2), (467, 1)]),
  (8237899, 2, [(2, 1), (3, 2), (457661, 1)]),
  (103, 5, [(2, 1), (3, 1), (17, 1)]),
  (8127937, 5, [(2, 6), (3, 2), (103, 1), (137, 1)]),
  (601, 7, [(2, 3), (3, 1), (5, 2)]),
  (929, 3, [(2, 5), (29, 1)]),
  (1116659, 2, [(2, 1), (601, 1), (929, 1)]),
  (8933273, 3, [(2, 3), (1116659, 1)]),
  (443, 2, [(2, 1), (13, 1), (17, 1)]),
  (887, 5, [(2, 1), (443, 1)]),
  (9127231, 3, [(2, 1), (3, 1), (5, 1), (7, 3), (887, 1)]),
  (109, 6, [(2, 2), (3, 3)]),
  (4201, 11, [(2, 3), (3, 1), (5, 2), (7, 1)]),
  (8242363, 2, [(2, 1), (3, 2), (109, 1), (4201, 1)]),
  (257, 3, [(2, 8)]),
  (1543, 5, [(2, 1), (3, 1), (257, 1)]),
  (6173, 2, [(2, 2), (1543, 1)]),
  (7777981, 14, [(2, 2), (3, 2), (5, 1), (7, 1), (6173, 1)]),
  (151, 6, [(2, 1), (3, 1), (5, 2)]),
  (2237, 2, [(2, 2), (13, 1), (43, 1)]),
  (8782463, 5, [(2, 1), (13, 1), (151, 1), (2237, 1)]),
  (11, 2, [(2, 1), (5, 1)]),
  (23, 5, [(2, 1), (11, 1)]),
  (47, 5, [(2, 1), (23, 1)]),
  (283, 3, [(2, 1), (3, 1), (47, 1)]),
  (8394913, 10, [(2, 5), (3, 2), (103, 1), (283, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9117269, 1027968), (9117529, 636544), (9122747, 887040), (9124061, 902016), (9124937, 887040), (9125951, 998016), (9126679, 193408), (9127229, 0), (9129401, 887040), (9129659, 1351680), (9131389, 348928), (9132191, 737280)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9112867 + 2 * t ∧ (9112867 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9112867) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3050000
