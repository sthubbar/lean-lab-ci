/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3210000 through 3219999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3210000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8932224, 8891776, 8772096, 5555200, 6648064, 6341760, 7276288, 4098048, 3160576, 8768256, 6642304, 6533376, 7069824, 2635648, 3571840, 2523648, 8755456, 5468544, 2801280, 3152128, 2516736, 7623040, 3898368, 3493120, 5010816, 2882944, 3345664, 7165824, 4620928, 4222848, 3239296, 2888064, 2915584, 2810496, 2839296, 7400064, 5772288, 3367936, 3031936, 4165120, 2484864, 2816128, 3584896, 3739008, 2862336, 2528128, 6887808, 3499648, 2785536, 3896064, 3250176, 2723200, 2648448, 2487808, 887040, 1325056, 0, 128640, 1696896, 949504, 247936]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9435401, 9435595, 9437969, 9438749, 9438887, 9439229, 9441251, 9444601, 9446117, 9447931, 9448049, 9449485]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (5, 2, [(2, 2)]),
  (7, 3, [(2, 1), (3, 1)]),
  (113, 3, [(2, 4), (7, 1)]),
  (1583, 5, [(2, 1), (7, 1), (113, 1)]),
  (79151, 13, [(2, 1), (5, 2), (1583, 1)]),
  (158303, 5, [(2, 1), (79151, 1)]),
  (8548363, 2, [(2, 1), (3, 3), (158303, 1)]),
  (11, 2, [(2, 1), (5, 1)]),
  (18433, 5, [(2, 11), (3, 2)]),
  (405527, 5, [(2, 1), (11, 1), (18433, 1)]),
  (8110541, 3, [(2, 2), (5, 1), (405527, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (52433, 3, [(2, 4), (29, 1), (113, 1)]),
  (314599, 3, [(2, 1), (3, 1), (52433, 1)]),
  (9437971, 3, [(2, 1), (3, 1), (5, 1), (314599, 1)]),
  (41, 6, [(2, 3), (5, 1)]),
  (83, 2, [(2, 1), (41, 1)]),
  (89, 3, [(2, 3), (11, 1)]),
  (3739, 7, [(2, 1), (3, 1), (7, 1), (89, 1)]),
  (9310111, 3, [(2, 1), (3, 1), (5, 1), (83, 1), (3739, 1)]),
  (19, 2, [(2, 1), (3, 2)]),
  (73, 5, [(2, 3), (3, 2)]),
  (293, 2, [(2, 2), (73, 1)]),
  (9377, 3, [(2, 5), (293, 1)]),
  (356327, 5, [(2, 1), (19, 1), (9377, 1)]),
  (8551849, 14, [(2, 3), (3, 1), (356327, 1)]),
  (17, 3, [(2, 4)]),
  (409, 21, [(2, 3), (3, 1), (17, 1)]),
  (8552191, 3, [(2, 1), (3, 1), (5, 1), (17, 1), (41, 1), (409, 1)]),
  (37, 2, [(2, 2), (3, 2)]),
  (71707, 2, [(2, 1), (3, 1), (17, 1), (19, 1), (37, 1)]),
  (7744357, 2, [(2, 2), (3, 3), (71707, 1)]),
  (23, 5, [(2, 1), (11, 1)]),
  (137, 3, [(2, 3), (17, 1)]),
  (337, 10, [(2, 4), (3, 1), (7, 1)]),
  (4247549, 3, [(2, 2), (23, 1), (137, 1), (337, 1)]),
  (8495099, 2, [(2, 1), (4247549, 1)]),
  (31, 3, [(2, 1), (3, 1), (5, 1)]),
  (3163, 3, [(2, 1), (3, 1), (17, 1), (31, 1)]),
  (8559079, 6, [(2, 1), (3, 1), (11, 1), (41, 1), (3163, 1)]),
  (13, 2, [(2, 2), (3, 1)]),
  (9829, 10, [(2, 2), (3, 3), (7, 1), (13, 1)]),
  (176923, 2, [(2, 1), (3, 2), (9829, 1)]),
  (9199997, 2, [(2, 2), (13, 1), (176923, 1)]),
  (139, 2, [(2, 1), (3, 1), (23, 1)]),
  (2053, 2, [(2, 2), (3, 3), (19, 1)]),
  (8561011, 2, [(2, 1), (3, 1), (5, 1), (139, 1), (2053, 1)]),
  (239, 7, [(2, 1), (7, 1), (17, 1)]),
  (184031, 14, [(2, 1), (5, 1), (7, 1), (11, 1), (239, 1)]),
  (9201551, 7, [(2, 1), (5, 2), (184031, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9435401, 887040), (9435595, 1325056), (9437969, 0), (9438749, 128640), (9438887, 887040), (9439229, 887040), (9441251, 1696896), (9444601, 949504), (9446117, 887040), (9447931, 247936), (9448049, 887040), (9449485, 247936)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9432867 + 2 * t ∧ (9432867 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9432867) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3210000
