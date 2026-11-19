/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3280000 through 3289999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3280000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [9807616, 9126912, 9287040, 9110272, 6696576, 7631104, 7242624, 6997120, 9123072, 7977856, 3003264, 9246592, 4975744, 6888192, 4195840, 7424640, 5910016, 6127104, 3237760, 7520640, 3506944, 3156096, 3515392, 3165312, 4253184, 7561216, 4250880, 7002880, 4093824, 4519936, 3854464, 3217152, 3604992, 3170944, 7754880, 3926656, 3140352, 4452864, 3270400, 3847936, 5823360, 3386752, 5365632, 3939712, 4577664, 3700480, 2990464, 4056064, 3452544, 3594112, 3242880, 3194112, 1241856, 1664256, 891904, 1092096, 1459200, 0]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9928043, 9930335, 9934315, 9935105, 9935477, 9938975, 9940985, 9940997, 9943355, 9946547]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (5, 2, [(2, 2)]),
  (41, 6, [(2, 3), (5, 1)]),
  (1231, 3, [(2, 1), (3, 1), (5, 1), (41, 1)]),
  (34469, 10, [(2, 2), (7, 1), (1231, 1)]),
  (8686189, 2, [(2, 2), (3, 2), (7, 1), (34469, 1)]),
  (17, 3, [(2, 4)]),
  (11, 2, [(2, 1), (5, 1)]),
  (23, 5, [(2, 1), (11, 1)]),
  (1013, 3, [(2, 2), (11, 1), (23, 1)]),
  (8266081, 7, [(2, 5), (3, 1), (5, 1), (17, 1), (1013, 1)]),
  (109, 6, [(2, 2), (3, 3)]),
  (6977, 3, [(2, 6), (109, 1)]),
  (41863, 3, [(2, 1), (3, 1), (6977, 1)]),
  (2260603, 2, [(2, 1), (3, 3), (41863, 1)]),
  (9042413, 2, [(2, 2), (2260603, 1)]),
  (127, 3, [(2, 1), (3, 2), (7, 1)]),
  (211, 2, [(2, 1), (3, 1), (5, 1), (7, 1)]),
  (8843011, 3, [(2, 1), (3, 1), (5, 1), (11, 1), (127, 1), (211, 1)]),
  (8693623, 5, [(2, 1), (3, 3), (7, 1), (109, 1), (211, 1)]),
  (19, 2, [(2, 1), (3, 2)]),
  (83, 2, [(2, 1), (41, 1)]),
  (4649, 3, [(2, 3), (7, 1), (83, 1)]),
  (8479777, 5, [(2, 5), (3, 1), (19, 1), (4649, 1)]),
  (31, 3, [(2, 1), (3, 1), (5, 1)]),
  (1471, 6, [(2, 1), (3, 1), (5, 1), (7, 2)]),
  (8481787, 2, [(2, 1), (3, 1), (31, 2), (1471, 1)]),
  (43, 3, [(2, 1), (3, 1), (7, 1)]),
  (947, 2, [(2, 1), (11, 1), (43, 1)]),
  (1531, 2, [(2, 1), (3, 2), (5, 1), (17, 1)]),
  (8699143, 3, [(2, 1), (3, 1), (947, 1), (1531, 1)]),
  (239, 7, [(2, 1), (7, 1), (17, 1)]),
  (433, 5, [(2, 4), (3, 3)]),
  (1733, 2, [(2, 2), (433, 1)]),
  (3467, 2, [(2, 1), (1733, 1)]),
  (9943357, 2, [(2, 2), (3, 1), (239, 1), (3467, 1)]),
  (89, 3, [(2, 3), (11, 1)]),
  (179, 2, [(2, 1), (89, 1)]),
  (359, 7, [(2, 1), (179, 1)]),
  (719, 11, [(2, 1), (359, 1)]),
  (1439, 7, [(2, 1), (719, 1)]),
  (69073, 10, [(2, 4), (3, 1), (1439, 1)]),
  (276293, 2, [(2, 2), (69073, 1)]),
  (9946549, 2, [(2, 2), (3, 2), (276293, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9928043, 1241856), (9930335, 1664256), (9934315, 891904), (9935105, 1092096), (9935477, 1241856), (9938975, 1459200), (9940985, 1459200), (9940997, 1241856), (9943355, 0), (9946547, 0)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9927683 + 2 * t ∧ (9927683 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9927683) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3280000
