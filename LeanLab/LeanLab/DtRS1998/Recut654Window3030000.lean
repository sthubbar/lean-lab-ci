/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3030000 through 3039999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3030000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8583296, 8542848, 8423168, 8406528, 3352320, 3749120, 3222912, 8419328, 6299136, 6816896, 6538880, 2286720, 5206272, 5992832, 6293376, 2452352, 1839360, 2748800, 3144192, 2490368, 2534016, 6720896, 7274112, 7051136, 2598528, 2461568, 4272000, 3549440, 6184448, 3019008, 1886336, 3492096, 2539136, 6857472, 2890368, 1932800, 2566656, 1906688, 2996736, 2174720, 5119616, 2135936, 1827072, 5423360, 2811648, 3873920, 3150720, 2683008, 2436608, 2102528, 4661888, 3816192, 3390080, 3235968, 2467200, 0, 103296]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8728455, 8736021]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (5, 2, [(2, 2)]),
  (11, 2, [(2, 1), (5, 1)]),
  (3, 2, [(2, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (71, 7, [(2, 1), (5, 1), (7, 1)]),
  (127, 3, [(2, 1), (3, 2), (7, 1)]),
  (8728457, 3, [(2, 3), (11, 2), (71, 1), (127, 1)]),
  (19, 2, [(2, 1), (3, 2)]),
  (73, 5, [(2, 3), (3, 2)]),
  (97, 5, [(2, 5), (3, 1)]),
  (389, 2, [(2, 2), (97, 1)]),
  (227177, 3, [(2, 3), (73, 1), (389, 1)]),
  (8632727, 10, [(2, 1), (19, 1), (227177, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(8728455, 0), (8736021, 103296)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8723939 + 2 * t ∧ (8723939 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8723939) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3030000
