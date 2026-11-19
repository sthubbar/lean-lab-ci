/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3060000 through 3069999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3060000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8803584, 8763136, 8643456, 8626816, 7494400, 2189568, 6519424, 8639616, 2399488, 6213120, 2153088, 3443200, 2359168, 2759424, 3023488, 2126976, 6513664, 2395008, 6941184, 7147648, 4882176, 4036480, 2786944, 3969408, 3110656, 2106624, 3217024, 2733696, 2672640, 2903296, 7271424, 7077760, 5643648, 3767424, 3456256, 6404736, 3712384, 2754304, 3239296, 2969088, 7037184, 5426560, 5339904, 4492288, 2059648, 4094208, 3364480, 2519808, 3121536, 2687488, 2507008, 2322816, 2047360, 0, 899328, 251008]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9005879, 9012539, 9017419]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (5, 2, [(2, 2)]),
  (13, 2, [(2, 2), (3, 1)]),
  (11, 2, [(2, 1), (5, 1)]),
  (23, 5, [(2, 1), (11, 1)]),
  (251, 6, [(2, 1), (5, 3)]),
  (9005881, 14, [(2, 3), (3, 1), (5, 1), (13, 1), (23, 1), (251, 1)]),
  (37, 2, [(2, 2), (3, 2)]),
  (7, 3, [(2, 1), (3, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (6091, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (29, 1)]),
  (8113213, 2, [(2, 2), (3, 2), (37, 1), (6091, 1)]),
  (53, 2, [(2, 2), (13, 1)]),
  (59, 2, [(2, 1), (29, 1)]),
  (827, 2, [(2, 1), (7, 1), (59, 1)]),
  (41351, 7, [(2, 1), (5, 2), (827, 1)]),
  (8766413, 2, [(2, 2), (53, 1), (41351, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9005879, 0), (9012539, 899328), (9017419, 251008)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9004227 + 2 * t ∧ (9004227 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9004227) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3060000
