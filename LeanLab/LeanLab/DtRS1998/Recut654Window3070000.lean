/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3070000 through 3079999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3070000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8803584, 8763136, 8643456, 5426560, 6513664, 6213120, 8626816, 2395008, 2399488, 8639616, 6519424, 6759168, 7494400, 7037184, 3443200, 2106624, 7147648, 3610368, 3121536, 2786944, 3769728, 3023488, 2126976, 3364480, 2903296, 2969088, 4882176, 2507008, 2317056, 2047360, 2519808, 3767424, 2687488, 3031936, 7271424, 4094208, 3712384, 2594560, 2672640, 3239296, 5339904, 3456256, 3110656, 7077760, 4036480, 2681856, 2059648, 6941184, 6404736, 2388096, 2153088, 4492288, 3217024, 2754304, 2189568, 220288, 0, 119296]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9026659, 9040571, 9043123]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (5, 2, [(2, 2)]),
  (11, 2, [(2, 1), (5, 1)]),
  (89, 3, [(2, 3), (11, 1)]),
  (71, 7, [(2, 1), (5, 1), (7, 1)]),
  (853, 2, [(2, 2), (3, 1), (71, 1)]),
  (8806373, 2, [(2, 2), (29, 1), (89, 1), (853, 1)]),
  (13, 2, [(2, 2), (3, 1)]),
  (131, 2, [(2, 1), (5, 1), (13, 1)]),
  (9040573, 2, [(2, 2), (3, 5), (71, 1), (131, 1)]),
  (41, 6, [(2, 3), (5, 1)]),
  (83, 2, [(2, 1), (41, 1)]),
  (151, 6, [(2, 1), (3, 1), (5, 2)]),
  (26879, 13, [(2, 1), (89, 1), (151, 1)]),
  (8923829, 2, [(2, 2), (83, 1), (26879, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9026659, 220288), (9040571, 0), (9043123, 119296)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9024227 + 2 * t ∧ (9024227 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9024227) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3070000
