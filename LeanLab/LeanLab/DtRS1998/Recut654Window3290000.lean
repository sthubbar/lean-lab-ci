/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3290000 through 3299999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3290000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [9324160, 8643456, 8803584, 8626816, 6759168, 7147648, 8639616, 6519424, 6213120, 8763136, 6513664, 6941184, 3364480, 3969408, 4492288, 2672640, 2656896, 2754304, 2759424, 3031936, 2969088, 3443200, 3769728, 3456256, 7037184, 3371008, 6404736, 3712384, 2786944, 2710656, 2687488, 7271424, 4036480, 3610368, 5643648, 2594560, 3121536, 3110656, 7494400, 5339904, 7077760, 3217024, 2733696, 4882176, 2818816, 2681856, 2519808, 3767424, 3023488, 2507008, 5426560, 3572608, 3239296, 220288, 0, 899328, 773376, 869376, 758400, 1223040, 169344]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9467047, 9471947, 9473363, 9475481, 9475901, 9477539, 9483527, 9483629, 9484199]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (5, 2, [(2, 2)]),
  (3, 2, [(2, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (43, 3, [(2, 1), (3, 1), (7, 1)]),
  (231169, 17, [(2, 8), (3, 1), (7, 1), (43, 1)]),
  (9246761, 3, [(2, 3), (5, 1), (231169, 1)]),
  (13, 2, [(2, 2), (3, 1)]),
  (53, 2, [(2, 2), (13, 1)]),
  (281, 3, [(2, 3), (5, 1), (7, 1)]),
  (9471949, 2, [(2, 2), (3, 1), (53, 2), (281, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (97, 5, [(2, 5), (3, 1)]),
  (127, 3, [(2, 1), (3, 2), (7, 1)]),
  (714503, 5, [(2, 1), (29, 1), (97, 1), (127, 1)]),
  (8574037, 5, [(2, 2), (3, 1), (714503, 1)]),
  (17, 3, [(2, 4)]),
  (137, 3, [(2, 3), (17, 1)]),
  (4933, 2, [(2, 2), (3, 2), (137, 1)]),
  (29599, 13, [(2, 1), (3, 1), (4933, 1)]),
  (8702107, 5, [(2, 1), (3, 1), (7, 2), (29599, 1)]),
  (613, 2, [(2, 2), (3, 2), (17, 1)]),
  (1434421, 6, [(2, 2), (3, 2), (5, 1), (13, 1), (613, 1)]),
  (8606527, 3, [(2, 1), (3, 1), (1434421, 1)]),
  (41, 6, [(2, 3), (5, 1)]),
  (83, 2, [(2, 1), (41, 1)]),
  (167, 5, [(2, 1), (83, 1)]),
  (5011, 2, [(2, 1), (3, 1), (5, 1), (167, 1)]),
  (8719141, 2, [(2, 2), (3, 1), (5, 1), (29, 1), (5011, 1)]),
  (19, 2, [(2, 1), (3, 2)]),
  (229, 6, [(2, 2), (3, 1), (19, 1)]),
  (8260489, 7, [(2, 3), (3, 3), (167, 1), (229, 1)]),
  (11, 2, [(2, 1), (5, 1)]),
  (23, 5, [(2, 1), (11, 1)]),
  (1013, 3, [(2, 2), (11, 1), (23, 1)]),
  (6079, 17, [(2, 1), (3, 1), (1013, 1)]),
  (24317, 2, [(2, 2), (6079, 1)]),
  (9483631, 6, [(2, 1), (3, 1), (5, 1), (13, 1), (24317, 1)]),
  (61, 2, [(2, 2), (3, 1), (5, 1)]),
  (2441, 6, [(2, 3), (5, 1), (61, 1)]),
  (9314857, 5, [(2, 3), (3, 2), (53, 1), (2441, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9467047, 220288), (9471947, 0), (9473363, 899328), (9475481, 773376), (9475901, 869376), (9477539, 758400), (9483527, 1223040), (9483629, 0), (9484199, 169344)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9464227 + 2 * t ∧ (9464227 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9464227) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3290000
