/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3180000 through 3189999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3180000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8763136, 8803584, 8643456, 7147648, 6519424, 6213120, 3443200, 2395008, 8639616, 5426560, 6513664, 3969408, 2399488, 2672640, 4036480, 2356224, 3110656, 2519808, 3456256, 4882176, 7077760, 6941184, 2359168, 2388096, 2786944, 2759424, 3239296, 3610368, 2733696, 4492288, 3769728, 3364480, 2317056, 3031936, 3712384, 6759168, 7494400, 2969088, 3371008, 5643648, 3121536, 2507008, 7271424, 8626816, 3767424, 3217024, 2681856, 2754304, 4094208, 3023488, 2818816, 2656896, 2322816, 2281216, 220288, 0, 773376, 64768, 297856, 608640, 169344, 1196416]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9247639, 9248009, 9252041, 9252535, 9254179, 9258601, 9258643, 9260897, 9261731, 9264179, 9264181]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (5, 2, [(2, 2)]),
  (41, 6, [(2, 3), (5, 1)]),
  (83, 2, [(2, 1), (41, 1)]),
  (167, 5, [(2, 1), (83, 1)]),
  (233, 3, [(2, 3), (29, 1)]),
  (9027353, 3, [(2, 3), (29, 1), (167, 1), (233, 1)]),
  (43, 3, [(2, 1), (3, 1), (7, 1)]),
  (11, 2, [(2, 1), (5, 1)]),
  (67, 2, [(2, 1), (3, 1), (11, 1)]),
  (13, 2, [(2, 2), (3, 1)]),
  (53, 2, [(2, 2), (13, 1)]),
  (107, 2, [(2, 1), (53, 1)]),
  (9248011, 2, [(2, 1), (3, 1), (5, 1), (43, 1), (67, 1), (107, 1)]),
  (89, 3, [(2, 3), (11, 1)]),
  (9613, 2, [(2, 2), (3, 3), (89, 1)]),
  (8478667, 3, [(2, 1), (3, 2), (7, 2), (9613, 1)]),
  (727, 5, [(2, 1), (3, 1), (11, 2)]),
  (97, 5, [(2, 5), (3, 1)]),
  (1553, 3, [(2, 4), (97, 1)]),
  (9032249, 3, [(2, 3), (727, 1), (1553, 1)]),
  (17, 3, [(2, 4)]),
  (137, 3, [(2, 3), (17, 1)]),
  (409, 21, [(2, 3), (3, 1), (17, 1)]),
  (9189413, 2, [(2, 2), (41, 1), (137, 1), (409, 1)]),
  (401, 3, [(2, 4), (5, 2)]),
  (19, 2, [(2, 1), (3, 2)]),
  (11173, 5, [(2, 2), (3, 1), (7, 2), (19, 1)]),
  (8960747, 2, [(2, 1), (401, 1), (11173, 1)]),
  (59, 2, [(2, 1), (29, 1)]),
  (113, 3, [(2, 4), (7, 1)]),
  (26669, 2, [(2, 2), (59, 1), (113, 1)]),
  (2240197, 5, [(2, 2), (3, 1), (7, 1), (26669, 1)]),
  (8960789, 2, [(2, 2), (2240197, 1)]),
  (61, 2, [(2, 2), (3, 1), (5, 1)]),
  (31, 3, [(2, 1), (3, 1), (5, 1)]),
  (4217, 3, [(2, 3), (17, 1), (31, 1)]),
  (25303, 3, [(2, 1), (3, 1), (4217, 1)]),
  (9260899, 2, [(2, 1), (3, 1), (61, 1), (25303, 1)]),
  (151, 6, [(2, 1), (3, 1), (5, 2)]),
  (3323, 2, [(2, 1), (11, 1), (151, 1)]),
  (8653093, 5, [(2, 2), (3, 1), (7, 1), (31, 1), (3323, 1)]),
  (23, 5, [(2, 1), (11, 1)]),
  (1373, 2, [(2, 2), (7, 3)]),
  (126317, 2, [(2, 2), (23, 1), (1373, 1)]),
  (757903, 3, [(2, 1), (3, 1), (126317, 1)]),
  (9094837, 2, [(2, 2), (3, 1), (757903, 1)]),
  (131, 2, [(2, 1), (5, 1), (13, 1)]),
  (8067767, 5, [(2, 1), (7, 1), (53, 1), (83, 1), (131, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9247639, 220288), (9248009, 0), (9252041, 773376), (9252535, 220288), (9254179, 64768), (9258601, 297856), (9258643, 297856), (9260897, 0), (9261731, 608640), (9264179, 169344), (9264181, 1196416)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9244227 + 2 * t ∧ (9244227 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9244227) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3180000
