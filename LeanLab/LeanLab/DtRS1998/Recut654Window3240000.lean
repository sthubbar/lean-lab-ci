/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3240000 through 3249999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3240000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [9259392, 8578688, 8738816, 8698368, 6694400, 2689536, 6148352, 4427520, 8574848, 3378432, 3904640, 6454656, 8562048, 6972416, 7082880, 2607872, 2592128, 5361792, 2967168, 3704960, 5275136, 2529792, 2617088, 7429632, 6876416, 2754048, 5578880, 6339968, 3391488, 3507840, 2455040, 2668928, 2442240, 3045888, 3056768, 7012992, 3152256, 2330240, 4029440, 2622720, 4817408, 3174528, 6448896, 3702656, 3647616, 3306240, 2904320, 7206656, 3971712, 3299712, 2838528, 2645888, 2334720, 233088, 693632, 0, 708608, 814976, 804608]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9301725, 9302539, 9302983, 9308139, 9309769, 9313231, 9315121, 9317161, 9317881, 9318103]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (5, 2, [(2, 2)]),
  (11, 2, [(2, 1), (5, 1)]),
  (23, 5, [(2, 1), (11, 1)]),
  (139, 2, [(2, 1), (3, 1), (23, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (233, 3, [(2, 3), (29, 1)]),
  (32621, 3, [(2, 2), (5, 1), (7, 1), (233, 1)]),
  (9068639, 13, [(2, 1), (139, 1), (32621, 1)]),
  (8608909, 2, [(2, 2), (3, 1), (7, 2), (11, 4)]),
  (13, 2, [(2, 2), (3, 1)]),
  (73, 5, [(2, 3), (3, 2)]),
  (358723, 2, [(2, 1), (3, 3), (7, 1), (13, 1), (73, 1)]),
  (8609353, 5, [(2, 3), (3, 1), (358723, 1)]),
  (97, 5, [(2, 5), (3, 1)]),
  (109, 6, [(2, 2), (3, 3)]),
  (2399, 11, [(2, 1), (11, 1), (109, 1)]),
  (465407, 5, [(2, 1), (97, 1), (2399, 1)]),
  (9308141, 2, [(2, 2), (5, 1), (465407, 1)]),
  (181, 2, [(2, 2), (3, 2), (5, 1)]),
  (238921, 23, [(2, 3), (3, 1), (5, 1), (11, 1), (181, 1)]),
  (1433527, 5, [(2, 1), (3, 1), (238921, 1)]),
  (8601163, 5, [(2, 1), (3, 1), (1433527, 1)]),
  (163, 2, [(2, 1), (3, 4)]),
  (653, 2, [(2, 2), (163, 1)]),
  (8619601, 17, [(2, 4), (3, 1), (5, 2), (11, 1), (653, 1)]),
  (211, 2, [(2, 1), (3, 1), (5, 1), (7, 1)]),
  (113, 3, [(2, 4), (7, 1)]),
  (227, 2, [(2, 1), (113, 1)]),
  (287383, 5, [(2, 1), (3, 1), (211, 1), (227, 1)]),
  (8621491, 3, [(2, 1), (3, 1), (5, 1), (287383, 1)]),
  (17, 3, [(2, 4)]),
  (239, 7, [(2, 1), (7, 1), (17, 1)]),
  (8502187, 2, [(2, 1), (3, 1), (7, 2), (11, 2), (239, 1)]),
  (479, 13, [(2, 1), (239, 1)]),
  (3833, 3, [(2, 3), (479, 1)]),
  (8624251, 10, [(2, 1), (3, 2), (5, 3), (3833, 1)]),
  (53, 2, [(2, 2), (13, 1)]),
  (8513497, 7, [(2, 3), (3, 2), (23, 1), (53, 1), (97, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9301725, 233088), (9302539, 693632), (9302983, 693632), (9308139, 0), (9309769, 708608), (9313231, 693632), (9315121, 693632), (9317161, 814976), (9317881, 693632), (9318103, 804608)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9299459 + 2 * t ∧ (9299459 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9299459) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3240000
