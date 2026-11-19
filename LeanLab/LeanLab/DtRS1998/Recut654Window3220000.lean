/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3220000 through 3229999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3220000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [9394560, 8713856, 8873984, 8833536, 6283520, 6589824, 8710016, 4562688, 2590208, 2824704, 5714048, 3513600, 7107584, 8697216, 3643008, 6829568, 6475136, 2469888, 2743040, 3287424, 2752256, 3102336, 7011584, 7148160, 3191936, 7341824, 2857344, 2889216, 3840128, 3680768, 7218048, 3837824, 3434880, 6584064, 4952576, 3093888, 4164608, 3039488, 4106880, 2458496, 2429568, 2426624, 7564800, 3782784, 2664960, 5496960, 5410304, 4039808, 3441408, 3309696, 3181056, 2804096, 843776, 1251200, 393984, 135168, 189696, 939776, 828800, 0]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9395881, 9398707, 9398889, 9399573, 9401937, 9404677, 9410881, 9412521]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (37, 2, [(2, 2), (3, 2)]),
  (5, 2, [(2, 2)]),
  (13, 2, [(2, 2), (3, 1)]),
  (53, 2, [(2, 2), (13, 1)]),
  (107, 2, [(2, 1), (53, 1)]),
  (12841, 21, [(2, 3), (3, 1), (5, 1), (107, 1)]),
  (8552107, 2, [(2, 1), (3, 2), (37, 1), (12841, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (433, 5, [(2, 4), (3, 3)]),
  (48497, 3, [(2, 4), (7, 1), (433, 1)]),
  (678959, 13, [(2, 1), (7, 1), (48497, 1)]),
  (8147509, 2, [(2, 2), (3, 1), (678959, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (1451, 2, [(2, 1), (5, 2), (29, 1)]),
  (9004907, 2, [(2, 1), (29, 1), (107, 1), (1451, 1)]),
  (271, 6, [(2, 1), (3, 3), (5, 1)]),
  (11, 2, [(2, 1), (5, 1)]),
  (89, 3, [(2, 3), (11, 1)]),
  (4273, 5, [(2, 4), (3, 1), (89, 1)]),
  (17093, 2, [(2, 2), (4273, 1)]),
  (9264407, 5, [(2, 1), (271, 1), (17093, 1)]),
  (23, 5, [(2, 1), (11, 1)]),
  (47, 5, [(2, 1), (23, 1)]),
  (283, 3, [(2, 1), (3, 1), (47, 1)]),
  (313, 10, [(2, 3), (3, 1), (13, 1)]),
  (354317, 2, [(2, 2), (283, 1), (313, 1)]),
  (9212243, 2, [(2, 1), (13, 1), (354317, 1)]),
  (17, 3, [(2, 4)]),
  (239, 7, [(2, 1), (7, 1), (17, 1)]),
  (113, 3, [(2, 4), (7, 1)]),
  (227, 2, [(2, 1), (113, 1)]),
  (5903, 5, [(2, 1), (13, 1), (227, 1)]),
  (8464903, 3, [(2, 1), (3, 1), (239, 1), (5903, 1)]),
  (2221, 2, [(2, 2), (3, 1), (5, 1), (37, 1)]),
  (62189, 2, [(2, 2), (7, 1), (2221, 1)]),
  (8582083, 5, [(2, 1), (3, 1), (23, 1), (62189, 1)]),
  (71, 7, [(2, 1), (5, 1), (7, 1)]),
  (1847, 5, [(2, 1), (13, 1), (71, 1)]),
  (48023, 5, [(2, 1), (13, 1), (1847, 1)]),
  (672323, 2, [(2, 1), (7, 1), (48023, 1)]),
  (9412523, 2, [(2, 1), (7, 1), (672323, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9395881, 843776), (9398707, 1251200), (9398889, 393984), (9399573, 135168), (9401937, 189696), (9404677, 939776), (9410881, 828800), (9412521, 0)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9394627 + 2 * t ∧ (9394627 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9394627) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3220000
