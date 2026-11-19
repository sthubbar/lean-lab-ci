/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3120000 through 3129999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3120000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8738816, 8698368, 8578688, 3378432, 6454656, 8574848, 2958720, 6148352, 8562048, 2330240, 6448896, 3904640, 5361792, 5275136, 7082880, 3056768, 2216448, 3702656, 4427520, 7206656, 6339968, 3971712, 3704960, 3152256, 3545600, 7429632, 3507840, 6972416, 2622720, 6876416, 2904320, 3299712, 2838528, 2323328, 3045888, 2694656, 2442240, 3391488, 2617088, 2689536, 2607872, 2592128, 6694400, 4817408, 5578880, 3174528, 2967168, 2668928, 2645888, 2088320, 7012992, 2722176, 2529792, 2455040, 2258048, 0, 804608, 708608, 1158272, 155520, 1547136, 693632, 186240]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9062349, 9062983, 9065713, 9065953, 9066043, 9067815, 9073695, 9073923, 9075511, 9076089]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (5, 2, [(2, 2)]),
  (11, 2, [(2, 1), (5, 1)]),
  (3, 2, [(2, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (1373, 2, [(2, 2), (7, 3)]),
  (16477, 2, [(2, 2), (3, 1), (1373, 1)]),
  (9062351, 11, [(2, 1), (5, 2), (11, 1), (16477, 1)]),
  (12289, 11, [(2, 12), (3, 1)]),
  (49157, 2, [(2, 2), (12289, 1)]),
  (8258377, 5, [(2, 3), (3, 1), (7, 1), (49157, 1)]),
  (37, 2, [(2, 2), (3, 2)]),
  (223, 3, [(2, 1), (3, 1), (37, 1)]),
  (28099, 2, [(2, 1), (3, 2), (7, 1), (223, 1)]),
  (8261107, 3, [(2, 1), (3, 1), (7, 2), (28099, 1)]),
  (101, 2, [(2, 2), (5, 2)]),
  (19, 2, [(2, 1), (3, 2)]),
  (191, 19, [(2, 1), (5, 1), (19, 1)]),
  (383, 5, [(2, 1), (191, 1)]),
  (4597, 5, [(2, 2), (3, 1), (383, 1)]),
  (8357347, 2, [(2, 1), (3, 2), (101, 1), (4597, 1)]),
  (113, 3, [(2, 4), (7, 1)]),
  (227, 2, [(2, 1), (113, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (1451, 2, [(2, 1), (5, 2), (29, 1)]),
  (2903, 5, [(2, 1), (1451, 1)]),
  (7907773, 2, [(2, 2), (3, 1), (227, 1), (2903, 1)]),
  (3617, 3, [(2, 5), (113, 1)]),
  (1114037, 5, [(2, 2), (7, 1), (11, 1), (3617, 1)]),
  (8912297, 3, [(2, 3), (1114037, 1)]),
  (229, 6, [(2, 2), (3, 1), (19, 1)]),
  (1217, 3, [(2, 6), (19, 1)]),
  (8918177, 3, [(2, 5), (229, 1), (1217, 1)]),
  (17, 3, [(2, 4)]),
  (1153, 5, [(2, 7), (3, 2)]),
  (1881697, 7, [(2, 5), (3, 1), (17, 1), (1153, 1)]),
  (7526789, 2, [(2, 2), (1881697, 1)]),
  (13, 2, [(2, 2), (3, 1)]),
  (199, 3, [(2, 1), (3, 2), (11, 1)]),
  (8381881, 11, [(2, 3), (3, 4), (5, 1), (13, 1), (199, 1)]),
  (463, 3, [(2, 1), (3, 1), (7, 1), (11, 1)]),
  (44449, 13, [(2, 5), (3, 1), (463, 1)]),
  (177797, 2, [(2, 2), (44449, 1)]),
  (8889851, 2, [(2, 1), (5, 2), (177797, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9062349, 0), (9062983, 804608), (9065713, 804608), (9065953, 708608), (9066043, 1158272), (9067815, 155520), (9073695, 155520), (9073923, 1547136), (9075511, 693632), (9076089, 186240)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9059459 + 2 * t ∧ (9059459 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9059459) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3120000
