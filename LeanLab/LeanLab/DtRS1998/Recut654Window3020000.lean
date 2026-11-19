/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3020000 through 3029999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3020000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8480000, 8439552, 8319872, 8303232, 7170816, 3645824, 6190080, 8316032, 2035584, 6617600, 5102976, 5889536, 6195840, 2071424, 2893440, 1803392, 6824064, 6713600, 4168704, 2064512, 3040896, 6435584, 2430720, 3446144, 2363904, 2349056, 6947840, 2915712, 2032640, 1658112, 1783040, 3047424, 4558592, 3712896, 2645504, 3119616, 1999232, 2196224, 3286784, 2787072, 2708352, 2183424, 5016320, 2270976, 3770624, 3388800, 3249024, 2797952, 2387072, 2699904, 2495232, 2435840, 2075904, 1676672, 652160, 0]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [8602285, 8609295]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (5, 2, [(2, 2)]),
  (97, 5, [(2, 5), (3, 1)]),
  (11, 2, [(2, 1), (5, 1)]),
  (31, 3, [(2, 1), (3, 1), (5, 1)]),
  (683, 5, [(2, 1), (11, 1), (31, 1)]),
  (1325021, 2, [(2, 2), (5, 1), (97, 1), (683, 1)]),
  (7950127, 5, [(2, 1), (3, 1), (1325021, 1)]),
  (61, 2, [(2, 2), (3, 1), (5, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (8821, 2, [(2, 2), (3, 2), (5, 1), (7, 2)]),
  (8609297, 3, [(2, 4), (61, 1), (8821, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(8602285, 652160), (8609295, 0)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 8600643 + 2 * t ∧ (8600643 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 8600643) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3020000
