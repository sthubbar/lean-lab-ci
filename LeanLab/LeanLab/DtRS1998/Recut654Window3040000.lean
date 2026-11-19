/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3040000 through 3049999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3040000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8932224, 8891776, 8772096, 8755456, 6341760, 3571840, 6648064, 8768256, 7276288, 6887808, 5555200, 2523648, 4620928, 2801280, 3584896, 2810496, 2528128, 4222848, 3898368, 2915584, 7206400, 7165824, 3250176, 2487808, 7400064, 2409856, 5468544, 3031936, 2235264, 7623040, 6642304, 6533376, 2648448, 7069824, 2188288, 3493120, 2451456, 3701248, 2882944, 3896064, 2318208, 3367936, 2785536, 3239296, 3160576, 2281728, 4098048, 2516736, 5772288, 4165120, 3152128, 2947456, 2723200, 2255616, 0, 247936]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9102089, 9110167]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (5, 2, [(2, 2)]),
  (7, 3, [(2, 1), (3, 1)]),
  (127, 3, [(2, 1), (3, 2), (7, 1)]),
  (11, 2, [(2, 1), (5, 1)]),
  (199, 3, [(2, 1), (3, 2), (11, 1)]),
  (2389, 2, [(2, 2), (3, 1), (199, 1)]),
  (9102091, 2, [(2, 1), (3, 1), (5, 1), (127, 1), (2389, 1)]),
  (41, 6, [(2, 3), (5, 1)]),
  (23, 5, [(2, 1), (11, 1)]),
  (47, 5, [(2, 1), (23, 1)]),
  (659, 2, [(2, 1), (7, 1), (47, 1)]),
  (8862233, 3, [(2, 3), (41, 2), (659, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9102089, 0), (9110167, 247936)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9092867 + 2 * t ∧ (9092867 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9092867) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3040000
