/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3090000 through 3099999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3090000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [8833536, 8873984, 8713856, 8697216, 7218048, 2743040, 6589824, 8710016, 3434880, 5714048, 6584064, 7107584, 5496960, 6283520, 2857344, 2804096, 2577408, 2590208, 6475136, 7564800, 3837824, 3093888, 3181056, 7341824, 4039808, 3309696, 2664960, 3191936, 4106880, 4164608, 2889216, 2458496, 5410304, 3287424, 2429568, 7011584, 2426624, 3782784, 2387456, 7148160, 3039488, 2824704, 3840128, 3680768, 3513600, 2781056, 4562688, 3526656, 4952576, 3643008, 2393216, 2351616, 2259968, 189696, 0, 290688, 393984, 1251200, 828800]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9137691, 9141159, 9141873, 9142269, 9147529, 9153693, 9154399]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (5, 2, [(2, 2)]),
  (61, 2, [(2, 2), (3, 1), (5, 1)]),
  (19, 2, [(2, 1), (3, 2)]),
  (191, 19, [(2, 1), (5, 1), (19, 1)]),
  (372833, 3, [(2, 5), (61, 1), (191, 1)]),
  (2236999, 7, [(2, 1), (3, 1), (372833, 1)]),
  (8947997, 2, [(2, 2), (2236999, 1)]),
  (7, 3, [(2, 1), (3, 1)]),
  (17, 3, [(2, 4)]),
  (5441, 3, [(2, 6), (5, 1), (17, 1)]),
  (32647, 3, [(2, 1), (3, 1), (5441, 1)]),
  (9141161, 3, [(2, 3), (5, 1), (7, 1), (32647, 1)]),
  (11, 2, [(2, 1), (5, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (10847, 5, [(2, 1), (11, 1), (17, 1), (29, 1)]),
  (260329, 7, [(2, 3), (3, 1), (10847, 1)]),
  (8851187, 2, [(2, 1), (17, 1), (260329, 1)]),
  (13, 2, [(2, 2), (3, 1)]),
  (53, 2, [(2, 2), (13, 1)]),
  (131, 2, [(2, 1), (5, 1), (13, 1)]),
  (82531, 3, [(2, 1), (3, 2), (5, 1), (7, 1), (131, 1)]),
  (8748287, 5, [(2, 1), (53, 1), (82531, 1)]),
  (397, 5, [(2, 2), (3, 2), (11, 1)]),
  (7896331, 2, [(2, 1), (3, 2), (5, 1), (13, 1), (17, 1), (397, 1)]),
  (89, 3, [(2, 3), (11, 1)]),
  (179, 2, [(2, 1), (89, 1)]),
  (31, 3, [(2, 1), (3, 1), (5, 1)]),
  (1303, 6, [(2, 1), (3, 1), (7, 1), (31, 1)]),
  (8863007, 5, [(2, 1), (19, 1), (179, 1), (1303, 1)]),
  (3469, 2, [(2, 2), (3, 1), (17, 2)]),
  (8325601, 13, [(2, 5), (3, 1), (5, 2), (3469, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9137691, 189696), (9141159, 0), (9141873, 290688), (9142269, 393984), (9147529, 1251200), (9153693, 290688), (9154399, 828800)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9134627 + 2 * t ∧ (9134627 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9134627) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3090000
