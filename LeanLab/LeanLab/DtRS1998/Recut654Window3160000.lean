/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 3160000 through 3169999.
Missing bitmap indices have explicit Pocklington witnesses.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions
import LeanLab.DtRS1998.Recut654PatchCertificates

namespace LeanLab.DtRS1998.Recut654Window3160000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [9240704, 9063936, 9200256, 9080576, 7584768, 3109760, 6950784, 2956928, 3801600, 9076736, 7196288, 3191424, 5863680, 6650240, 3460608, 7378304, 4406528, 4149504, 4204544, 7931520, 6841856, 2836608, 7708544, 3893376, 2754176, 4929408, 3118976, 3880320, 6956544, 4206848, 3340416, 3124608, 3406208, 2832128, 4473600, 3469056, 3255936, 3196544, 4531328, 3808128, 2825216, 7514880, 6080768, 5777024, 3654144, 3031680, 3558656, 3224064, 3676416, 2793344, 2718336, 4047488, 3147776, 2796288, 1617920, 734976, 0, 2049024, 437120, 501888]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [9642349, 9654321, 9655011, 9657279, 9657991, 9659169]

/-- Pocklington certificates for the missing companion primes and their factors. -/
def patchCertificates : List Big.Cert := [
  (2, 1, []),
  (3, 2, [(2, 1)]),
  (5, 2, [(2, 2)]),
  (7, 3, [(2, 1), (3, 1)]),
  (13, 2, [(2, 2), (3, 1)]),
  (53, 2, [(2, 2), (13, 1)]),
  (743, 5, [(2, 1), (7, 1), (53, 1)]),
  (267481, 13, [(2, 3), (3, 2), (5, 1), (743, 1)]),
  (8024431, 6, [(2, 1), (3, 1), (5, 1), (267481, 1)]),
  (41, 6, [(2, 3), (5, 1)]),
  (83, 2, [(2, 1), (41, 1)]),
  (11, 2, [(2, 1), (5, 1)]),
  (199, 3, [(2, 1), (3, 2), (11, 1)]),
  (53731, 12, [(2, 1), (3, 3), (5, 1), (199, 1)]),
  (8919347, 2, [(2, 1), (83, 1), (53731, 1)]),
  (31, 3, [(2, 1), (3, 1), (5, 1)]),
  (19, 2, [(2, 1), (3, 2)]),
  (683, 5, [(2, 1), (11, 1), (31, 1)]),
  (77863, 5, [(2, 1), (3, 1), (19, 1), (683, 1)]),
  (9655013, 2, [(2, 2), (31, 1), (77863, 1)]),
  (29, 2, [(2, 2), (7, 1)]),
  (59, 2, [(2, 1), (29, 1)]),
  (2243, 2, [(2, 1), (19, 1), (59, 1)]),
  (7608257, 3, [(2, 6), (53, 1), (2243, 1)]),
  (211, 2, [(2, 1), (3, 1), (5, 1), (7, 1)]),
  (2111, 7, [(2, 1), (5, 1), (211, 1)]),
  (384203, 2, [(2, 1), (7, 1), (13, 1), (2111, 1)]),
  (9220873, 35, [(2, 3), (3, 1), (384203, 1)]),
  (89, 3, [(2, 3), (11, 1)]),
  (179, 2, [(2, 1), (89, 1)]),
  (25579, 2, [(2, 1), (3, 2), (7, 2), (29, 1)]),
  (9157283, 2, [(2, 1), (179, 1), (25579, 1)])]

/-- Each exceptional companion certificate has a prime first entry. -/
theorem patchCertificates_prime : ∀ c ∈ patchCertificates, c.1.Prime := by
  exact Big.chainP_sound patchCertificates [] (by simp) (by decide +kernel)

/-- Missing bit indices paired with their selected candidate displacement. -/
def patchPairs : List (ℕ × ℕ) := [(9642349, 1617920), (9654321, 734976), (9655011, 0), (9657279, 2049024), (9657991, 437120), (9659169, 501888)]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 9641347 + 2 * t ∧ (9641347 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 9641347) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · exact Recut654PatchCertificates.prime_patches_of_chain 2 shifts missing
      patchCertificates patchPairs patchCertificates_prime (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window3160000
