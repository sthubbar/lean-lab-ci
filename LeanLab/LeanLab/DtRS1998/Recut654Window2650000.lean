/-
AI wrote this Lean code for CODEX task654b.
P0037 Sections 4.2 and 5.2, pages 210 and 212.
Companion differences for j from 2650000 through 2659999.
Missing bitmap indices have explicit one-bit prime checks.
No large candidate primality is asserted. Goldbach is open.
-/
import LeanLab.DtRS1998.Recut654Exceptions

namespace LeanLab.DtRS1998.Recut654Window2650000

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

/-- Candidate displacements for this 10000-offset window. -/
def shifts : List ℕ := [7170816, 6617600, 6435584, 6195840, 1993472, 3132672, 6824064, 6081152, 3712896, 2349056, 6190080, 6947840, 1122432, 5320064, 1723776, 5889536, 2363904, 1783040, 2787072, 1829504, 3388800, 6713600, 4168704, 2064512, 3286784, 3119616, 1462016, 2463360, 1803392, 949632, 6754176, 3770624, 899456, 2430720, 4558592, 2915712, 1463424, 3446144, 2797952, 2495232, 2270976, 2075904, 1162880, 2035584, 1225856, 5102976, 3443840, 1218560, 3645824, 3047424, 2435840, 2358272, 1957632, 0]

/-- The missing bit indices certified individually below. -/
def missing : List ℕ := [7871577]

/-- LEAF: Prime companion differences for all 10000 offsets in this window. -/
theorem small_differences :
    ∀ t : ℕ, t < 10000 →
      ∃ s ∈ shifts, s ≤ 7860643 + 2 * t ∧ (7860643 + 2 * t - s).Prime := by
  apply Recut654Exceptions.prime_differences_of_bitmap_patches
    (A := 7860643) (count := 10000) (lo := 2) (W := 7000000) shifts missing
    (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide)
  · intro k hk
    simp only [missing, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl
    · refine ⟨0, by decide, by decide, ?_⟩
      change Nat.Prime 7871579
      exact Recut654Exceptions.prime_of_bit 7871579 (by decide)
        (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)
  · decide +kernel

end LeanLab.DtRS1998.Recut654Window2650000
