/-
AI wrote this Lean code for CODEX task58.
A uniform endpoint choice for P0039 equations 3.1, 3.2 and 3.11.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58Endpoint
import LeanLab.ExceptionalSet.GrimmeltTeravainen2025Params

open Real Filter

namespace LeanLab.ChenPrimeExceptional.Task58

open U1433 U1424 LeanLab.ExceptionalSet.GT2025

noncomputable section

/-- The cubic size conditions used in the two S counts hold for all sufficiently large N. -/
theorem eventually_cubic_sizes {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      4 * ((N : ℝ) ^ ((1 : ℝ) / 3 - δ)) ^ 3 ≤ N ∧
      8 * ((N : ℝ) ^ ((1 : ℝ) / 3 - δ)) ^ 3 < N := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (3 * δ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 3 * δ)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_gt_atTop 8, eventually_ge_atTop (2 : ℕ)] with N h8 hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact ⟨four_cube_le hNp (by linarith), cube_lt hNp h8⟩

/-- One delta satisfies the paper's parameter hierarchy and all endpoint conditions. -/
theorem exists_admissible_delta {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ StrictHierarchy δ ∧
      ∀ N : ℕ, 1 < N → EndpointNotPrime ((N : ℝ) ^ ((1 : ℝ) / 3 - δ)) := by
  obtain ⟨δ, hδ, hδε, hE⟩ := exists_uniform_delta_endpoint
    (show 0 < min ε (1 / 200) from lt_min hε (by norm_num))
  refine ⟨δ, hδ, hδε.trans_le (min_le_left _ _), ?_, hE⟩
  exact (strictHierarchy_iff hδ).2 (hδε.trans_le (min_le_right _ _))

/-- For one arbitrarily small fixed delta, the paper's B1 and B2 S values hold for all
sufficiently large natural N in their stated n range, with no endpoint hypothesis. -/
theorem exists_delta_eventual_S {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ StrictHierarchy δ ∧
      ∀ᶠ N : ℕ in atTop, ∀ lo : ℝ, ∀ n : ℕ, (N : ℝ) ≤ 2 * (n : ℝ) →
        (InB1 lo ((N : ℝ) ^ ((1 : ℝ) / 3 - δ)) N n →
          Scount lo ((N : ℝ) ^ ((1 : ℝ) / 3 - δ)) n = 1) ∧
        (InB2 lo ((N : ℝ) ^ ((1 : ℝ) / 3 - δ)) N n →
          Scount lo ((N : ℝ) ^ ((1 : ℝ) / 3 - δ)) n = 0) := by
  obtain ⟨δ, hδ, hδε, hh, hE⟩ := exists_admissible_delta hε
  refine ⟨δ, hδ, hδε, hh, ?_⟩
  filter_upwards [eventually_cubic_sizes hδ, eventually_ge_atTop (2 : ℕ)] with N hs hN
  intro lo n hn
  exact ⟨fun hB => S_eq_one_B1 hB hn hs.1 (hE N (by omega)),
    fun hB => S_eq_zero_B2 hB hn hs.2 (hE N (by omega))⟩

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.eventually_cubic_sizes
#print axioms LeanLab.ChenPrimeExceptional.Task58.exists_admissible_delta
#print axioms LeanLab.ChenPrimeExceptional.Task58.exists_delta_eventual_S
