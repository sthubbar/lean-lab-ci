/-
Burst 20261122, unit P1122-0106, wiring. P0069 Baker Harman Pintz 1997, page 53 and the end of
Section 5. The assembly `upper_short_weight_of_slack_leaf` of UpperShortC165Leaves runs through the
slack LEAF `upper_normalized_raw_conditions_slack`, whose main split in
SPLIT_upper_normalized_raw_conditions_slack carries the leaf `upper_slack_split_slack_distribution`,
refuted in Refute1122SlackDistribution. UpperShortC165Leaves cannot import the route, which imports
it, so this new file states `upper_short_weight_of_slack_leaf` verbatim under a new name and proves
it through `upslack_route` of Prep1121UpslackRoute, the split that builds lam = (v1 + delta) / D
from the local density D of the raw weight. The proof is the original one with that single input
swapped. New file, no new definition, no sorry of its own.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.UpperShortC165Leaves
import LeanLab.BHP1997.Prep1121UpslackRoute

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- P0069, page 53 and the end of Section 5: the statement of `upper_short_weight_of_slack_leaf`,
verbatim, routed through `upslack_route` instead of the slack LEAF and its main split. The density is
v1 = the paper value + delta with delta half the margin below 2.2, as in the original. PROVED modulo
the leaves of `upslack_route` and the inputs h4, h9. -/
theorem upper_short_weight_of_upslack_route
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v1 : ℝ) (b1 : ℝ → ℕ → ℝ),
        v1 < 2.2 ∧ RightConditions ε B v1 b1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x, primeWeight m ≤ b1 x m := by
  obtain ⟨ω, hω, hz⟩ := Task308.buchstab_model_exists
  obtain ⟨B0, η, hη, hrange⟩ := upper_thresholds
  refine ⟨B0, η, hη, fun B ε hB hε hεη => ?_⟩
  obtain ⟨hB0, hε0, hε8⟩ := hrange B ε hB hε hεη
  set P := ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
    upperDeletedIntegral ω ε with hP
  have hP22 : P < 2.2 := upper_density_bound hω hz hε0.le hε8 le_rfl
  have hδ : 0 < (2.2 - P) / 2 := by linarith
  obtain ⟨lam, Λ, hlam, ⟨X, hX⟩, hdist, hms⟩ :=
    upslack_route h4 h9 hω hz hε0 hε8 hδ
  refine ⟨P + (2.2 - P) / 2, upperNormCoeff ε lam, by linarith,
    Task308.right_conditions_of_parts (upper_norm_coeff_divisor_bound hB0 hε0 hε8 hlam)
      hdist hms, max X 4, fun x hx m hm => ?_⟩
  exact upper_prime_le_norm_coeff hε0 (le_of_max_le_right hx) hm
    (hX x (le_of_max_le_left hx) m hm)

end LeanLab.BHP1997.DecompC165d
