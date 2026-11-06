import LeanLab.ChenDoubleSieve.Decomp367c
import LeanLab.ChenDoubleSieve.Decomp367d

/-!
Elementary preparation for the F4 prime sum in Wu 2004 equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, page 39.
The general single prime mass and uniform level shift bounds are reused.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task366
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The unrestricted F4 reciprocal pair mass has a constant bound on the tail. -/
theorem fullPairs4_mass_bounded : ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N → pairMass (fullPairs4 N) ≤ K := by
  obtain ⟨K, hK, M, hM⟩ := Task367.lowerPrimeBand_mass_bounded
  refine ⟨K ^ 2, sq_pos_of_pos hK, M, ?_⟩
  intro N hN
  calc
    _ ≤ pairMass (lowerPrimeBand N ×ˢ lowerPrimeBand N) :=
      pairMass_mono (fullPairs4_subset N)
    _ = (∑ p ∈ lowerPrimeBand N, 1 / (p : ℝ)) *
        (∑ p ∈ lowerPrimeBand N, 1 / (p : ℝ)) := pairMass_product _ _
    _ ≤ K * K := mul_le_mul (hM N hN) (hM N hN)
      (sum_nonneg (by intros; positivity)) hK.le
    _ = K ^ 2 := by ring

/-- The reciprocal F4 sum is unchanged in the limit by removing the logarithmic loss.
CONDITIONAL ON IsLinearSieve only. No two dimensional integral limit is used. -/
theorem reciprocalFullSum4_shift_small (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      |reciprocalFullSum4 f B N - reciprocalFullSum4 f 0 N| ≤ ε := by
  obtain ⟨K, hK, M, hM⟩ := fullPairs4_mass_bounded
  obtain ⟨J, hJ⟩ := Task367.lower_values_shift_small F f h B hB (ε / K) (by positivity)
  refine ⟨max 2 (max M J), ?_⟩
  intro N hN
  have he : reciprocalFullSum4 f B N - reciprocalFullSum4 f 0 N =
      ∑ p ∈ fullPairs4 N,
        (f (lowerLevel B N (p.1 * p.2)) - f (lowerLevel 0 N (p.1 * p.2))) /
          ((p.1 : ℝ) * p.2) := by
    simp only [reciprocalFullSum4, ← sum_sub_distrib, sub_div]
  rw [he]
  calc
    _ ≤ ∑ p ∈ fullPairs4 N,
        |(f (lowerLevel B N (p.1 * p.2)) - f (lowerLevel 0 N (p.1 * p.2))) /
          ((p.1 : ℝ) * p.2)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ fullPairs4 N, (ε / K) * (1 / ((p.1 : ℝ) * p.2)) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hd, hb⟩ := fullPairs4_product (by omega) hp
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p.1 : ℝ) * p.2)]
      simpa only [div_eq_mul_inv, one_mul] using
        div_le_div_of_nonneg_right (hJ N (by omega) _ hd hb)
          (by positivity : (0 : ℝ) ≤ (p.1 : ℝ) * p.2)
    _ = (ε / K) * pairMass (fullPairs4 N) := by simp only [pairMass, mul_sum]
    _ ≤ (ε / K) * K := mul_le_mul_of_nonneg_left (hM N (by omega)) (by positivity)
    _ = ε := by field_simp

/-- The actual F4 limit is reduced to the zero loss reciprocal sum limit.
CONDITIONAL ON IsLinearSieve and the explicit zero loss integral limit. -/
theorem lowerSum4_of_zero_loss (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B)
    (hzero : Tendsto (reciprocalFullSum4 f 0) evenAtTop (𝓝 (lowerIntegral4 f))) :
    Tendsto (lowerSum4 f B) evenAtTop (𝓝 (lowerIntegral4 f)) := by
  apply lowerSum4_of_reciprocal F f h B hB
  have hd : Tendsto (fun N => dist (reciprocalFullSum4 f 0 N)
      (reciprocalFullSum4 f B N)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨K, hK⟩ := reciprocalFullSum4_shift_small F f h B hB (ε / 2) (by positivity)
    refine ⟨K, ?_⟩
    intro N hN
    simpa only [Real.dist_eq, sub_zero, abs_abs, abs_sub_comm] using
      (hK N hN).trans_lt (by linarith : ε / 2 < ε)
  exact hzero.congr_dist (tendsto_inf_left hd)

end LeanLab.ChenDoubleSieve.Task366
