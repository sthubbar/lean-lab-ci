import LeanLab.ExceptionalSet.SPLIT_leaf_poisson_index
import LeanLab.ExceptionalSet.SPLIT_leaf_poisson_endpoint
import LeanLab.ExceptionalSet.Decomp404b

/-!
P0082 page 356, elementary inputs for the two adjacent Fourier frequencies.
Exact clean companions preserve all original split files and their sealed statements.
Source: https://doi.org/10.5802/aif.1621
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp464b

open Real MeasureTheory Filter
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck)

/-- P0082 page 356, continuity at the boundary frequencies in the Poisson display.
Exact clean companion for the open endpoint leaf. -/
theorem leaf_ftR_continuous (K : ℝ → ℂ) (hK : Integrable K) : Continuous (ftR K) := by
  have hct : Continuous (FourierTransform.fourier K) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (L := innerₗ ℝ) continuous_inner hK
  have he : ftR K = FourierTransform.fourier K :=
    funext (Decomp404b.ftR_eq_fourier K)
  rw [he]
  exact hct

/-- P0082 page 356, continuity at the boundary frequencies in the Poisson display.
Exact clean companion for the open endpoint leaf. -/
theorem leaf_rescale_tendsto (ξ : ℝ) :
    Filter.Tendsto (fun n : ℕ => ξ * (1 + (1 : ℝ) / ((n : ℝ) + 1))) Filter.atTop (nhds ξ) := by
  simpa only [add_zero, mul_one] using
    (tendsto_const_nhds (x := ξ)).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

/-- P0082 page 356, continuity at the boundary frequencies in the Poisson display.
Exact clean companion for the open endpoint leaf. -/
theorem leaf_rescale_abs_gt_one (ξ : ℝ) (hξ : 1 ≤ |ξ|) (n : ℕ) :
    1 < |ξ * (1 + (1 : ℝ) / ((n : ℝ) + 1))| := by
  have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  rw [abs_mul, abs_of_pos (by linarith : 0 < 1 + (1 : ℝ) / ((n : ℝ) + 1))]
  nlinarith

/-- P0082 page 356, continuity at the boundary frequencies in the Poisson display.
Exact clean companion for the open endpoint leaf. -/
theorem leaf_eq_zero_of_tendsto {f : ℝ → ℂ} {u : ℕ → ℝ} {ξ : ℝ}
    (hf : Continuous f) (hu : Filter.Tendsto u Filter.atTop (nhds ξ)) (h0 : ∀ n : ℕ, f (u n) = 0) :
    f ξ = 0 := by
  have hlim : Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop (nhds (f ξ)) := by
    simpa only [Function.comp_def, h0] using (hf.continuousAt.tendsto.comp hu)
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- P0082 page 356, exact original split statement from the completed companions. -/
theorem leaf_poisson_endpoint_split (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    ∀ ξ : ℝ, 1 ≤ |ξ| → ftR K ξ = 0 := by
  intro ξ hξ
  refine leaf_eq_zero_of_tendsto (f := ftR K) (u := fun n : ℕ => ξ * (1 + (1 : ℝ) / ((n : ℝ) + 1)))
    (leaf_ftR_continuous K hK) (leaf_rescale_tendsto ξ) ?_
  intro n
  exact hsupp _ (leaf_rescale_abs_gt_one ξ hξ n)

end LeanLab.ExceptionalSet.Decomp464b
