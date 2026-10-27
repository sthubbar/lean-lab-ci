import LeanLab.GoldbachAverage.PrefixBounds124
import LeanLab.GoldbachAverage.I2Bound124

/-!
The convergent geometric variance tails in P0051 page 11 before eq. 56.
AI wrote this Lean code. Goldbach is open.
-/

set_option maxHeartbeats 800000

noncomputable section
namespace LeanLab.GoldbachAverage.VarianceTails124
open MeasureTheory Set Filter
open FloorVariance82 PrefixBounds124 GeometricTail124 I2Bound124 WeightedMass124

/-- Linear growth gives genuine convergent geometric square prefixes.
Source context: P0051 page 11 before eq. 56. -/
theorem square_prefix_series {F : ℝ → ℝ} (hF : Measurable F)
    {N K h : ℝ} (hN : 0 < N) (hK : 0 ≤ K) (hh : 0 ≤ h)
    (hb : ∀ t : ℝ, 0 ≤ t → |F t| ≤ K * (t + h + 1)) :
    (∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun t => F t ^ 2) volume 0 T) ∧
      Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) *
        ∫ t in (0 : ℝ)..(((j : ℝ) + 1) * N), F t ^ 2) := by
  have hp (T : ℝ) (hT : 0 ≤ T) :=
    bounded_square_prefix hF hT hK hh (fun t ht _ => hb t ht)
  refine ⟨fun T hT => (hp T hT).1, ?_⟩
  exact geometric_cubic_summable (fun T => ∫ t in (0 : ℝ)..T, F t ^ 2) hN hh (sq_nonneg K)
    (fun T hT => (hp T hT).2.1) (fun T hT => (hp T hT).2.2)

/-- LEAF. The R square exponential mass is bounded by a convergent geometric prefix sum.
Source: P0051 page 11, the display before eq. 56. -/
theorem rMass_prefix_bound (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) *
      ∫ t in (0 : ℝ)..(((j : ℝ) + 1) * N), psiFloorError t ^ 2) ∧
    rMass N ≤ 2 * ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) *
      ∫ t in (0 : ℝ)..(((j : ℝ) + 1) * N), psiFloorError t ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp := square_prefix_series measurable_psiFloorError hN0
    (by norm_num : (0 : ℝ) ≤ 8) (le_refl (0 : ℝ))
    (fun t ht => by simpa using R_linear_bound ht)
  refine ⟨hp.2, ?_⟩
  exact exponential_integral_le_prefix_series hN0 _ (fun _ => sq_nonneg _)
    (fun j => hp.1 _ (by positivity)) (weighted_R_square_integrable N hN) hp.2

/-- LEAF. The R increment square mass is bounded by a convergent geometric prefix sum.
Source: P0051 page 11, the display before eq. 56. -/
theorem deltaMass_prefix_bound (N : ℕ) (hN : 1 ≤ N) {h : ℝ} (hh : 0 ≤ h) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) *
      ∫ t in (0 : ℝ)..(((j : ℝ) + 1) * N),
        (psiFloorError (t + h) - psiFloorError t) ^ 2) ∧
    deltaMass N h ≤ 2 * ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) *
      ∫ t in (0 : ℝ)..(((j : ℝ) + 1) * N),
        (psiFloorError (t + h) - psiFloorError t) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : Measurable (fun t : ℝ => psiFloorError (t + h) - psiFloorError t) :=
    (measurable_psiFloorError.comp (measurable_id.add_const h)).sub measurable_psiFloorError
  have hp := square_prefix_series hm hN0 (by norm_num : (0 : ℝ) ≤ 16) hh
    (fun t ht => R_increment_linear ht hh)
  refine ⟨hp.2, ?_⟩
  exact exponential_integral_le_prefix_series hN0 _ (fun _ => sq_nonneg _)
    (fun j => hp.1 _ (by positivity)) (weighted_delta_integrable N hN hh) hp.2

/-- The H variance series in eq. 56 converges without RH.
Source: P0051 page 11 eq. 56 and page 3 eq. 15. -/
theorem H_series_summable {N : ℝ} (hN : 0 < N) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) * InghamTheta.H (((j : ℝ) + 1) * N)) := by
  have hm : Measurable (fun t : ℝ => Chebyshev.psi t - t) :=
    Chebyshev.psi_mono.measurable.sub measurable_id
  exact (square_prefix_series hm hN (by norm_num : (0 : ℝ) ≤ 8)
    (le_refl (0 : ℝ)) (fun t ht => by simpa using psi_error_linear ht)).2

/-- The J variance series in eq. 56 converges without RH.
Source: P0051 page 11 eq. 56 and page 3 eq. 15. -/
theorem J_series_summable {N h : ℝ} (hN : 0 < N) (hh : 0 ≤ h) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) * GSInputs.J (((j : ℝ) + 1) * N) h) := by
  have hm : Measurable (fun t : ℝ => Chebyshev.psi (t + h) - Chebyshev.psi t - h) :=
    ((Chebyshev.psi_mono.measurable.comp (measurable_id.add_const h)).sub
      Chebyshev.psi_mono.measurable).sub_const h
  exact (square_prefix_series hm hN (by norm_num : (0 : ℝ) ≤ 8) hh
    (fun t ht => psi_short_error_linear ht hh)).2

end LeanLab.GoldbachAverage.VarianceTails124
