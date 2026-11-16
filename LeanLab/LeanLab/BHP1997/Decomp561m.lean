/-
P0069 pages 7 and 8, display 2.6 and the two following displays.
Independent split of eta extension and finite endpoint replacement.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.PrincipalData635
import LeanLab.BHP1997.SPLIT_leaf_eta_cutoff561
import LeanLab.BHP1997.SPLIT_leaf_finite_endpoint561

namespace LeanLab.BHP1997.Decomp561m
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e

/-- LEAF. P0069 page 8 first display after 2.6, eta tail truncation alone.
Extend the original eta limits to a complete period while retaining the exact
finite convolution count. The reciprocal square integral and full modulus
arithmetic envelope are proved in Decomp561h. The polynomial tail reduction
and mean square passage are still required here. OPEN. -/
theorem leaf_eta_cutoff561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ,
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          etaTailError561 ε D x u v ≤ C * scale512 ε A x := by
  exact leaf_eta_cutoff561_split

/-- LEAF. P0069 page 8 second display after 2.6, finite endpoint correction alone.
Replace the exact finite convolution count in the complete period model by Y.
The endpoint discrepancy is bounded before the singular series factor is
summed. D is fixed before choosing the threshold C. No eta cutoff remains.
The two smaller errors are not merged inside this input. OPEN. -/
theorem leaf_finite_endpoint561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ,
      ∀ A : ℝ, 0 < A → ∀ D : ℝ,
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          endpointError561 ε D x u v ≤ C * scale512 ε A x := by
  exact leaf_finite_endpoint561_split

/-- P0069 page 8 displays following 2.6, exact expanded eta extension conclusion.
CONDITIONAL ON the separate cutoff and finite endpoint inputs. -/
theorem major_eta_extension561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ,
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          etaExtensionError512 ε D x u v ≤ C * scale512 ε A x := by
  obtain ⟨ε₁, hε₁, hcut⟩ := leaf_eta_cutoff561
  obtain ⟨ε₂, hε₂, hend⟩ := leaf_finite_endpoint561
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro ε hε he u v A hA
  apply combine_eventual561 ε A
    (fun D x => etaTailError561 ε D x u v)
    (fun D x => endpointError561 ε D x u v)
    (fun D x => etaExtensionError512 ε D x u v)
  · exact hcut ε hε (lt_of_lt_of_le he (min_le_left _ _)) u v A hA
  · exact ⟨0, fun D _ => hend ε hε (lt_of_lt_of_le he (min_le_right _ _)) u v A hA D⟩
  · intro D x
    exact two_error_mean_square561 _ _ _ _

end LeanLab.BHP1997.Decomp561m
