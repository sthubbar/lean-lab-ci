/-
P0069 pages 7 and 8, display 2.6 and the two following displays.
Independent split of eta extension and finite endpoint replacement.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561e

namespace LeanLab.BHP1997.Decomp561m
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e

/-- P0069 page 6, the exact Ramanujan sum at frequency minus N. -/
noncomputable def ramanujan512 (q N : ℕ) : ℂ :=
  ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
    @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))

/-- P0069 page 8, the truncated singular series main term. -/
noncomputable def truncatedMain512 (ε D x u v : ℝ) (N : ℕ) : ℂ :=
  u * v * length512 ε x / (Real.log x * Real.log (length512 ε x)) *
    ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
      (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 * ramanujan512 q N

/-- P0069 page 7 display 2.6, the principal model with the original eta limits. -/
noncomputable def principalArc512 (ε D x u v : ℝ) (N : ℕ) : ℂ :=
  u * v / (Real.log x * Real.log (length512 ε x)) *
    ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
      (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 * ramanujan512 q N *
        ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
          (Real.log x ^ (4 * D) / (q * length512 ε x)),
          integrand512 ε x (fun _ => 1) (fun _ => 1) N t

/-- P0069 page 8, the combined eta extension and finite endpoint mean square. -/
noncomputable def etaExtensionError512 (ε D x u v : ℝ) : ℝ :=
  ∑ N ∈ frequencies512 ε x,
    ‖principalArc512 ε D x u v N - truncatedMain512 ε D x u v N‖ ^ 2

/-- P0069 page 8 first display after 2.6, the complete period principal model.
The integral over a period equals the exact finite convolution count. -/
noncomputable def completePrincipal561 (ε D x u v : ℝ) (N : ℕ) : ℂ :=
  u * v / (Real.log x * Real.log (length512 ε x)) *
    ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
      (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 * ramanujan512 q N *
        ∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          integrand512 ε x (fun _ => 1) (fun _ => 1) N t

/-- P0069 page 8 first display after 2.6, the eta cutoff error alone. -/
noncomputable def etaTailError561 (ε D x u v : ℝ) : ℝ :=
  ∑ N ∈ frequencies512 ε x,
    ‖principalArc512 ε D x u v N - completePrincipal561 ε D x u v N‖ ^ 2

/-- P0069 page 8 second display after 2.6, the finite convolution endpoint error alone. -/
noncomputable def endpointError561 (ε D x u v : ℝ) : ℝ :=
  ∑ N ∈ frequencies512 ε x,
    ‖completePrincipal561 ε D x u v N - truncatedMain512 ε D x u v N‖ ^ 2

/-- P0069 pages 7 and 8, the finite square triangle inequality for two distinct errors. -/
theorem two_error_mean_square561 (S : Finset ℕ) (f g h : ℕ → ℂ) :
    (∑ N ∈ S, ‖f N - h N‖ ^ 2) ≤
      2 * (∑ N ∈ S, ‖f N - g N‖ ^ 2) + 2 * (∑ N ∈ S, ‖g N - h N‖ ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro N hN
  have ht : ‖f N - h N‖ ≤ ‖f N - g N‖ + ‖g N - h N‖ := by
    simpa only [dist_eq_norm] using dist_triangle (f N) (g N) (h N)
  have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
  nlinarith [sq_nonneg (‖f N - g N‖ - ‖g N - h N‖)]

/-- P0069 pages 7 and 8, combine two eventual error bounds at common parameters.
This is threshold bookkeeping and has no analytic premise beyond the two bounds. -/
theorem combine_eventual561 (ε A : ℝ) (F G H : ℝ → ℝ → ℝ)
    (hF : ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      F D x ≤ C * scale512 ε A x)
    (hG : ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      G D x ≤ C * scale512 ε A x)
    (hH : ∀ D x, H D x ≤ 2 * F D x + 2 * G D x) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      H D x ≤ C * scale512 ε A x := by
  obtain ⟨D₁, hD₁⟩ := hF
  obtain ⟨D₂, hD₂⟩ := hG
  refine ⟨max D₁ D₂, fun D hD => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hD₁ D ((le_max_left _ _).trans hD)
  obtain ⟨C₂, hC₂⟩ := hD₂ D ((le_max_right _ _).trans hD)
  let C := max (max C₁ C₂) (max (2 * C₁ + 2 * C₂) 1)
  refine ⟨C, fun x hx => ?_⟩
  have hx₁ : C₁ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx₂ : C₂ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx1 : 1 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hs : 0 ≤ scale512 ε A x := by
    have hx0 : 0 ≤ x := le_trans zero_le_one hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    unfold scale512
    positivity
  calc
    H D x ≤ 2 * F D x + 2 * G D x := hH D x
    _ ≤ (2 * C₁ + 2 * C₂) * scale512 ε A x := by
      nlinarith [hC₁ x hx₁, hC₂ x hx₂]
    _ ≤ C * scale512 ε A x := mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) hs

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
  sorry

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
  sorry

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
