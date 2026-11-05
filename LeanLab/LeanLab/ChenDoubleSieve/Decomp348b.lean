import LeanLab.ChenDoubleSieve.Decomp348a

/-!
Supply split for the F4 lower bound in Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set MeasureTheory
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open Task275
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The actual ordered coprime prime pair domain for Upsilon 4. -/
def lowerPairs4 (N : ℕ) : Finset (ℕ × ℕ) :=
  Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2)

/-- The finite prime sum before passage to the F4 double integral. -/
def lowerSum4 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ lowerPairs4 N,
    f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ)

/-- The unscaled double integral in equation 10.5 for F4. -/
def lowerIntegral4 (f : ℝ → ℝ) : ℝ :=
  ∫ t in kappa1..kappa2,
    (∫ u in t..kappa2, f ((1 / 2 - t - u) / kappa1) / u) / t

/-- The finite level main term for Upsilon 4. -/
def main4 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) / log N * lowerDensity N * lowerSum4 f B N

-- FREE-nv-minimax task169 attempt: the direct IsLinearSieve projections for both leaves were tried and failed because the hypothesis has no such fields.

/-- LEAF. Wu 2004 page 39 equation 10.5, application of Lemmas 2.2 and 2.3.
This estimates only the count by its finite prime sum main term.
The replacement of li N by N over log N is included in the normalized error. -/
theorem main4_lower (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        main4 f B N - η * Θ N ≤ sieveTerms N 4 := by
  sorry

/-- LEAF. Wu 2004 page 39 equation 10.5, replacement of prime sums by integrals.
The coprimality removal and finite logarithmic level loss belong to this limit.
There is no sieve count or Euler product in this statement. -/
theorem lowerSum4_tendsto (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) :
    Tendsto (lowerSum4 f B) evenAtTop (𝓝 (lowerIntegral4 f)) := by
  sorry

/-- Exact normalization of the finite Upsilon 4 main term. -/
theorem main4_ratio (f : ℝ → ℝ) (B : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    main4 f B N / Θ N = scaledDensity N * lowerSum4 f B N := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold main4 scaledDensity Θ
  field_simp [(CN_pos N).ne', hlog.ne', hpos.ne']
  <;> ring

/-- The finite Upsilon 4 main term tends to its exact integral coefficient.
CONDITIONAL ON the two OPEN normalization limits and IsLinearSieve. -/
theorem main4_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) :
    Tendsto (fun N => main4 f B N / Θ N) evenAtTop
      (𝓝 (integralTerms F f ω 4)) := by
  have ht := scaledDensity_tendsto.mul (lowerSum4_tendsto F f h B hB)
  have ht' : Tendsto (fun N => scaledDensity N * lowerSum4 f B N)
      evenAtTop (𝓝 (integralTerms F f ω 4)) := by
    convert ht using 1
    change 𝓝 (2 / (kappa1 * exp eulerMascheroniConstant) * lowerIntegral4 f) = _
    rfl
  apply ht'.congr'
  filter_upwards [(eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left] with N hN
  exact (main4_ratio f B hN).symm

/-- The exact lower_F4 conclusion follows from strictly smaller analytic leaves.
OPEN through main4_lower, lowerSum4_tendsto and scaledDensity_tendsto. -/
theorem lower_F4_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 4 - ε) * Θ N ≤ sieveTerms N 4 := by
  exact lower_of_main _ _ (main4 f) (main4_lower F f h)
    (fun B hB => main4_tendsto F f ω h B hB)

end LeanLab.ChenDoubleSieve.Task348
