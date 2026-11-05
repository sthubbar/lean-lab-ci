import LeanLab.ChenDoubleSieve.Decomp348a

/-!
Supply split for the F5 lower bound in Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set MeasureTheory
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open Task275
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The actual ordered coprime prime pair domain for Upsilon 5. -/
def lowerPairs5 (N : ℕ) : Finset (ℕ × ℕ) :=
  Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ kappa2 ∧
      (N : ℝ) ^ kappa2 ≤ q ∧
      (q : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / p)

/-- The finite prime sum before passage to the F5 double integral. -/
def lowerSum5 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ lowerPairs5 N,
    f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ)

/-- The unscaled double integral in equation 10.5 for F5. -/
def lowerIntegral5 (f : ℝ → ℝ) : ℝ :=
  ∫ t in kappa1..kappa2,
    (∫ u in kappa2..(1 / 2 - 2 * kappa1 - t), f ((1 / 2 - t - u) / kappa1) / u) / t

/-- The finite level main term for Upsilon 5. -/
def main5 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) / log N * lowerDensity N * lowerSum5 f B N

/-- LEAF. Wu 2004 page 39 equation 10.5, application of Lemmas 2.2 and 2.3.
This estimates only the count by its finite prime sum main term.
The replacement of li N by N over log N is included in the normalized error. -/
theorem main5_lower (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        main5 f B N - η * Θ N ≤ sieveTerms N 5 := by
  sorry

/-- LEAF. Wu 2004 page 39 equation 10.5, replacement of prime sums by integrals.
The coprimality removal and finite logarithmic level loss belong to this limit.
There is no sieve count or Euler product in this statement. -/
theorem lowerSum5_tendsto (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) :
    Tendsto (lowerSum5 f B) evenAtTop (𝓝 (lowerIntegral5 f)) := by
  sorry

/-- Exact normalization of the finite Upsilon 5 main term. -/
theorem main5_ratio (f : ℝ → ℝ) (B : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    main5 f B N / Θ N = scaledDensity N * lowerSum5 f B N := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold main5 scaledDensity Θ
  field_simp [(CN_pos N).ne', hlog.ne', hpos.ne']
  <;> ring

/-- The finite Upsilon 5 main term tends to its exact integral coefficient.
CONDITIONAL ON the two OPEN normalization limits and IsLinearSieve. -/
theorem main5_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) :
    Tendsto (fun N => main5 f B N / Θ N) evenAtTop
      (𝓝 (integralTerms F f ω 5)) := by
  have ht := scaledDensity_tendsto.mul (lowerSum5_tendsto F f h B hB)
  have ht' : Tendsto (fun N => scaledDensity N * lowerSum5 f B N)
      evenAtTop (𝓝 (integralTerms F f ω 5)) := by
    convert ht using 1
    change 𝓝 (2 / (kappa1 * exp eulerMascheroniConstant) * lowerIntegral5 f) = _
    rfl
  apply ht'.congr'
  filter_upwards [(eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left] with N hN
  exact (main5_ratio f B hN).symm

/-- The exact lower_F5 conclusion follows from strictly smaller analytic leaves.
OPEN through main5_lower, lowerSum5_tendsto and scaledDensity_tendsto. -/
theorem lower_F5_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 5 - ε) * Θ N ≤ sieveTerms N 5 := by
  exact lower_of_main _ _ (main5 f) (main5_lower F f h)
    (fun B hB => main5_tendsto F f ω h B hB)

end LeanLab.ChenDoubleSieve.Task348
