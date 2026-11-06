import LeanLab.ChenDoubleSieve.Decomp366c

/-!
Supply the F4 prime sum limit through a fixed continuous kernel.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
The remaining partial summation input has no moving residual level,
no coprimality condition and no totient weight.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set MeasureTheory
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task366
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- LEAF. Wu 2004 page 39 equation 10.5, the fixed kernel part of the
standard replacement of sums over primes by integrals.
This statement has only reciprocal prime weights on the fixed ordered triangle.
The finite logarithmic perturbation and arithmetic restrictions are absent. -/
theorem continuous_prime_triangle (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2)) :
    Tendsto (fun N : ℕ => ∑ p ∈ fullPairs4 N,
      g (log (p.1 : ℝ) / log N, log (p.2 : ℝ) / log N) /
        ((p.1 : ℝ) * p.2)) atTop
      (𝓝 (∫ t in kappa1..kappa2, (∫ u in t..kappa2, g (t, u) / u) / t)) := by
  sorry

/-- The residual level kernel is continuous on the entire closed exponent square.
CONDITIONAL ON IsLinearSieve only. -/
theorem lower_kernel_continuous (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ContinuousOn (fun x : ℝ × ℝ => f ((1 / 2 - x.1 - x.2) / kappa1))
      (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2) := by
  apply h.2.1.comp
    (((continuous_const.sub continuous_fst).sub continuous_snd).div_const kappa1).continuousOn
  intro x hx
  change 0 < (1 / 2 - x.1 - x.2) / kappa1
  apply div_pos _ (by norm_num [kappa1])
  have hx1 := hx.1.2
  have hx2 := hx.2.2
  norm_num [kappa2] at hx1 hx2
  linarith

/-- The fixed continuous kernel supplies the zero loss reciprocal F4 limit.
OPEN through continuous_prime_triangle. -/
theorem reciprocalFullSum4_zero_tendsto (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    Tendsto (reciprocalFullSum4 f 0) atTop (𝓝 (lowerIntegral4 f)) := by
  have ht := continuous_prime_triangle
    (fun x : ℝ × ℝ => f ((1 / 2 - x.1 - x.2) / kappa1))
    (lower_kernel_continuous F f h)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  apply sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2, _⟩ := fullPairs4_primes hp
  rw [Task367.lowerLevel_zero_coordinates hN hp1.pos hp2.pos]

/-- The exact sealed lowerSum4_tendsto target follows from the smaller fixed
continuous kernel leaf and the proved elementary error estimates.
OPEN only through continuous_prime_triangle. -/
theorem lowerSum4_tendsto_supplied (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) :
    Tendsto (lowerSum4 f B) evenAtTop (𝓝 (lowerIntegral4 f)) := by
  exact lowerSum4_of_zero_loss F f h B hB
    (tendsto_inf_left (reciprocalFullSum4_zero_tendsto F f h))

end LeanLab.ChenDoubleSieve.Task366
