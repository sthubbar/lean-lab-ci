import LeanLab.ExceptionalSet.SPLIT_leaf_product_integrable

/-!
Split of the kernel step of the generic Fourier fold: for an integrable continuous
kernel whose Fourier transform vanishes outside the interval from `-1` to `1`, the
supremum of the norm of the kernel over the unit interval starting at `n` is a
summable function of the integer `n`.

The proof smooths the kernel with a factor whose Fourier transform equals one on that
interval, so the kernel is reproduced by its convolution with the factor. The value at
a point is then bounded by the weighted integral of the factor against the kernel, the
supremum over one unit interval is bounded by the integral of the supremum of the
weights, the weights are summed over the intervals by monotone convergence, and the
total weight is bounded by one constant, which leaves the integral of the kernel alone.

The four lemmas marked LEAF below are the open work items; the assembly at the end of
the file derives the kernel statement from them.
-/

namespace LeanLab.ExceptionalSet.Decomp446b

open Real MeasureTheory
open scoped ENNReal
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck norm_eC)

/-- LEAF. Step 1 of the proof: the smoothing factor exists. There is an integrable
function of one real variable whose Fourier transform equals one on the closed interval
from `-1` to `1`, and whose unit interval sup norms, summed over the integers, are
bounded by a single constant uniformly after any real translation. The statement
mentions no kernel. -/
theorem leaf_split_bump_exists :
    ∃ (φ : ℝ → ℂ) (C : ℝ≥0∞),
      Integrable φ ∧
        (∀ α : ℝ, |α| ≤ 1 → ftR φ α = 1) ∧
          C ≠ ⊤ ∧
            (∀ y : ℝ,
              (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1),
                ENNReal.ofReal ‖φ (t - y)‖) ≤ C) := by
  sorry

/-- LEAF. Step 2 of the proof: the convolution identity. Convolving the kernel with a
smoothing factor whose Fourier transform equals one on the closed interval from `-1`
to `1` returns the kernel at every point. This is one identity and it says nothing
about summing over the integer intervals. -/
theorem leaf_split_conv_eq (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (φ : ℝ → ℂ) (hφ : Integrable φ)
    (hφhat : ∀ α : ℝ, |α| ≤ 1 → ftR φ α = 1) :
    ∀ t : ℝ, (∫ y : ℝ, φ (t - y) * K y) = K t := by
  sorry

/-- LEAF. Step 3 of the proof: the bound on one unit interval. The supremum of the
norm of the kernel over the unit interval starting at the integer `n` is at most the
integral over the real line of the supremum of the modulus of the smoothing factor on
that same interval, translated to the integration variable, against the modulus of the
kernel. One interval only, no sum over `n`. -/
theorem leaf_split_interval_sup_le (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (φ : ℝ → ℂ) (hφ : Integrable φ)
    (hφhat : ∀ α : ℝ, |α| ≤ 1 → ftR φ α = 1) (n : ℤ) :
    (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) ≤
      ∫⁻ y : ℝ,
        (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖φ (t - y)‖) *
          ENNReal.ofReal ‖K y‖ := by
  sorry

/-- LEAF. Step 4 of the proof: the sum over the intervals of the interval integrals is
at most the integral of the summed weights. This is the exchange of a sum over the
integers with an integral of nonnegative extended real valued functions, with the
modulus of the kernel as the common weight; it is an inequality, not an identity, and
it bounds no kernel on its own. -/
theorem leaf_split_tsum_integral_le (K : ℝ → ℂ) (φ : ℝ → ℂ) :
    (∑' n : ℤ, ∫⁻ y : ℝ,
        (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖φ (t - y)‖) *
          ENNReal.ofReal ‖K y‖) ≤
      ∫⁻ y : ℝ,
        (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖φ (t - y)‖) *
          ENNReal.ofReal ‖K y‖ := by
  sorry

/-- Assembly. The weights of the four steps above: the smoothing factor of step 1,
the convolution identity of step 2, the single interval bound of step 3 and the
exchange of the sum with the integral in step 4, with the uniform bound on the total
weight turning the result into a finite multiple of the integral of the kernel. -/
theorem leaf_kernel_sup_summable_split (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖) ≠ ⊤ := by
  classical
  obtain ⟨φ, C, hφ, hφhat, hC, hCbound⟩ := leaf_split_bump_exists
  have hk : (∫⁻ y : ℝ, ENNReal.ofReal ‖K y‖) < ⊤ := by
    have h := hK.2
    rw [hasFiniteIntegral_iff_norm] at h
    exact h
  have hmul : (∫⁻ y : ℝ, C * ENNReal.ofReal ‖K y‖) ≠ ⊤ := by
    rw [lintegral_const_mul'' C hK.1.norm.aemeasurable.ennreal_ofReal]
    exact (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) hk).ne
  refine ne_top_of_le_ne_top hmul ?_
  calc
    (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖K t‖)
        ≤ ∑' n : ℤ, ∫⁻ y : ℝ,
            (⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖φ (t - y)‖) *
              ENNReal.ofReal ‖K y‖ :=
          ENNReal.tsum_le_tsum fun n => leaf_split_interval_sup_le K hK hcont hsupp φ hφ hφhat n
    _ ≤ ∫⁻ y : ℝ,
          (∑' n : ℤ, ⨆ t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1), ENNReal.ofReal ‖φ (t - y)‖) *
            ENNReal.ofReal ‖K y‖ :=
        leaf_split_tsum_integral_le K φ
    _ ≤ ∫⁻ y : ℝ, C * ENNReal.ofReal ‖K y‖ := by
        refine lintegral_mono fun y => ?_
        have hy := hCbound y
        gcongr

end LeanLab.ExceptionalSet.Decomp446b
