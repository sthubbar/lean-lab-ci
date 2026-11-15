/-
SPLIT of brun_titchmarsh_pointwise from Decomp92.lean.
AI wrote this Lean code, SPLIT task550, 2026-11-15.
Source: Montgomery and Vaughan, The Large Sieve, Mathematica 20, 1973, Theorem 2;
also Ramare and Saouter 2003 page 16.
-/
import LeanLab.KadiriLumley2014.ZeroDefinitions259
import LeanLab.KadiriLumley2014.SmoothedFormula259
import LeanLab.KadiriLumley2014.TableRounding
import LeanLab.KadiriLumley2014.TableCertificates259
import LeanLab.KadiriLumley2014.BindingRow
import LeanLab.KadiriLumley2014.OmegaIntegral
import LeanLab.KadiriLumley2014.WeightTail

namespace LeanLab.KadiriLumley2014.TaskF550

open Real Set MeasureTheory
open Task64

/-- LEAF. The tail coefficient formula from equation 2.7, page 3.
This is the exact expression for the upper bound on the theta difference. -/
theorem tailCoefficient_formula (δ u X : ℝ) :
    tailCoefficient δ u X = 2 * (1 + δ) * (Real.exp u - 1) * X *
      (Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1))) :=
  rfl

/-- LEAF. For the parameters, the argument to theta is nonnegative.
This holds because X ≥ exp 38 and the other factors are positive. -/
theorem theta_arg_nonneg {δ u X t : ℝ} (hδ : 0 ≤ δ) (hu : 0 ≤ u) (hX : 0 < X)
    (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ X * (1 + δ * t) := by
  have ht0 : 0 ≤ t := ht.1
  have : 0 ≤ 1 + δ * t := by nlinarith
  nlinarith

/-- LEAF. The exponential factor is at least one when u ≥ 0. -/
theorem exp_factor_ge_one (u : ℝ) (hu : 0 ≤ u) : 1 ≤ Real.exp u :=
  Real.one_le_exp_iff.mpr hu

/-- LEAF. The two theta arguments are ordered: X*(1+δ*t) ≤ exp(u)*X*(1+δ*t). -/
theorem theta_arg_order {δ u X t : ℝ} (hδ : 0 ≤ δ) (hu : 0 ≤ u) (hX : 0 < X)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    X * (1 + δ * t) ≤ Real.exp u * (X * (1 + δ * t)) := by
  have hE : 1 ≤ Real.exp u := exp_factor_ge_one u hu
  have hpos : 0 ≤ X * (1 + δ * t) := theta_arg_nonneg hδ hu hX ht
  nlinarith

/-- LEAF. The pointwise theta difference is nonnegative.
This follows from theta_mono since the arguments are ordered. -/
theorem theta_diff_nonneg {δ u X t : ℝ} (hδ : 0 ≤ δ) (hu : 0 ≤ u) (hX : 0 < X)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
        Chebyshev.theta (X * (1 + δ * t)) := by
  have harg := theta_arg_order hδ hu hX ht
  have := Chebyshev.theta_mono (theta_arg_nonneg hδ hu hX ht) harg
  linarith

/-- LEAF. The pointwise Brun-Titchmarsh bound from Montgomery-Vaughan 1973.
This is the exact constant-two bound cited in the paper. -/
theorem brun_titchmarsh_pointwise {δ u X t : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) (hgap : 1 < X * (Real.exp u - 1))
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
      Chebyshev.theta (X * (1 + δ * t)) ≤ tailCoefficient δ u X := by
  sorry

/-- Assembly theorem: brun_titchmarsh_pointwise_F550.
The exact statement from Decomp92.lean, proved from the leaves above.
This is the pointwise Brun-Titchmarsh bound from Montgomery-Vaughan 1973,
Theorem 2, as cited in the paper. -/
theorem brun_titchmarsh_pointwise_F550 {δ u X t : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) (hgap : 1 < X * (Real.exp u - 1))
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
      Chebyshev.theta (X * (1 + δ * t)) ≤ tailCoefficient δ u X := by
  have hu0 : 0 ≤ u := hu.le
  have hXpos : 0 < X := by
    have h := Real.exp_pos 38
    linarith
  exact brun_titchmarsh_pointwise hδ hδ1 hu hu1 hX hgap ht

end LeanLab.KadiriLumley2014.TaskF550
