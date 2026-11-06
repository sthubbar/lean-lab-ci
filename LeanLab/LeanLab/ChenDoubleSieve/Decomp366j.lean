import LeanLab.ChenDoubleSieve.Decomp366f

/-!
The constant kernel case of the F4 prime sum integral limit.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
This verifies the ordered triangle normalization without the general weighted input.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set MeasureTheory intervalIntegral
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task366
open Task275 Task348

/-- The reciprocal triangle integral is half the square of its logarithmic mass. -/
theorem reciprocal_triangle_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (∫ u in t..b, (1 : ℝ) / u) / t) = log (b / a) ^ 2 / 2 := by
  have hb : 0 < b := ha.trans_le hab
  have hinner : (∫ t in a..b, (∫ u in t..b, (1 : ℝ) / u) / t) =
      ∫ t in a..b, (log b - log t) / t := by
    apply integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := ha.trans_le ht.1
    dsimp only
    rw [integral_one_div_of_pos ht0 hb, log_div hb.ne' ht0.ne']
  rw [hinner]
  have hd : ∀ t ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => -(log b - log t) ^ 2 / 2)
        ((log b - log t) / t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := ha.trans_le ht.1
    convert (((hasDerivAt_log ht0.ne').const_sub (log b)).pow 2).neg.div_const 2 using 1
    ring
  have hc : ContinuousOn (fun t : ℝ => (log b - log t) / t) (Icc a b) := by
    apply (continuousOn_const.sub (continuousOn_id.log (by
      intro t ht
      exact (ha.trans_le ht.1).ne'))).div continuousOn_id
    intro t ht
    exact (ha.trans_le ht.1).ne'
  rw [integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hab)]
  rw [log_div hb.ne' ha.ne']
  ring

/-- A constant numerator scales the reciprocal triangle integral exactly. -/
theorem reciprocal_triangle_const {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c : ℝ) :
    (∫ t in a..b, (∫ u in t..b, c / u) / t) = c * (log (b / a) ^ 2 / 2) := by
  have he : (fun u : ℝ => c / u) = fun u : ℝ => c * (1 / u) := by
    funext u
    ring
  simp_rw [he, intervalIntegral.integral_const_mul, mul_div_assoc]
  rw [intervalIntegral.integral_const_mul, reciprocal_triangle_integral ha hab]

/-- The paper's unscaled F4 integral has the expected value for a constant f. -/
theorem lowerIntegral4_const (c : ℝ) :
    lowerIntegral4 (fun _ => c) = c * (log (kappa2 / kappa1) ^ 2 / 2) := by
  exact reciprocal_triangle_const (by norm_num [kappa1])
    (by norm_num [kappa1, kappa2]) c

/-- Every constant kernel has the exact prime triangle integral limit.
This theorem uses no OPEN analytic input and no sieve function hypothesis. -/
theorem constant_prime_triangle_tendsto (c : ℝ) :
    Tendsto (fun N : ℕ => ∑ p ∈ fullPairs4 N, c / ((p.1 : ℝ) * p.2)) atTop
      (𝓝 (∫ t in kappa1..kappa2, (∫ u in t..kappa2, c / u) / t)) := by
  change Tendsto _ atTop (𝓝 (lowerIntegral4 (fun _ => c)))
  rw [lowerIntegral4_const]
  convert fullPairs4_mass_tendsto.const_mul c using 1
  ext N
  simp only [pairMass, mul_sum]
  apply sum_congr rfl
  intro p hp
  ring

end LeanLab.ChenDoubleSieve.Task366
