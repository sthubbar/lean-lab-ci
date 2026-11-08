import LeanLab.ExceptionalSet.SPLIT_leaf_poisson

/-!
Split of the sealed statement `leaf_poisson_endpoint` of
`LeanLab.ExceptionalSet.SPLIT_leaf_poisson` into four strictly smaller steps, plus an
assembly `leaf_poisson_endpoint_split` whose statement is the sealed statement and whose
proof uses only the four leaves.

The sealed statement asks that the Fourier transform of `K` vanish at the two boundary
frequencies `|ξ| = 1`, while the hypothesis `hsupp` only gives vanishing for `1 < |α|`.
The proof is a single limiting argument, cut here into its four ingredients:

* `leaf_ftR_continuous`: `ftR K` is continuous when `K` is integrable; this is the
  analytic step and the only place integrability is used.
* `leaf_rescale_tendsto`: the rescaled frequencies `ξ (1 + 1/(n+1))` tend to `ξ`.
* `leaf_rescale_abs_gt_one`: those frequencies stay outside the closed unit interval, so
  the support hypothesis applies to each of them.
* `leaf_eq_zero_of_tendsto`: a continuous function vanishing along a sequence tending to
  `ξ` vanishes at `ξ`.

Note that the continuity hypothesis on `K` itself is not needed for this step: the
continuity that matters is that of `ftR K`, which integrability alone supplies.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp371d

open Real MeasureTheory Filter
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck)

/-- LEAF. Continuity step: for an integrable `K` the Fourier transform `ftR K` is
continuous in the frequency variable. This is the analytic content of the whole split, and
it is the only step that uses integrability of `K`. -/
theorem leaf_ftR_continuous (K : ℝ → ℂ) (hK : Integrable K) : Continuous (ftR K) := by
  have heC_norm : ∀ x : ℝ, ‖eC x‖ = 1 := by
    intro x
    unfold eC
    have h : (2 * (π : ℂ) * Complex.I * (x : ℂ)) = ((2 * π * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have heC_continuous : Continuous eC := by
    unfold eC
    fun_prop
  unfold ftR
  have key : ∀ β : ℝ, Continuous fun x : ℝ => K β * eC (-(x * β)) := by
    intro β
    exact continuous_const.mul
      (heC_continuous.comp ((continuous_id.mul continuous_const : Continuous fun x : ℝ => x * β).neg))
  have keym : ∀ ξ : ℝ, AEStronglyMeasurable (fun β : ℝ => K β * eC (-(ξ * β))) := by
    intro ξ
    exact hK.aestronglyMeasurable.mul
      (heC_continuous.comp ((continuous_const.mul continuous_id : Continuous fun β : ℝ => ξ * β).neg)).aestronglyMeasurable
  refine continuous_of_dominated (bound := fun β => ‖K β‖)
    (F := fun ξ β => K β * eC (-(ξ * β))) keym ?_ hK.norm ?_
  · intro ξ
    filter_upwards with β
    rw [norm_mul, heC_norm, mul_one]
  · filter_upwards with β
    exact key β

/-- LEAF. Limit step: the rescaled frequencies `ξ * (1 + 1/(n+1))` tend to `ξ` as `n` grows.
This is the bookkeeping identity behind the limiting argument, and it holds for every
`ξ`, including `ξ = 0` and negative `ξ`. -/
theorem leaf_rescale_tendsto (ξ : ℝ) :
    Filter.Tendsto (fun n : ℕ => ξ * (1 + (1 : ℝ) / ((n : ℝ) + 1))) Filter.atTop (nhds ξ) := by
  have heq : (fun n : ℕ => ξ * (1 + 1 / ((n : ℝ) + 1))) = fun n : ℕ => ξ + ξ * (1 / ((n : ℝ) + 1)) := by
    ext n
    ring
  rw [heq]
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℝ => 1 / (n + 1)) atTop (nhds 0) := by
      have heq2 : (fun n : ℝ => 1 / (n + 1)) = (fun x : ℝ => x⁻¹) ∘ (fun n : ℝ => n + 1) := by
        ext x
        simp only [Function.comp_apply, one_div]
      rw [heq2]
      exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
    have h2 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop
    exact h1.comp h2
  have h3 : Tendsto (fun n : ℕ => ξ * (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
    have hz : nhds 0 = nhds (ξ * 0) := by rw [mul_zero]
    rw [hz]
    exact Tendsto.const_mul ξ h
  have h4 : Tendsto (fun n : ℕ => ξ + ξ * (1 / ((n : ℝ) + 1))) atTop (nhds ξ) := by
    have hz : nhds ξ = nhds (ξ + 0) := by rw [add_zero]
    rw [hz]
    exact Tendsto.const_add ξ h3
  exact h4

/-- LEAF. Support step: for `1 ≤ |ξ|` every rescaled frequency `ξ * (1 + 1/(n+1))` has
absolute value strictly bigger than `1`, so the hypothesis that `ftR K` vanishes off the
closed unit interval applies at each of those points. The bound is strict at `n = 0`,
where the factor is `2`, and it is used only for `|ξ| ≥ 1`. -/
theorem leaf_rescale_abs_gt_one (ξ : ℝ) (hξ : 1 ≤ |ξ|) (n : ℕ) :
    1 < |ξ * (1 + (1 : ℝ) / ((n : ℝ) + 1))| := by
  have h1 : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  have h2 : 1 < 1 + (1 : ℝ) / ((n : ℝ) + 1) := by linarith
  have h3 : 0 < 1 + (1 : ℝ) / ((n : ℝ) + 1) := by linarith
  rw [abs_mul]
  have h4 : |1 + (1 : ℝ) / ((n : ℝ) + 1)| = 1 + (1 : ℝ) / ((n : ℝ) + 1) := by
    exact abs_of_pos h3
  rw [h4]
  nlinarith

/-- LEAF. Vanishing step: if a continuous function `f` vanishes at every member of a
sequence converging to `ξ`, then `f ξ = 0`. This is a purely topological step, with no
integral in it. -/
theorem leaf_eq_zero_of_tendsto {f : ℝ → ℂ} {u : ℕ → ℝ} {ξ : ℝ}
    (hf : Continuous f) (hu : Filter.Tendsto u Filter.atTop (nhds ξ)) (h0 : ∀ n : ℕ, f (u n) = 0) :
    f ξ = 0 := by
  have h1 : Tendsto (fun n : ℕ => f (u n)) atTop (nhds (f ξ)) := by
    exact Tendsto.comp hf.continuousAt hu
  have h2 : Tendsto (fun n : ℕ => (0 : ℂ)) atTop (nhds (f ξ)) := by
    have h_eq : (fun n : ℕ => (0 : ℂ)) = (fun n : ℕ => f (u n)) := by
      ext n
      exact (h0 n).symm
    rw [h_eq]
    exact h1
  have h3 : Tendsto (fun n : ℕ => (0 : ℂ)) atTop (nhds 0) := tendsto_const_nhds
  exact tendsto_nhds_unique h2 h3

/-- Assembly: the sealed statement, from the four leaves above. The continuity hypothesis on
`K` is not used, only the continuity of `ftR K` that `leaf_ftR_continuous` supplies. -/
theorem leaf_poisson_endpoint_split (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    ∀ ξ : ℝ, 1 ≤ |ξ| → ftR K ξ = 0 := by
  intro ξ hξ
  refine leaf_eq_zero_of_tendsto (f := ftR K) (u := fun n : ℕ => ξ * (1 + (1 : ℝ) / ((n : ℝ) + 1)))
    (leaf_ftR_continuous K hK) (leaf_rescale_tendsto ξ) ?_
  intro n
  exact hsupp _ (leaf_rescale_abs_gt_one ξ hξ n)

end LeanLab.ExceptionalSet.Decomp371d
