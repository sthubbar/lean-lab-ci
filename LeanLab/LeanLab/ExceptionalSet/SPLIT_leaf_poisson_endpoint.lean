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

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck)

/-- LEAF. Continuity step: for an integrable `K` the Fourier transform `ftR K` is
continuous in the frequency variable. This is the analytic content of the whole split, and
it is the only step that uses integrability of `K`. -/
theorem leaf_ftR_continuous (K : ℝ → ℂ) (hK : Integrable K) : Continuous (ftR K) := by
  sorry

/-- LEAF. Limit step: the rescaled frequencies `ξ * (1 + 1/(n+1))` tend to `ξ` as `n` grows.
This is the bookkeeping identity behind the limiting argument, and it holds for every
`ξ`, including `ξ = 0` and negative `ξ`. -/
theorem leaf_rescale_tendsto (ξ : ℝ) :
    Filter.Tendsto (fun n : ℕ => ξ * (1 + (1 : ℝ) / ((n : ℝ) + 1))) Filter.atTop (nhds ξ) := by
  sorry

/-- LEAF. Support step: for `1 ≤ |ξ|` every rescaled frequency `ξ * (1 + 1/(n+1))` has
absolute value strictly bigger than `1`, so the hypothesis that `ftR K` vanishes off the
closed unit interval applies at each of those points. The bound is strict at `n = 0`,
where the factor is `2`, and it is used only for `|ξ| ≥ 1`. -/
theorem leaf_rescale_abs_gt_one (ξ : ℝ) (hξ : 1 ≤ |ξ|) (n : ℕ) :
    1 < |ξ * (1 + (1 : ℝ) / ((n : ℝ) + 1))| := by
  sorry

/-- LEAF. Vanishing step: if a continuous function `f` vanishes at every member of a
sequence converging to `ξ`, then `f ξ = 0`. This is a purely topological step, with no
integral in it. -/
theorem leaf_eq_zero_of_tendsto {f : ℝ → ℂ} {u : ℕ → ℝ} {ξ : ℝ}
    (hf : Continuous f) (hu : Filter.Tendsto u Filter.atTop (nhds ξ)) (h0 : ∀ n : ℕ, f (u n) = 0) :
    f ξ = 0 := by
  sorry

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
