/-
Unit task393, branch repair of `free-nv-nemotron/task393`.

The branch `free-nv-nemotron/task393` tried to discharge `Routes.U1556Sweep.dqt_W_le` and left
its scaffolding in place: seven `sorry` tokens inside the body of that existing statement, on a
file that carried one, and text that does not elaborate. This module carries the open step, so the
existing file stays exactly as main has it and gains nothing.

The step is stated on the upstream `Dpt` (ChirreHagen2025.ThetaPsi) rather than on
`Routes.U1556Sweep.Dqt`; the two expressions are definitionally equal, and `dqt_W_le_of_leaf`
below is the parent's statement verbatim, proved from the leaf by unfolding both.

Nothing here is new mathematics: the statement is the one already open on main.
-/
import Mathlib
import LeanLab.ChirreHagen2025.SmoothY
import LeanLab.ChirreHagen2025.ThetaPsi
import LeanLab.Routes.U1556Sweep

namespace LeanLab.Task393

open Real MeasureTheory Set Filter Topology
open LeanLab.ChirreHagen2025 LeanLab.ChirreHagen2025.SmoothKernel

/-- LEAF: the weighted prime power difference, unconditional. For `0 < δ ≤ 10^-13` and
`X ≥ 10^13`, `D(y)² W(y/X)` with `D = (ψ - θ)((1+δ)y) - (ψ - θ)(y)` and `W` the SmoothY weight is
integrable on `y > 2` and `∫_{y>2} D² W(y/X) ≤ 10^-6 δ log²(2.0001/δ) X²`.

Plain math: `D ≥ 0` is supported near prime powers `p^k`, `k ≥ 2`; when `δ√y < 1` the lab's
`Dpt_le` gives `D ≤ log²((1+δ)y)/log 2` and `∫ D W ~ δ Σ p^k log p W(p^k/X) << δ X^{3/2} log X`,
so the ratio is about `0.27 log X / (L² √X) < 10^-8` at `X = 10^13`; when `δ√y ≥ 1`,
`D ≤ θ(√((1+δ)y)) - θ(√y) + O(y^{1/3})` and Brun-Titchmarsh give `D² << δ² y log² y`, ratio
`<< δ`. Splitting `∫_2^∞` at `X` and bounding the tail with `W(y/X) = (X/y)^4` is the bookkeeping.
Carried over from `Routes.U1556Sweep` unchanged. Unit task393. -/
theorem leaf_dpt_W_le {δ X : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (hX : 10 ^ 13 ≤ X) :
    IntegrableOn (fun y => Dpt δ y ^ 2 * W (y / X)) (Ioi 2) ∧
      ∫ y in Ioi 2, Dpt δ y ^ 2 * W (y / X)
        ≤ 1 / 10 ^ 6 * δ * Real.log (2.0001 / δ) ^ 2 * X ^ 2 := by
  sorry

/-- Twin of `Routes.U1556Sweep.dqt_W_le`, the parent's statement verbatim in this namespace and
proved from `leaf_dpt_W_le`: `Dqt` and `Dpt` are the same term written through two names, so the
parent's open step follows from the leaf by unfolding both. It is not new mathematics and it does
not touch the parent, which keeps its own `sorry`. Unit task393. -/
theorem dqt_W_le_of_leaf {δ X : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13) (hX : 10 ^ 13 ≤ X) :
    IntegrableOn (fun y => LeanLab.Routes.U1556.Dqt δ y ^ 2 * W (y / X)) (Ioi 2) ∧
      ∫ y in Ioi 2, LeanLab.Routes.U1556.Dqt δ y ^ 2 * W (y / X)
        ≤ 1 / 10 ^ 6 * δ * Real.log (2.0001 / δ) ^ 2 * X ^ 2 := by
  have h := leaf_dpt_W_le (δ := δ) (X := X) hδ hδ1 hX
  simpa only [LeanLab.Routes.U1556.Dqt, Dpt, fpt] using h

end LeanLab.Task393
