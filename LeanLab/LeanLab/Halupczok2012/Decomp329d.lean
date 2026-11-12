import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-!
Arithmetic audit of the short interval parameters in Wu 2004.
Source: arXiv 0705.1652 page 34 Lemma 9.2 and page 42 Theorem 5 proof.
https://arxiv.org/abs/0705.1652
The ordered parameter range and two auxiliary inequalities hold.
The printed condition three kappa one plus rho at least one half fails.
This is a QUESTION about the short interval adaptation.
It does not refute Theorem 5 or the sealed Wu leaf.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp329d

/-- Wu arXiv pages 34 and 42, an exact audit at theta equal to 0.971.
The last two assertions isolate the deficit in the printed weight lemma hypothesis. -/
theorem wu_short_parameter_audit :
    let θ : ℝ := 971 / 1000
    let κ1 : ℝ := (2 * θ - 1) / 12
    let κ2 : ℝ := 111 / 1000
    let ρ : ℝ := (2 * θ - 1) / 4
    let σ2 : ℝ := 271 / 1000
    let σ1 : ℝ := 313 / 1000
    0 < κ1 ∧ κ1 < κ2 ∧ κ2 < ρ ∧ ρ < σ2 ∧ σ2 < σ1 ∧ σ1 < 1 / 3 ∧
      1 < 3 * σ1 + κ1 ∧ 1 < 2 * σ1 + σ2 + κ2 ∧
      3 * κ1 + ρ = 471 / 1000 ∧
      1 / 2 - (3 * κ1 + ρ) = 29 / 1000 ∧ 3 * κ1 + ρ < 1 / 2 := by
  norm_num

end LeanLab.Halupczok2012.Decomp329d
