import LeanLab.PNTPort.Selberg.Sharp4

/-!
# Almost all short windows contain a prime power, under RH

Lab proof, unit U-5926, CLOUD 20261020T0216Z-cloud32, T2 toward IDEAS I-5100. AI wrote this
file. Known mathematics, Selberg 1943's corollary in a Gaussian-weighted local form;
CONDITIONAL ON RiemannHypothesis only.

`almost_all_windows`: assuming RH there is `C` such that for `0 < η ≤ δ ≤ 1` and every `U`, the
Gaussian-weighted measure of the `u ≥ U - 1` for which `(e^u, e^{u+δ}]` holds no prime power,
that is `ψ(e^{u+δ}) = ψ(e^u)`, is at most
`C (δ (log(1/δ) + 3)² + η² e^U + η^{-5/4} e^{-2U}) / (δ² e^U)`.

Proof: on that set `N(u) = -e^{-u/2} e^u (e^δ - 1)`, so `N(u)² ≥ δ² e^u ≥ δ² e^{U-1}`; Chebyshev's
inequality with `selberg_sharp`. With `X = e^U`, `h = δX` and `η = √(δ/X)` the bound is
`≪ log²X / h` for `h ≥ X^{2/13}`: under RH, outside a set of weighted measure `≪ log² X/h`, every
window `(x, x e^δ]` near `X` contains a prime power.
-/

namespace LeanLab.PNTPort.Selberg

open Complex Finset MeasureTheory Filter Topology
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.PNTPort.Gallagher

/-- The weighted indicator of the empty windows `ψ(e^{u+δ}) = ψ(e^u)`, `u ≥ U - 1`. -/
noncomputable def emptyW (δ U u : ℝ) : ℝ :=
  if U - 1 ≤ u ∧ Chebyshev.psi (Real.exp (u + δ)) = Chebyshev.psi (Real.exp u) then gw U u else 0

lemma emptyW_le (δ U u : ℝ) (hδ : 0 < δ) :
    emptyW δ U u ≤ Nw δ u ^ 2 * gw U u / (δ ^ 2 * Real.exp (U - 1)) := by
  unfold emptyW
  have hg := gw_nonneg U u
  split_ifs with h
  · obtain ⟨hu, hψ⟩ := h
    have hpos : 0 < δ ^ 2 * Real.exp (U - 1) := by positivity
    rw [le_div_iff₀ hpos]
    have hN : Nw δ u ^ 2 = Real.exp u * (Real.exp δ - 1) ^ 2 := by
      unfold Nw
      rw [hψ, show Real.exp (u + δ) = Real.exp u * Real.exp δ from Real.exp_add u δ]
      have e1 : Real.exp (-(u / 2)) ^ 2 = Real.exp (-u) := by
        rw [← Real.exp_nat_mul]; ring_nf
      have e2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
      have : (Real.exp (-(u / 2)) * (Chebyshev.psi (Real.exp u) - Chebyshev.psi (Real.exp u) -
          (Real.exp u * Real.exp δ - Real.exp u))) ^ 2 =
          Real.exp (-(u / 2)) ^ 2 * Real.exp u * (Real.exp u * (Real.exp δ - 1) ^ 2) := by ring
      rw [this, e1, e2, one_mul]
    rw [hN]
    have hd : δ ≤ Real.exp δ - 1 := by linarith [Real.add_one_le_exp δ]
    have hd2 : δ ^ 2 ≤ (Real.exp δ - 1) ^ 2 := pow_le_pow_left₀ hδ.le hd 2
    have he : Real.exp (U - 1) ≤ Real.exp u := Real.exp_le_exp.mpr hu
    have : δ ^ 2 * Real.exp (U - 1) ≤ Real.exp u * (Real.exp δ - 1) ^ 2 := by
      calc δ ^ 2 * Real.exp (U - 1) ≤ (Real.exp δ - 1) ^ 2 * Real.exp u :=
            mul_le_mul hd2 he (by positivity) (by positivity)
        _ = _ := by ring
    calc gw U u * (δ ^ 2 * Real.exp (U - 1)) ≤ gw U u * (Real.exp u * (Real.exp δ - 1) ^ 2) :=
          mul_le_mul_of_nonneg_left this hg
      _ = _ := by ring
  · positivity

lemma measurable_emptyW (δ U : ℝ) : Measurable (emptyW δ U) := by
  have hψ : Measurable (fun x : ℝ => Chebyshev.psi x) := Chebyshev.psi_mono.measurable
  have h1 : Measurable (fun u : ℝ => Chebyshev.psi (Real.exp (u + δ))) :=
    hψ.comp (Real.measurable_exp.comp (measurable_id.add_const δ))
  have h2 : Measurable (fun u : ℝ => Chebyshev.psi (Real.exp u)) := hψ.comp Real.measurable_exp
  have hs : MeasurableSet {u : ℝ | U - 1 ≤ u ∧
      Chebyshev.psi (Real.exp (u + δ)) = Chebyshev.psi (Real.exp u)} :=
    (measurableSet_le measurable_const measurable_id).inter (measurableSet_eq_fun h1 h2)
  unfold emptyW
  exact Measurable.ite hs (gw_continuous U).measurable measurable_const

/-- **Almost all short windows hold a prime power**, under RH. -/
theorem almost_all_windows (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ δ η : ℝ, 0 < η → η ≤ δ → δ ≤ 1 → ∀ U : ℝ,
    Integrable (emptyW δ U) ∧
      ∫ u, emptyW δ U u ≤ C * (δ * (Real.log (1 / δ) + 3) ^ 2 +
        η ^ 2 * Real.exp U + η ^ (-(5 / 4) : ℝ) * Real.exp (-(2 * U))) /
          (δ ^ 2 * Real.exp (U - 1)) := by
  obtain ⟨C, hC, h⟩ := selberg_sharp hRH
  refine ⟨C, hC, fun δ η hη hηδ hδ1 U => ?_⟩
  have hδ : 0 < δ := lt_of_lt_of_le hη hηδ
  obtain ⟨hi, hb⟩ := h δ η hη hηδ hδ1 U
  have hpos : 0 < δ ^ 2 * Real.exp (U - 1) := by positivity
  have hI : Integrable (fun u => Nw δ u ^ 2 * gw U u / (δ ^ 2 * Real.exp (U - 1))) :=
    hi.div_const _
  have hE : Integrable (emptyW δ U) := by
    refine hI.mono' (measurable_emptyW δ U).aestronglyMeasurable (ae_of_all _ fun u => ?_)
    have h0 : 0 ≤ emptyW δ U u := by
      unfold emptyW; split_ifs
      · exact gw_nonneg U u
      · exact le_rfl
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact emptyW_le δ U u hδ
  refine ⟨hE, ?_⟩
  calc ∫ u, emptyW δ U u ≤ ∫ u, Nw δ u ^ 2 * gw U u / (δ ^ 2 * Real.exp (U - 1)) :=
        integral_mono hE hI fun u => emptyW_le δ U u hδ
    _ = (∫ u, Nw δ u ^ 2 * gw U u) / (δ ^ 2 * Real.exp (U - 1)) := integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right hb hpos.le

end LeanLab.PNTPort.Selberg
