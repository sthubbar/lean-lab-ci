/-
P0079 page 10, integrating the elementary rectangle slices.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp375f
open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo
/-- P0079 page 10, the inner integral in display 37.
Integrating the proved tent lower bound on its contained interval gives
eta squared over twice lambda1, without any analytic prime estimate. -/
theorem tent_slice_lower375 (l q ε X η u v : ℝ)
    (hl : 1 < l) (hq : 1 < q) (hql : q ≤ l)
    (hε : 0 < ε) (hX : 0 < X) (hη : 0 < η)
    (hηsmall : η ≤ 2 * ε * (l - 1) * X) (hu : |u| ≤ ε * X)
    (hv : v ∈ Set.Icc (2 * ε * l * X / q) ((1 - ε * l) * X / q)) :
    η ^ 2 / (2 * l) ≤
      ∫ t in Set.Icc (ε * X) X, max 0 (η - |l * t - q * v + u|) := by
  have H := tent_rectangle375 l q ε X η u v hl hq hql hε hX hη hηsmall hu hv
  dsimp only at H
  let c := (q * v - u) / l
  let r := η / (2 * l)
  have hl0 : 0 < l := by linarith only [hl]
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hc : Continuous (fun t : ℝ => max 0 (η - |l * t - q * v + u|)) := by fun_prop
  have hmono : (∫ t in Set.Icc (c - r) (c + r), (η / 2 : ℝ)) ≤
      ∫ t in Set.Icc (c - r) (c + r), max 0 (η - |l * t - q * v + u|) :=
    setIntegral_mono_on continuous_const.integrableOn_Icc hc.integrableOn_Icc
      measurableSet_Icc H.2.2
  have hsub : (∫ t in Set.Icc (c - r) (c + r), max 0 (η - |l * t - q * v + u|)) ≤
      ∫ t in Set.Icc (ε * X) X, max 0 (η - |l * t - q * v + u|) :=
    setIntegral_mono_set hc.integrableOn_Icc (Eventually.of_forall (fun _ => le_max_left _ _))
      (Eventually.of_forall (fun _ ht => H.2.1 ht))
  have hlen : 0 ≤ (c + r) - (c - r) := by linarith only [hr0]
  have hconst : (∫ t in Set.Icc (c - r) (c + r), (η / 2 : ℝ)) = η ^ 2 / (2 * l) := by
    rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul, max_eq_left hlen]
    dsimp [r]
    field_simp
    <;> ring
  rw [hconst] at hmono
  exact hmono.trans hsub
end LeanLab.LZPowersOfTwo
