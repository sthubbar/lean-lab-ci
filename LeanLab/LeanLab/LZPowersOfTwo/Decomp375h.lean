/-
P0079 page 10, the continuous double-box lower bound in display 37.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp375g
open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo
/-- P0079 page 10, display 37. Integrating the positive slices over the
permitted v band gives the full continuous rectangle lower coefficient. -/
theorem tent_box_lower375 (l q ε X η u : ℝ)
    (hl : 1 < l) (hq : 1 < q) (hql : q ≤ l)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l)) (hX : 0 < X) (hη : 0 < η)
    (hηsmall : η ≤ 2 * ε * (l - 1) * X) (hu : |u| ≤ ε * X) :
    (1 - 3 * l * ε) / (2 * (l * q)) * η ^ 2 * X ≤
      ∫ v in Set.Icc (ε * X) X,
        ∫ t in Set.Icc (ε * X) X, max 0 (η - |l * t - q * v + u|) := by
  have hl0 : 0 < l := by linarith only [hl]
  have hq0 : 0 < q := by linarith only [hq]
  have hsmall : 8 * l * ε < 1 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * l)).mp hε'
    nlinarith only [H]
  have hk : 0 < 1 - 3 * ε * l := by nlinarith only [hsmall, mul_pos hε hl0]
  let a := 2 * ε * l * X / q
  let b := (1 - ε * l) * X / q
  have hab : a ≤ b := by
    dsimp [a, b]
    apply (div_le_div_iff_of_pos_right hq0).mpr
    nlinarith only [mul_nonneg hk.le hX.le]
  have H := tent_rectangle375 l q ε X η u a hl hq hql hε hX hη hηsmall hu ⟨le_rfl, hab⟩
  let F := fun v : ℝ => ∫ t in Set.Icc (ε * X) X, max 0 (η - |l * t - q * v + u|)
  have hc : Continuous F := by
    apply continuous_parametric_integral_of_continuous (s := Set.Icc (ε * X) X)
    ·
      fun_prop
    · exact isCompact_Icc
  have hn : ∀ v, 0 ≤ F v := fun v => integral_nonneg (fun t => le_max_left _ _)
  have hm : (∫ v in Set.Icc a b, (η ^ 2 / (2 * l) : ℝ)) ≤ ∫ v in Set.Icc a b, F v := by
    apply setIntegral_mono_on continuous_const.integrableOn_Icc hc.integrableOn_Icc measurableSet_Icc
    intro v hv
    exact tent_slice_lower375 l q ε X η u v hl hq hql hε hX hη hηsmall hu hv
  have hs : (∫ v in Set.Icc a b, F v) ≤ ∫ v in Set.Icc (ε * X) X, F v :=
    setIntegral_mono_set hc.integrableOn_Icc (Eventually.of_forall hn)
      (Eventually.of_forall (fun _ hv => H.1 hv))
  have he : (∫ v in Set.Icc a b, (η ^ 2 / (2 * l) : ℝ)) =
      (1 - 3 * l * ε) / (2 * (l * q)) * η ^ 2 * X := by
    rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul, max_eq_left (sub_nonneg.mpr hab)]
    dsimp [a, b]
    field_simp
    <;> ring
  rw [he] at hm
  exact hm.trans hs
end LeanLab.LZPowersOfTwo
