import LeanLab.ExceptionalSet.UpJ200.Decomp428d

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.Localization446`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


namespace LeanLab.ExceptionalSet.UpJ200.Localization446

open Real MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (Sp Kfun calE)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp404e

/-- P0082 page 366 before display 27. For a nonnegative integrable weight,
a distant pair bound by V leaves at most V times the square of its mass.
This is an auxiliary integral comparison and uses no cancellation theorem. -/
theorem far_integral_le (A : Set ℝ) (g : ℝ → ℝ) (H : ℝ → ℝ → ℝ)
    (hg : IntegrableOn g A) (hg0 : ∀ x, 0 ≤ g x) (hH0 : ∀ x y, 0 ≤ H x y)
    (r V : ℝ) (hV : 0 ≤ V)
    (hH : ∀ x ∈ A, ∀ y ∈ A, r < |x - y| → H x y ≤ V) :
    (∫ x in A, ∫ y in A ∩ {y : ℝ | r < |x - y|}, g x * g y * H x y) ≤
      V * (∫ x in A, g x) ^ 2 := by
  have hm : 0 ≤ ∫ x in A, g x := integral_nonneg hg0
  have hi (x : ℝ) (hx : x ∈ A) :
      (∫ y in A ∩ {y : ℝ | r < |x - y|}, g x * g y * H x y) ≤
        g x * V * (∫ y in A, g y) := by
    calc
      _ ≤ ∫ y in A ∩ {y : ℝ | r < |x - y|}, g x * V * g y := by
        apply setIntegral_mono_of_nonneg
        · intro y hy
          exact mul_nonneg (mul_nonneg (hg0 x) (hg0 y)) (hH0 x y)
        · intro y hy
          have ht := mul_le_mul_of_nonneg_left (hH x hx y hy.1 hy.2)
            (mul_nonneg (hg0 x) (hg0 y))
          nlinarith
        · exact (hg.mono_set inter_subset_left).const_mul (g x * V)
      _ ≤ ∫ y in A, g x * V * g y :=
        setIntegral_mono_set (hg.const_mul _) (Filter.Eventually.of_forall (fun y => mul_nonneg (mul_nonneg (hg0 x) hV) (hg0 y)))
          inter_subset_left.eventuallySubset
      _ = _ := integral_const_mul _ _
  calc
    _ ≤ ∫ x in A, g x * V * (∫ y in A, g y) := by
      apply setIntegral_mono_of_nonneg
      · intro x hx
        apply integral_nonneg
        intro y
        exact mul_nonneg (mul_nonneg (hg0 x) (hg0 y)) (hH0 x y)
      · exact hi
      · exact (hg.mul_const V).mul_const _
    _ = V * (∫ x in A, g x) ^ 2 := by
      rw [integral_mul_const, integral_mul_const]
      ring

/-- P0082 page 366 display 27. A nearby strip of radius r has length
at most twice r. The two pointwise bounds control its inner integral. -/
theorem near_integral_le (A : Set ℝ) (g : ℝ → ℝ) (H : ℝ → ℝ → ℝ)
    (hg : IntegrableOn g A) (hg0 : ∀ x, 0 ≤ g x) (hH0 : ∀ x y, 0 ≤ H x y)
    (r B T : ℝ) (hr : 0 ≤ r) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hgb : ∀ x ∈ A, g x ≤ B) (hH : ∀ x ∈ A, ∀ y ∈ A, H x y ≤ T) :
    (∫ x in A, ∫ y in A ∩ {y : ℝ | |x - y| ≤ r}, g x * g y * H x y) ≤
      2 * r * B * T * (∫ x in A, g x) := by
  have hi (x : ℝ) (hx : x ∈ A) :
      (∫ y in A ∩ {y : ℝ | |x - y| ≤ r}, g x * g y * H x y) ≤
        (2 * r * B * T) * g x := by
    have hsub : A ∩ {y : ℝ | |x - y| ≤ r} ⊆ Icc (x - r) (x + r) := by
      intro y hy
      have hh := abs_le.mp (show |x - y| ≤ r from hy.2)
      constructor <;> linarith
    have hconst : IntegrableOn (fun _ : ℝ => g x * B * T) (Icc (x - r) (x + r)) :=
      integrableOn_const (by simp)
    calc
      _ ≤ ∫ y in A ∩ {y : ℝ | |x - y| ≤ r}, g x * B * T := by
        apply setIntegral_mono_of_nonneg
        · intro y hy
          exact mul_nonneg (mul_nonneg (hg0 x) (hg0 y)) (hH0 x y)
        · intro y hy
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hgb y hy.1) (hg0 x))
            (hH x hx y hy.1) (hH0 x y) (mul_nonneg (hg0 x) hB)
        · exact hconst.mono_set hsub
      _ ≤ ∫ y in Icc (x - r) (x + r), g x * B * T :=
        setIntegral_mono_set hconst
          (Filter.Eventually.of_forall (fun _ => mul_nonneg (mul_nonneg (hg0 x) hB) hT))
          hsub.eventuallySubset
      _ = _ := by
        rw [setIntegral_const]
        simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ x + r - (x - r))]
        ring
  calc
    _ ≤ ∫ x in A, (2 * r * B * T) * g x := by
      apply setIntegral_mono_of_nonneg
      · intro x hx
        apply integral_nonneg
        intro y
        exact mul_nonneg (mul_nonneg (hg0 x) (hg0 y)) (hH0 x y)
      · exact hi
      · exact hg.const_mul _
    _ = _ := integral_const_mul _ _

/-- Exact supply for Decomp428d.leaf_far_localization.
Source: P0082 page 366, first contribution to display 26. -/
theorem leaf_far_localization_supplied (γ δ κ : ℝ) (N : ℕ) (V : ℝ) (hV : 0 ≤ V)
    (hΔ : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1)
    (hphase : ∀ α ∈ truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
      ∀ β ∈ truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
        F γ N ^ (3 * δ - 1) < |α - β| → ‖phaseSum γ N (β - α)‖ ≤ V) :
    farMoment γ δ κ N ≤ V *
      (∫ α in truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
        ‖Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
          (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)‖) ^ 2 := by
  let X := F γ N
  let P := X ^ (6 * δ)
  let Δ := calE γ κ N ^ (-(1 / 8 : ℝ))
  let A := truncatedDomain P X
  let g : ℝ → ℝ := fun α => ‖Sp P X α ^ 2 * (Kfun Δ α : ℂ)‖
  have hc : Continuous g := by
    apply Continuous.norm
    apply Continuous.mul
    · unfold Sp U1539.eC
      fun_prop
    · exact KernelTransform264.Kfun_continuous Δ
  exact far_integral_le A g (fun α β => ‖phaseSum γ N (β - α)‖)
    (hc.integrableOn_Icc.mono_set inter_subset_right)
    (fun _ => norm_nonneg _) (fun _ _ => norm_nonneg _) (X ^ (3 * δ - 1)) V hV hphase

/-- Exact supply for Decomp428c.leaf_localization.
Source: P0082 page 366 display 27. No prime cancellation estimate is assumed. -/
theorem leaf_localization_supplied (γ δ κ : ℝ) (N : ℕ) (U : ℝ)
    (hU : 0 ≤ U) (hΔ : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1)
    (hsup : ∀ β ∈ truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
      ‖Sp (F γ N ^ (6 * δ)) (F γ N) β‖ ^ 2 ≤ U) :
    nearMoment γ δ κ N ≤
      4 * N * F γ N ^ (3 * δ - 1) * U *
        (∫ α in truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
          ‖Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
            (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)‖) := by
  let X := F γ N
  let P := X ^ (6 * δ)
  let Δ := calE γ κ N ^ (-(1 / 8 : ℝ))
  let A := truncatedDomain P X
  let g : ℝ → ℝ := fun α => ‖Sp P X α ^ 2 * (Kfun Δ α : ℂ)‖
  have hc : Continuous g := by
    apply Continuous.norm
    apply Continuous.mul
    · unfold Sp U1539.eC
      fun_prop
    · exact KernelTransform264.Kfun_continuous Δ
  have hΔ0 : 0 < Δ := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hgb (β : ℝ) (hβ : β ∈ A) : g β ≤ 2 * U := by
    have hk := KernelTail385.kernel_abs_le_two_sub Δ β hΔ0 hΔ
    have hs := hsup β hβ
    dsimp [g]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ U * 2 := mul_le_mul hs (by linarith) (abs_nonneg _) hU
      _ = _ := by ring
  have hb := near_integral_le A g (fun α β => ‖phaseSum γ N (β - α)‖)
    (hc.integrableOn_Icc.mono_set inter_subset_right)
    (fun _ => norm_nonneg _) (fun _ _ => norm_nonneg _) (X ^ (3 * δ - 1)) (2 * U) N
    (Real.rpow_nonneg (Real.exp_pos _).le _) (by positivity) (Nat.cast_nonneg _)
    hgb (fun _ _ β _ => Decomp428d.phaseSum_norm_le γ N _)
  change nearMoment γ δ κ N ≤ _ at hb
  convert hb using 1 <;> dsimp only [X, P, Δ, A, g] <;> ring

end LeanLab.ExceptionalSet.UpJ200.Localization446
