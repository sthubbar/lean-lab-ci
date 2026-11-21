/-
P0069 Baker Harman Pintz 1997, page 43 display 5.1 and page 52 before 5.18.
The finite character family is summed before the prefix bound is applied.
This avoids a loss equal to the number of characters in the family.
The raw coefficient prefix mean squares remain explicit inputs.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Task670WeightedMeanSquare
import LeanLab.BHP1997.Decomp514a

namespace LeanLab.BHP1997.Task670CharacterFamily518
open Classical Complex MeasureTheory DecompC165b LowerShortC165
open scoped BigOperators

/-- The finite weighted mean square transfer preserves a bound summed over a family.
This is an auxiliary normalization step for P0069 page 43 display 5.1. -/
theorem family_weighted_mean_square {ι κ : Type*} (F : Finset κ) (s : Finset ι)
    (c : ι → ℂ) (f : ι → κ → ℝ → ℂ) (w : ℝ → ℝ) {u v R : ℝ}
    (huv : u ≤ v) (hf : ∀ i ∈ s, ∀ χ ∈ F, Continuous (f i χ)) (hw : Continuous w)
    (hw0 : ∀ t ∈ Set.Icc u v, 0 ≤ w t)
    (hR : ∀ i ∈ s, (∑ χ ∈ F, ∫ t in u..v, ‖f i χ t‖ ^ 2 * w t) ≤ R) :
    (∑ χ ∈ F, ∫ t in u..v, ‖∑ i ∈ s, c i * f i χ t‖ ^ 2 * w t) ≤
      (∑ i ∈ s, ‖c i‖) ^ 2 * R := by
  let P : ℝ := ∑ i ∈ s, ‖c i‖
  have hP : 0 ≤ P := Finset.sum_nonneg fun i _ => norm_nonneg _
  have henergy : ∀ i ∈ s, ∀ χ ∈ F, Continuous (fun t => ‖f i χ t‖ ^ 2 * w t) :=
    fun i hi χ hχ => ((hf i hi χ hχ).norm.pow 2).mul hw
  have hχ (χ : κ) (hχ : χ ∈ F) :
      (∫ t in u..v, ‖∑ i ∈ s, c i * f i χ t‖ ^ 2 * w t) ≤
        P * ∑ i ∈ s, ‖c i‖ * (∫ t in u..v, ‖f i χ t‖ ^ 2 * w t) := by
    have hsum : Continuous (fun t => ∑ i ∈ s, c i * f i χ t) :=
      continuous_finsetSum _ fun i hi => continuous_const.mul (hf i hi χ hχ)
    have hmajor : Continuous (fun t => P * ∑ i ∈ s, ‖c i‖ * (‖f i χ t‖ ^ 2 * w t)) :=
      continuous_const.mul (continuous_finsetSum _ fun i hi =>
        continuous_const.mul (henergy i hi χ hχ))
    calc
      _ ≤ ∫ t in u..v, P * ∑ i ∈ s, ‖c i‖ * (‖f i χ t‖ ^ 2 * w t) := by
        apply intervalIntegral.integral_mono_on huv
          (((hsum.norm.pow 2).mul hw).intervalIntegrable u v) (hmajor.intervalIntegrable u v)
        intro t ht
        have hpoint : ‖∑ i ∈ s, c i * f i χ t‖ ^ 2 ≤
            P * ∑ i ∈ s, ‖c i‖ * ‖f i χ t‖ ^ 2 :=
          Task670WeightedMeanSquare.finite_weighted_square s c (fun i => f i χ t)
        have hh := mul_le_mul_of_nonneg_right hpoint (hw0 t ht)
        simpa only [Finset.sum_mul, mul_assoc, Pi.mul_apply, Pi.pow_apply] using hh
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
        · simp_rw [intervalIntegral.integral_const_mul]
        · intro i hi
          exact (continuous_const.mul (henergy i hi χ hχ)).intervalIntegrable u v
  calc
    _ ≤ ∑ χ ∈ F, P * ∑ i ∈ s, ‖c i‖ * (∫ t in u..v, ‖f i χ t‖ ^ 2 * w t) :=
      Finset.sum_le_sum hχ
    _ = P * ∑ i ∈ s, ‖c i‖ * (∑ χ ∈ F, ∫ t in u..v, ‖f i χ t‖ ^ 2 * w t) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ P * ∑ i ∈ s, ‖c i‖ * R := by
      apply mul_le_mul_of_nonneg_left _ hP
      exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hR i hi) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; dsimp [P]; ring

/-- Partial summation transfers a prefix mean square bound already summed over the
finite character family. P0069 page 43 display 5.1 and page 52 before display 5.18. -/
theorem abel_family_weighted_mean_square {κ : Type*} (K : Finset κ) (s : Finset ℕ)
    {L U : ℕ} (hLU : L ≤ U) (hs : ∀ m ∈ s, L ≤ m ∧ m ≤ U)
    (F : ℕ → ℂ) (a : ℕ → κ → ℝ → ℂ) (w : ℝ → ℝ) {u v R : ℝ} (huv : u ≤ v)
    (ha : ∀ m ∈ s, ∀ χ ∈ K, Continuous (a m χ)) (hw : Continuous w)
    (hw0 : ∀ t ∈ Set.Icc u v, 0 ≤ w t)
    (hprefix : ∀ i ∈ Finset.Icc L U,
      (∑ χ ∈ K, ∫ t in u..v, ‖∑ m ∈ s.filter (fun m => m ≤ i), a m χ t‖ ^ 2 * w t) ≤ R) :
    (∑ χ ∈ K, ∫ t in u..v, ‖∑ m ∈ s, F m * a m χ t‖ ^ 2 * w t) ≤
      (‖F U‖ + ∑ i ∈ Finset.Ico L U, ‖F (i + 1) - F i‖) ^ 2 * R := by
  classical
  let c : ℕ → ℂ := fun i => if i = U then F U else -(F (i + 1) - F i)
  let P : ℕ → κ → ℝ → ℂ := fun i χ t => ∑ m ∈ s.filter (fun m => m ≤ i), a m χ t
  have htop : s.filter (fun m => m ≤ U) = s :=
    Finset.filter_eq_self.mpr fun m hm => (hs m hm).2
  have hrep (χ : κ) (t : ℝ) : (∑ m ∈ s, F m * a m χ t) = ∑ i ∈ Finset.Icc L U, c i * P i χ t := by
    rw [← Finset.sum_Ico_add_eq_sum_Icc hLU]
    have hsum : (∑ i ∈ Finset.Ico L U, c i * P i χ t) =
        -(∑ i ∈ Finset.Ico L U, (F (i + 1) - F i) * P i χ t) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiU : i ≠ U := ne_of_lt (Finset.mem_Ico.mp hi).2
      simp only [c, ite_eq_right hiU, neg_mul]
    rw [hsum]
    simp only [c, ite_true, P, htop]
    rw [Decomp514Abel.finite_abel s hs F (fun m => a m χ t)]
    ring
  have hc : (∑ i ∈ Finset.Icc L U, ‖c i‖) =
      ‖F U‖ + ∑ i ∈ Finset.Ico L U, ‖F (i + 1) - F i‖ := by
    rw [← Finset.sum_Ico_add_eq_sum_Icc hLU]
    have hsum : (∑ i ∈ Finset.Ico L U, ‖c i‖) =
        ∑ i ∈ Finset.Ico L U, ‖F (i + 1) - F i‖ := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiU : i ≠ U := ne_of_lt (Finset.mem_Ico.mp hi).2
      simp only [c, ite_eq_right hiU, norm_neg]
    rw [hsum]
    simp only [c, ite_true]
    ring
  have hPc : ∀ i ∈ Finset.Icc L U, ∀ χ ∈ K, Continuous (P i χ) := by
    intro i _ χ hχ
    exact continuous_finsetSum _ fun m hm => ha m (Finset.mem_filter.mp hm).1 χ hχ
  simp_rw [hrep]
  have h := family_weighted_mean_square K (Finset.Icc L U) c P w huv hPc hw hw0 hprefix
  rwa [hc] at h

/-- The actual lower factor transfers a prefix bound summed over characters with loss four.
Its threshold is uniform in the modulus and in the finite family. P0069 page 43 display 5.1. -/
theorem lower_factor_character_mean_square (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, ∀ K : Finset (DirichletCharacter ℂ q),
      ∀ a : ℕ → DirichletCharacter ℂ q → ℝ → ℂ, ∀ w : ℝ → ℝ,
      ∀ u v R : ℝ, u ≤ v → 0 ≤ R →
      (∀ m ∈ rightInterval ε x, ∀ χ ∈ K, Continuous (a m χ)) → Continuous w →
      (∀ t ∈ Set.Icc u v, 0 ≤ w t) →
      (∀ i ∈ Finset.Icc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (∑ χ ∈ K, ∫ t in u..v,
          ‖∑ m ∈ (rightInterval ε x).filter (fun m => m ≤ i), a m χ t‖ ^ 2 * w t) ≤ R) →
      (∑ χ ∈ K, ∫ t in u..v, ‖∑ m ∈ rightInterval ε x,
        (lowerFactor ω ε x m : ℂ) * a m χ t‖ ^ 2 * w t) ≤ 4 * R := by
  obtain ⟨X, hX⟩ := Decomp514a.leaf_factor_variation ω hω hz hε hε8
  refine ⟨max X 1, fun x hx q K a w u v R huv hR ha hw hw0 hprefix => ?_⟩
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  let L : ℕ := ⌊x ^ (11 / 20 + ε)⌋₊
  let U : ℕ := ⌊2 * x ^ (11 / 20 + ε)⌋₊
  have hY : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
  have hLU : L ≤ U := Nat.floor_mono (by linarith)
  have hs : ∀ m ∈ rightInterval ε x, L ≤ m ∧ m ≤ U := by
    intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hm
    exact ⟨h1.le, h2⟩
  have h := abel_family_weighted_mean_square K (rightInterval ε x) hLU hs
    (fun m => (lowerFactor ω ε x m : ℂ)) a w huv ha hw hw0 hprefix
  have he : ‖(lowerFactor ω ε x U : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lowerFactor_nonneg _ _ _ _)]
    exact lowerFactor_le_one _ _ _ _
  have hv : (∑ i ∈ Finset.Ico L U,
      ‖(lowerFactor ω ε x (i + 1) : ℂ) - (lowerFactor ω ε x i : ℂ)‖) ≤ 1 := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hX x hxX
  have hv0 : 0 ≤ ∑ i ∈ Finset.Ico L U,
      ‖(lowerFactor ω ε x (i + 1) : ℂ) - (lowerFactor ω ε x i : ℂ)‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  have hcost : (‖(lowerFactor ω ε x U : ℂ)‖ + ∑ i ∈ Finset.Ico L U,
      ‖(lowerFactor ω ε x (i + 1) : ℂ) - (lowerFactor ω ε x i : ℂ)‖) ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (lowerFactor ω ε x U : ℂ)]
  exact h.trans (mul_le_mul_of_nonneg_right hcost hR)

end LeanLab.BHP1997.Task670CharacterFamily518
