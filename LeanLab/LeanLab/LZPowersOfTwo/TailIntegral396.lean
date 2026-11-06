/-
P0079 page 10, display 36, integration of the inverse-square model tail.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.CountBounds293

open Real MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 10, display 36. The inverse-square majorant is integrable
on every positive half-line. -/
theorem inverse_square_integrable396 (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Set.Ioi a) := by
  have H := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha
  simpa [Real.rpow_neg, Real.rpow_two, one_div] using H

/-- P0079 page 10, display 36. The integral of the inverse-square
majorant from positive a to infinity equals the reciprocal of a. -/
theorem inverse_square_integral396 (a : ℝ) (ha : 0 < a) :
    (∫ x : ℝ in Set.Ioi a, 1 / x ^ 2) = 1 / a := by
  have H := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha
  norm_num [Real.rpow_neg, Real.rpow_two, one_div] at H ⊢
  simpa only [Real.rpow_neg_one] using H

/-- P0079 page 10, display 36. An integrable function bounded above
by C divided by alpha squared on both tails has tail integral at most
2 C divided by the positive cutoff. -/
theorem inverse_square_tail_bound396 (f : ℝ → ℝ) (hf : Integrable f)
    (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (hbound : ∀ x : ℝ, a < |x| → f x ≤ C / x ^ 2) :
    (∫ x in {x : ℝ | a < |x|}, f x) ≤ 2 * C / a := by
  have hpos (g : ℝ → ℝ) (hg : Integrable g)
      (hb : ∀ x : ℝ, a < x → g x ≤ C / x ^ 2) :
      (∫ x in Set.Ioi a, g x) ≤ C / a := by
    calc
      _ ≤ ∫ x in Set.Ioi a, C * (1 / x ^ 2) := by
        apply setIntegral_mono_on hg.integrableOn
          ((inverse_square_integrable396 a ha).const_mul C) measurableSet_Ioi
        intro x hx
        simpa only [mul_one_div] using hb x hx
      _ = _ := by rw [integral_const_mul, inverse_square_integral396 a ha]; ring
  have hp := hpos f hf (fun x hx => hbound x (by rwa [abs_of_pos (ha.trans hx)]))
  have hn := hpos (fun x => f (-x)) hf.comp_neg
    (fun x hx => by simpa only [neg_sq] using
      (hbound (-x) (by rwa [abs_neg, abs_of_pos (ha.trans hx)])))
  rw [integral_comp_neg_Ioi] at hn
  have hset : {x : ℝ | a < |x|} = Set.Iio (-a) ∪ Set.Ioi a := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, lt_abs]
    constructor <;> intro H <;> rcases H with H | H
    · exact Or.inr H
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl H
  have hd : Disjoint (Set.Iio (-a)) (Set.Ioi a) := by
    apply Set.disjoint_left.mpr
    intro x hx hx'
    simp only [Set.mem_Iio, Set.mem_Ioi] at hx hx'
    linarith
  rw [hset, setIntegral_union hd measurableSet_Ioi hf.integrableOn hf.integrableOn,
    ← integral_Iic_eq_integral_Iio]
  calc
    _ ≤ C / a + C / a := add_le_add hn hp
    _ = _ := by ring

end LeanLab.LZPowersOfTwo
