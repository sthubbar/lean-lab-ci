import LeanLab.HelfgottMajor.SPLIT_principal_log_weight_budget

/-!
Splitting the long range square energy of the logarithmic derivative weight,
`Decomp457b.principal_log_weight_sq_long`, which bounds the square energy on the two half
lines `2 < |t|` by 190.

The region `2 < |t|` is the union of four intervals: the two windows `2 < t ≤ 5` and
`-5 ≤ t < -2` next to the cut at height two, and the two tails `5 < t` and `t < -5` beyond
height five.  On a window the weight is only bounded, and the length three of the window is
what the budget pays for; on a tail only the decay of the weight is paid for.  The four
interval budgets are seventy five, seventy five, twenty and twenty, and they add up to 190.

Each leaf below is one interval energy estimate of the weight.  The partition identity and
the addition of the four bounds are the only other ingredients, and both are proved here.
No prime sum, no zero sum and no scale appears in any of them.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
open Real MeasureTheory Contour457

/-- LEAF. The positive window next to the cut at height two: the square energy of the
logarithmic derivative weight over `2 < t ≤ 5` is at most seventy five.  This is the
bounded-size step on the short interval of length three, and it carries no decay. -/
theorem principal_log_weight_sq_window_pos :
    (∫ t in Set.Ioc 2 5, ‖principalLogWeight t‖ ^ 2) ≤ 75 := by
  sorry

/-- LEAF. The positive tail beyond height five: the square energy of the logarithmic
derivative weight over `5 < t` is at most twenty.  This is the decay step on the positive
half line, where only the fall off of the weight is paid for. -/
theorem principal_log_weight_sq_tail_pos :
    (∫ t in Set.Ioi 5, ‖principalLogWeight t‖ ^ 2) ≤ 20 := by
  sorry

/-- LEAF. The negative window next to the cut at height two: the square energy of the
logarithmic derivative weight over `-5 ≤ t < -2` is at most seventy five.  This is the
mirror image of the positive window and is kept as its own step because the weight is not
declared even anywhere in this file. -/
theorem principal_log_weight_sq_window_neg :
    (∫ t in Set.Ico (-5) (-2), ‖principalLogWeight t‖ ^ 2) ≤ 75 := by
  sorry

/-- LEAF. The negative tail beyond height five: the square energy of the logarithmic
derivative weight over `t < -5` is at most twenty.  This is the decay step on the negative
half line, kept separate from the positive tail for the same reason as the two windows. -/
theorem principal_log_weight_sq_tail_neg :
    (∫ t in Set.Iio (-5), ‖principalLogWeight t‖ ^ 2) ≤ 20 := by
  sorry

/-- The two half lines `2 < |t|` are exactly the union of the two intervals `t > 2` and
`t < -2`. -/
private theorem principal_log_weight_sq_long_region :
    ({t : ℝ | 2 < |t|} : Set ℝ) = Set.Ioi 2 ∪ Set.Iio (-2) := by
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ioi, Set.mem_Iio]
  constructor
  · intro h
    rcases lt_abs.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact lt_abs.mpr (Or.inl h)
    · exact lt_abs.mpr (Or.inr (by linarith))

/-- The positive half line splits at height five into the window and the tail. -/
private theorem principal_log_weight_sq_long_region_pos :
    (Set.Ioi (2 : ℝ)) = Set.Ioc 2 5 ∪ Set.Ioi 5 := by
  ext t
  simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
  constructor
  · intro h
    by_cases h5 : t ≤ 5
    · exact Or.inl ⟨h, h5⟩
    · exact Or.inr (by linarith)
  · rintro (⟨h, _⟩ | h)
    · exact h
    · linarith

/-- The negative half line splits at height five into the window and the tail. -/
private theorem principal_log_weight_sq_long_region_neg :
    (Set.Iio (-2 : ℝ)) = Set.Ico (-5) (-2) ∪ Set.Iio (-5) := by
  ext t
  simp only [Set.mem_Iio, Set.mem_union, Set.mem_Ico]
  constructor
  · intro h
    by_cases h5 : -5 ≤ t
    · exact Or.inl ⟨h5, h⟩
    · exact Or.inr (by linarith)
  · rintro (⟨_, h⟩ | h)
    · exact h
    · linarith

/-- The square energy over `2 < |t|` is the sum of the four interval energies.  The two
half lines are cut at height five, the four pieces are disjoint and measurable, and the
squared weight is integrable, so the integral splits twice on each half line. -/
private theorem principal_log_weight_sq_long_decomp :
    (∫ t in {t : ℝ | 2 < |t|}, ‖principalLogWeight t‖ ^ 2) =
      ((∫ t in Set.Ioc 2 5, ‖principalLogWeight t‖ ^ 2) +
        (∫ t in Set.Ioi 5, ‖principalLogWeight t‖ ^ 2)) +
      ((∫ t in Set.Ico (-5) (-2), ‖principalLogWeight t‖ ^ 2) +
        (∫ t in Set.Iio (-5), ‖principalLogWeight t‖ ^ 2)) := by
  classical
  have hint : Integrable (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) :=
    MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two (by norm_num)
  have hd : Disjoint (Set.Ioc (2 : ℝ) 5 ∪ Set.Ioi 5)
      (Set.Ico (-5) (-2) ∪ Set.Iio (-5)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    rw [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi] at hx
    rw [Set.mem_union, Set.mem_Ico, Set.mem_Iio] at hy
    rcases hx with ⟨h1, h2⟩ | h1 <;> rcases hy with ⟨k1, k2⟩ | k1 <;> linarith
  have hdp : Disjoint (Set.Ioc (2 : ℝ) 5) (Set.Ioi 5) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_Ioc] at hx
    rw [Set.mem_Ioi] at hx'
    linarith
  have hdn : Disjoint (Set.Ico (-5) (-2 : ℝ)) (Set.Iio (-5)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_Ico] at hx
    rw [Set.mem_Iio] at hx'
    linarith
  have h1 : (∫ t in (Set.Ioc (2 : ℝ) 5 ∪ Set.Ioi 5) ∪ (Set.Ico (-5) (-2) ∪ Set.Iio (-5)),
      ‖principalLogWeight t‖ ^ 2)
      = (∫ t in Set.Ioc (2 : ℝ) 5 ∪ Set.Ioi 5, ‖principalLogWeight t‖ ^ 2) +
        (∫ t in Set.Ico (-5) (-2) ∪ Set.Iio (-5), ‖principalLogWeight t‖ ^ 2) :=
    setIntegral_union hd (measurableSet_Ico.union measurableSet_Iio)
      hint.integrableOn hint.integrableOn
  have h2 : (∫ t in Set.Ioc (2 : ℝ) 5 ∪ Set.Ioi 5, ‖principalLogWeight t‖ ^ 2)
      = (∫ t in Set.Ioc 2 5, ‖principalLogWeight t‖ ^ 2) +
        (∫ t in Set.Ioi 5, ‖principalLogWeight t‖ ^ 2) :=
    setIntegral_union hdp measurableSet_Ioi hint.integrableOn hint.integrableOn
  have h3 : (∫ t in Set.Ico (-5) (-2 : ℝ) ∪ Set.Iio (-5), ‖principalLogWeight t‖ ^ 2)
      = (∫ t in Set.Ico (-5) (-2), ‖principalLogWeight t‖ ^ 2) +
        (∫ t in Set.Iio (-5), ‖principalLogWeight t‖ ^ 2) :=
    setIntegral_union hdn measurableSet_Iio hint.integrableOn hint.integrableOn
  rw [principal_log_weight_sq_long_region, principal_log_weight_sq_long_region_pos,
    principal_log_weight_sq_long_region_neg, h1, h2, h3]

/-- The long range square energy budget of the logarithmic derivative weight on the two half
lines `2 < |t|`, assembled from the four interval estimates.  The partition identity
reduces the region to the four pieces, and the four budgets add up to 190. -/
theorem principal_log_weight_sq_long_split :
    (∫ t in {t : ℝ | 2 < |t|}, ‖principalLogWeight t‖ ^ 2) ≤ 190 := by
  rw [principal_log_weight_sq_long_decomp]
  linarith [principal_log_weight_sq_window_pos, principal_log_weight_sq_tail_pos,
    principal_log_weight_sq_window_neg, principal_log_weight_sq_tail_neg]

end LeanLab.HelfgottMajor.Decomp457b
