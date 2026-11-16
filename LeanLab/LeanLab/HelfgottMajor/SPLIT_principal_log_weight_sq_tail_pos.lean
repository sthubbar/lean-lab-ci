import LeanLab.HelfgottMajor.SPLIT_principal_log_weight_sq_long

/-!
Splitting the positive tail energy `principal_log_weight_sq_tail_pos`, the square energy of the
logarithmic derivative weight on `5 < t` bounded by twenty.

The tail is cut once more, at height eight.  On the near piece `5 < t ≤ 8` the interval is short
and only the size of the weight is paid for; on the far piece `8 < t` only the decay is paid for.
Both pieces are compared against the same elementary majorant `(2 log t + 3) ^ 2 / t ^ 2`, whose
primitive `-((2 log t) ^ 2 + 20 log t + 29) / t` gives the two numerical values `3.322` and
`10.988`, and the two budgets four and sixteen add up to twenty.

Every leaf below is one step of that comparison: the pointwise square bound, integrability of the
majorant on each piece, and the two numerical integrals.  The partition identity, the monotone
comparison on each piece and the final addition are proved here, leaving no gap.
-/

namespace LeanLab.HelfgottMajor.Decomp457b
open Real MeasureTheory Contour457

/-- LEAF. The pointwise square bound on the positive tail: for `5 < t` the square of the
logarithmic derivative weight is at most the elementary majorant `(2 log t + 3) ^ 2 / t ^ 2`.
This is the analytic step, the size of `logDeriv riemannZeta` at `-1/2 + i t` against the size of
`-1/2 + i t`, and it carries all the arithmetic content of the bound. -/
theorem tail_pos_pointwise_sq (t : ℝ) (ht : 5 < t) :
    ‖principalLogWeight t‖ ^ 2 ≤ (2 * Real.log t + 3) ^ 2 / t ^ 2 := by
  sorry

/-- LEAF. Integrability of the majorant on the near piece `5 < t ≤ 8`.  The majorant is dominated
by a negative power of `t`, so it is integrable on the short interval; this is the hypothesis that
lets the near piece be compared with the weight. -/
theorem tail_pos_majorant_integrableOn_head :
    IntegrableOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (Set.Ioc 5 8) := by
  sorry

/-- LEAF. Integrability of the majorant on the far piece `8 < t`.  Here the decay of the majorant
is what is paid for, and again a negative power of `t` dominates it; this is the hypothesis that
lets the far piece be compared with the weight. -/
theorem tail_pos_majorant_integrableOn_far :
    IntegrableOn (fun t : ℝ => (2 * Real.log t + 3) ^ 2 / t ^ 2) (Set.Ioi 8) := by
  sorry

/-- LEAF. The numerical value of the near piece: the integral of the majorant over `5 < t ≤ 8` is
at most four.  The primitive is `-((2 log t) ^ 2 + 20 log t + 29) / t`, which gives the value
`3.322` for this piece, and the budget four leaves room. -/
theorem tail_pos_majorant_head_le :
    (∫ t in Set.Ioc 5 8, (2 * Real.log t + 3) ^ 2 / t ^ 2) ≤ 4 := by
  sorry

/-- LEAF. The numerical value of the far piece: the integral of the majorant over `8 < t` is at
most sixteen.  The same primitive gives the value `10.988` for this piece, and the budget sixteen
leaves room. -/
theorem tail_pos_majorant_far_le :
    (∫ t in Set.Ioi 8, (2 * Real.log t + 3) ^ 2 / t ^ 2) ≤ 16 := by
  sorry

/-- The positive tail `5 < t` splits at height eight into the near piece and the far piece. -/
private theorem tail_pos_region :
    (Set.Ioi (5 : ℝ)) = Set.Ioc 5 8 ∪ Set.Ioi 8 := by
  ext t
  simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
  constructor
  · intro h
    by_cases h8 : t ≤ 8
    · exact Or.inl ⟨h, h8⟩
    · exact Or.inr (by linarith)
  · rintro (⟨h, _⟩ | h)
    · exact h
    · linarith

/-- The two pieces of the positive tail are disjoint. -/
private theorem tail_pos_disjoint :
    Disjoint (Set.Ioc (5 : ℝ) 8) (Set.Ioi 8) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [Set.mem_Ioc] at hx
  rw [Set.mem_Ioi] at hx'
  linarith

/-- The square energy over the positive tail is the sum of the energies over the two pieces.  The
pieces are disjoint and measurable and the squared weight is integrable, so the integral splits. -/
private theorem tail_pos_decomp :
    (∫ t in Set.Ioi (5 : ℝ), ‖principalLogWeight t‖ ^ 2) =
      (∫ t in Set.Ioc 5 8, ‖principalLogWeight t‖ ^ 2) +
        (∫ t in Set.Ioi 8, ‖principalLogWeight t‖ ^ 2) := by
  have hint : Integrable (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) :=
    MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two (by norm_num)
  rw [tail_pos_region,
    setIntegral_union tail_pos_disjoint measurableSet_Ioi hint.integrableOn hint.integrableOn]

/-- The square energy of the logarithmic derivative weight on the positive tail `5 < t` is at most
twenty.  The tail is cut at height eight, each piece is compared with the elementary majorant
using the pointwise bound, and the two numerical integrals four and sixteen add up to twenty. -/
theorem principal_log_weight_sq_tail_pos_split :
    (∫ t in Set.Ioi 5, ‖principalLogWeight t‖ ^ 2) ≤ 20 := by
  classical
  have hint : Integrable (fun t : ℝ => ‖principalLogWeight t‖ ^ 2) :=
    MemLp.integrable_norm_pow LogWeight457.principal_log_weight_memLp_two (by norm_num)
  have hhead : (∫ t in Set.Ioc 5 8, ‖principalLogWeight t‖ ^ 2)
      ≤ ∫ t in Set.Ioc 5 8, (2 * Real.log t + 3) ^ 2 / t ^ 2 :=
    setIntegral_mono_on hint.integrableOn tail_pos_majorant_integrableOn_head measurableSet_Ioc
      (fun t ht => tail_pos_pointwise_sq t (Set.mem_Ioc.mp ht).1)
  have hfar : (∫ t in Set.Ioi 8, ‖principalLogWeight t‖ ^ 2)
      ≤ ∫ t in Set.Ioi 8, (2 * Real.log t + 3) ^ 2 / t ^ 2 :=
    setIntegral_mono_on hint.integrableOn tail_pos_majorant_integrableOn_far measurableSet_Ioi
      (fun t ht => tail_pos_pointwise_sq t (by linarith [Set.mem_Ioi.mp ht]))
  rw [tail_pos_decomp]
  linarith [hhead, hfar, tail_pos_majorant_head_le, tail_pos_majorant_far_le]

end LeanLab.HelfgottMajor.Decomp457b
