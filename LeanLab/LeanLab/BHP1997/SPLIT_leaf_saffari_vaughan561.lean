/-
Independent split of the multiplicative window comparison after display 2.16.
The fixed additive window of half width T over 4 is compared with the
multiplicative windows of the printed z range. AI wrote the Lean code.
Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561d

namespace LeanLab.BHP1997.Decomp561d
open Classical Complex Thm2 MeasureTheory Set
open scoped ComplexConjugate

/-- The window integrand of the first leaf is interval integrable on every
interval. It is a finite sum of indicators of bounded intervals, so it is
measurable, and its modulus is bounded by the square of the sum of the
coefficient norms. -/
private lemma intervalIntegrable_window561 (Y T : ℝ) (b : ℕ → ℂ) (v : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (a c : ℝ) :
    IntervalIntegrable (fun y : ℝ =>
      ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4),
        centered561 Y b v χ m‖ ^ 2) volume a c := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound (C := (∑ m ∈ support561 Y, ‖centered561 Y b v χ m‖) ^ 2) ?_ ?_ ?_
  · rw [Set.uIoc]
    exact measure_Ioc_lt_top
  · apply Measurable.aestronglyMeasurable
    have hrewrite : (fun y : ℝ =>
        ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4),
          centered561 Y b v χ m‖ ^ 2)
        = fun y : ℝ =>
          ‖∑ m ∈ support561 Y,
            (if y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4
              then centered561 Y b v χ m else 0)‖ ^ 2 := by
      funext y
      rw [Finset.sum_filter]
    rw [hrewrite]
    have hinner : Measurable (fun y : ℝ =>
        ∑ m ∈ support561 Y,
          (if y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4
            then centered561 Y b v χ m else 0)) := by
      refine Finset.measurable_sum _ (fun m _ => ?_)
      have hset : MeasurableSet {y : ℝ | y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4} := by
        have h1 : MeasurableSet {y : ℝ | y - T / 4 ≤ (m : ℝ)} :=
          measurableSet_le (by fun_prop) measurable_const
        have h2 : MeasurableSet {y : ℝ | (m : ℝ) ≤ y + T / 4} :=
          measurableSet_le measurable_const (by fun_prop)
        exact h1.inter h2
      exact Measurable.ite hset measurable_const measurable_const
    exact (Measurable.norm hinner).pow_const 2
  · filter_upwards with y
    have hnn : (0 : ℝ) ≤ ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4),
      centered561 Y b v χ m‖ ^ 2 := by positivity
    rw [Real.norm_of_nonneg hnn]
    set B : ℝ := ∑ m ∈ support561 Y, ‖centered561 Y b v χ m‖ with hB
    have hle : ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4),
      centered561 Y b v χ m‖ ≤ B :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun x _ _ => norm_nonneg _))
    have hBnn : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have h1 : 0 ≤ B - ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4),
      centered561 Y b v χ m‖ := by linarith
    have h2 : 0 ≤ B + ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4),
      centered561 Y b v χ m‖ := add_nonneg hBnn (norm_nonneg _)
    nlinarith [mul_nonneg h1 h2]

/-- The covering count of the last leaf, the step its docstring leaves implicit.
With the step z0 = T over 6Y, which the printed range from T over 6Y to 6T over Y
contains, the geometric chain from any centre y of the translated interval reaches
the whole additive window of length T over 2 in twelve pieces, uniformly in y. -/
private lemma window_chain_reach561 {Y T y : ℝ} (hY : 1 ≤ Y) (hT : 0 < T) (hTY : T ≤ Y)
    (hy : Y / 2 ≤ y) :
    y + T / 2 ≤ y * (1 + T / (6 * Y)) ^ 12 := by
  have hYpos : (0 : ℝ) < Y := by linarith
  have hypos : (0 : ℝ) < y := by linarith
  have hbern : 1 + 12 * (T / (6 * Y)) ≤ (1 + T / (6 * Y)) ^ 12 := by
    have hz : (0 : ℝ) ≤ T / (6 * Y) := by positivity
    have h := one_add_mul_le_pow (a := T / (6 * Y)) (n := 12) (by linarith)
    simpa using h
  have htwelve : 12 * (T / (6 * Y)) = 2 * T / Y := by
    field_simp
    ring
  have hquot : T / 2 / y ≤ 2 * T / Y := by
    rw [div_le_div_iff₀ hypos hYpos]
    nlinarith [hT, hy]
  calc y + T / 2 = y * (1 + T / 2 / y) := by
        field_simp
    _ ≤ y * (1 + 2 * T / Y) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hypos)
        linarith
    _ = y * (1 + 12 * (T / (6 * Y))) := by rw [htwelve]
    _ ≤ y * (1 + T / (6 * Y)) ^ 12 :=
        mul_le_mul_of_nonneg_left hbern (le_of_lt hypos)

/-- The one piece of the tiling of the last leaf whose ratio is not z0. If a chain
point w sits at or above the bottom y of the additive window and the window still
reaches one step z0 beyond w, then the merged piece from w up to y plus T over 2 has
its ratio inside the printed range, so the hypothesis of the last leaf covers it. -/
private lemma window_top_piece561 {Y T y w : ℝ} (hY : 1 ≤ Y) (hT : 0 < T) (hTY : T ≤ Y)
    (hy : Y / 2 ≤ y) (hyw : y ≤ w) (hlo : w + w * (T / (6 * Y)) ≤ y + T / 2) :
    T / (6 * Y) ≤ (y + T / 2 - w) / w ∧ (y + T / 2 - w) / w ≤ 6 * T / Y := by
  have hYpos : (0 : ℝ) < Y := by linarith
  have hwpos : (0 : ℝ) < w := by linarith
  constructor
  · rw [le_div_iff₀ hwpos, mul_comm (T / (6 * Y)) w]
    linarith
  · rw [div_le_iff₀ hwpos, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < Y)]
    have h1 : (0 : ℝ) ≤ w - y := by linarith
    have h2 : (0 : ℝ) ≤ 6 * w - Y / 2 := by linarith
    nlinarith [mul_nonneg h1 (le_of_lt hYpos), mul_nonneg h2 (le_of_lt hT)]

/-- LEAF. First step of the comparison: the lower part of the y range carries no
fixed window at all. The short polynomial is supported above Y while the upper
end y plus T over 4 stays below Y once y is at most Y minus T over 4, so the
filtered sum vanishes there and only the truncated y interval remains. -/
theorem leaf_fixed_window_empty_below561 :
    ∀ Y T : ℝ, 1 ≤ Y → 0 < T → T ≤ Y →
      ∀ (b : ℕ → ℂ) (v : ℝ) (q : ℕ) (E : Finset (DirichletCharacter ℂ q)),
        fixedWindowMoment561 Y T b v q E =
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 4)..(3 * Y),
              ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4),
                centered561 Y b v χ m‖ ^ 2 := by
  intro Y T hY hT hTY b v q E
  have h1 : Y / 2 ≤ Y - T / 4 := by linarith
  have h2 : Y - T / 4 ≤ 3 * Y := by linarith
  simp only [fixedWindowMoment561]
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  set F : ℝ → ℝ := fun y =>
    ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4),
      centered561 Y b v χ m‖ ^ 2 with hF
  have hzero : ∀ y ∈ Set.uIoc (Y / 2) (Y - T / 4), F y = 0 := by
    intro y hy
    simp only [hF]
    rw [Set.uIoc_of_le h1] at hy
    have hyY : y ≤ Y - T / 4 := hy.2
    have hsum : (∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4),
        centered561 Y b v χ m) = 0 := by
      refine Finset.sum_eq_zero (fun m hm => ?_)
      exfalso
      obtain ⟨hms, hp1, hp2⟩ := Finset.mem_filter.mp hm
      have hfloor : (⌊Y⌋₊ : ℝ) < (m : ℝ) := by
        exact_mod_cast (Finset.mem_Ioc.mp hms).1
      have hsucc : (⌊Y⌋₊ : ℝ) + 1 ≤ (m : ℝ) := by
        have hs : ⌊Y⌋₊ + 1 ≤ m := Nat.succ_le_of_lt (Finset.mem_Ioc.mp hms).1
        exact_mod_cast hs
      have hlty : Y < (⌊Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Y
      have hmY : Y < (m : ℝ) := by linarith
      linarith
    rw [hsum]
    simp
  have hFint : ∀ a c : ℝ, IntervalIntegrable F volume a c := by
    intro a c
    rw [hF]
    exact intervalIntegrable_window561 Y T b v χ a c
  have hz : (∫ y in (Y / 2)..(Y - T / 4), F y) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with y hy
    exact hzero y hy
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hFint (Y / 2) (Y - T / 4)) (hFint (Y - T / 4) (3 * Y)), hz, zero_add]

/-- LEAF. Second step: the two sided fixed window of half width T over 4 is the
one sided window of length T over 2 read at the translated centre. Shifting the
y variable by T over 4 turns y minus T over 4 into y and y plus T over 4 into
y plus T over 2, so the truncated fixed window integral is the one sided window
integral over the translated interval. -/
theorem leaf_window_translation561 :
    ∀ Y T : ℝ, 1 ≤ Y → 0 < T → T ≤ Y →
      ∀ (b : ℕ → ℂ) (v : ℝ) (q : ℕ) (E : Finset (DirichletCharacter ℂ q)),
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 4)..(3 * Y),
              ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 4),
                centered561 Y b v χ m‖ ^ 2) =
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 2)..(3 * Y - T / 4),
              ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2),
                centered561 Y b v χ m‖ ^ 2 := by
  intro Y T hY hT hTY b v q E
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  set f : ℝ → ℝ := fun u =>
    ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => u - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ u + T / 4),
      centered561 Y b v χ m‖ ^ 2 with hf
  have hfil : ∀ x : ℝ,
      (support561 Y).filter
          (fun m : ℕ => (x + T / 4) - T / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ (x + T / 4) + T / 4)
        = (support561 Y).filter (fun m : ℕ => x ≤ (m : ℝ) ∧ (m : ℝ) ≤ x + T / 2) := by
    intro x
    congr 1
    funext m
    simp only [add_sub_cancel_right]
    have hshift : x + T / 4 + T / 4 = x + T / 2 := by ring
    rw [hshift]
  have hpt : ∀ x : ℝ,
      (‖∑ m ∈ (support561 Y).filter (fun m : ℕ => x ≤ (m : ℝ) ∧ (m : ℝ) ≤ x + T / 2),
        centered561 Y b v χ m‖ ^ 2) = f (x + T / 4) := by
    intro x
    simp only [hf]
    rw [hfil x]
  have hconv : (∫ x in (Y - T / 2)..(3 * Y - T / 4),
      ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => x ≤ (m : ℝ) ∧ (m : ℝ) ≤ x + T / 2),
        centered561 Y b v χ m‖ ^ 2) =
      ∫ x in (Y - T / 2)..(3 * Y - T / 4), f (x + T / 4) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact hpt x
  rw [hconv, intervalIntegral.integral_comp_add_right (f := f) (d := T / 4),
    show Y - T / 2 + T / 4 = Y - T / 4 by ring,
    show 3 * Y - T / 4 + T / 4 = 3 * Y by ring]

/-- LEAF. Third step: the one sided window of length T over 2 is the
multiplicative window of the printed shape with the parameter T over 2 y. On the
translated interval every centre y is positive, so y times T over 2 y is T over
2 and the two filtered sums agree term by term. -/
theorem leaf_window_parameter_scale561 :
    ∀ Y T : ℝ, 1 ≤ Y → 0 < T → T ≤ Y →
      ∀ (b : ℕ → ℂ) (v : ℝ) (q : ℕ) (E : Finset (DirichletCharacter ℂ q)),
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 2)..(3 * Y - T / 4),
              ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2),
                centered561 Y b v χ m‖ ^ 2) ≤
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 2)..(3 * Y - T / 4),
              ‖∑ m ∈ (support561 Y).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * (T / (2 * y))),
                centered561 Y b v χ m‖ ^ 2 := by
  intro Y T hY hT hTY b v q E
  refine Finset.sum_le_sum (fun χ _ => ?_)
  apply le_of_eq
  apply intervalIntegral.integral_congr
  intro y hy
  have hab : Y - T / 2 ≤ 3 * Y - T / 4 := by linarith
  rw [Set.uIcc_of_le hab] at hy
  have hypos : 0 < y := by linarith [hy.1]
  have hz : y * (T / (2 * y)) = T / 2 := by
    have hy0 : y ≠ 0 := ne_of_gt hypos
    field_simp
  simp only [hz]

/-- LEAF. Fourth step, the comparison itself: a nonnegative uniform bound M for
every multiplicative window whose parameter lies in the printed z range bounds
the translated additive window moment by a universal constant times M. The
parameter T over 2 y stays inside the printed range on the translated interval,
and the additive windows of length T over 2 are covered by finitely many
multiplicative windows of the family, so no pointwise choice of z and no
character dependent constant is needed. OPEN. -/
theorem leaf_multiplicative_windows_bound_diagonal561 :
    ∃ C : ℝ, 0 < C ∧ ∀ Y T : ℝ, 1 ≤ Y → 0 < T → T ≤ Y →
      ∀ (b : ℕ → ℂ) (v : ℝ) (q : ℕ) (E : Finset (DirichletCharacter ℂ q)) (M : ℝ),
        0 ≤ M →
        (∀ z : ℝ, T / (6 * Y) ≤ z → z ≤ 6 * T / Y →
          multiplicativeWindowMoment561 Y z b v q E ≤ M) →
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y - T / 2)..(3 * Y - T / 4),
              ‖∑ m ∈ (support561 Y).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * (T / (2 * y))),
                centered561 Y b v χ m‖ ^ 2) ≤
          C * M := by
  sorry

/-- The sealed target, assembled from the four leaves above. Step one drops the
empty lower half of the y range, step two translates the two sided fixed window
to the one sided window, step three rewrites its length as a multiplicative
parameter at the centre, and step four applies the multiplicative window bound.
The constant is the one supplied by the last leaf. -/
theorem leaf_saffari_vaughan561_split :
    ∃ V : ℝ, 0 < V ∧ ∀ Y T : ℝ, 1 ≤ Y → 0 < T → T ≤ Y →
      ∀ (b : ℕ → ℂ) (v : ℝ) (q : ℕ) (E : Finset (DirichletCharacter ℂ q)) (M : ℝ),
        0 ≤ M →
        (∀ z : ℝ, T / (6 * Y) ≤ z → z ≤ 6 * T / Y →
          multiplicativeWindowMoment561 Y z b v q E ≤ M) →
        fixedWindowMoment561 Y T b v q E ≤ V * M := by
  obtain ⟨C, hCpos, hC⟩ := leaf_multiplicative_windows_bound_diagonal561
  refine ⟨C, hCpos, ?_⟩
  intro Y T hY hT hTY b v q E M hM hmulti
  exact (leaf_fixed_window_empty_below561 Y T hY hT hTY b v q E).trans_le
    ((leaf_window_translation561 Y T hY hT hTY b v q E).trans_le
      ((leaf_window_parameter_scale561 Y T hY hT hTY b v q E).trans
        (hC Y T hY hT hTY b v q E M hM hmulti)))

end LeanLab.BHP1997.Decomp561d
