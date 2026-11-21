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

/-
Bricks for the Saffari-Vaughan transfer leaf `leaf_multiplicative_windows_bound_diagonal561`.

Strategy: the exact identity  f(y + T/2) - f(y) = A(y, z) - A(y + T/2, z'),  z' = (z y - T/2)/(y + T/2),
with `A(u, w) = sum_{u <= m <= u(1+w)} c_m`, holds for every `z`; averaging it over `z in [D, 2D]`
with `D = 3T/(2Y)` and substituting `w = z'` turns the second term into an integral over the fixed
printed range `[T/(6Y), 6T/Y]`, at the cost of the Jacobian `(y + T/2)/y <= 2`.  Range conditions are
`zp_lower561` / `zp_upper561`; the resulting constant is `2 + 4 * (35/9) = 158/9 <= 18`.
Everything up to the final assembly (`saffari_core561`) is proved below.
-/
/-- The shifted parameter `z' = (z y - T/2) / (y + T/2)` is at least `T/(6Y)`. -/
private lemma zp_lower561 {Y T y z : ℝ} (hT : 0 < T) (hTY : T ≤ Y)
    (hy : Y / 2 ≤ y) (hz : 3 * T / (2 * Y) ≤ z) :
    T / (6 * Y) ≤ (z * y - T / 2) / (y + T / 2) := by
  have hYpos : (0 : ℝ) < Y := by linarith
  have hden : (0 : ℝ) < y + T / 2 := by linarith
  have hA : 9 * T * y ≤ 6 * Y * (z * y) := by
    have h1 : (3 * T / (2 * Y)) * y ≤ z * y :=
      mul_le_mul_of_nonneg_right hz (by linarith)
    have h2 : 6 * Y * ((3 * T / (2 * Y)) * y) = 9 * T * y := by
      field_simp
      ring
    nlinarith [h1, h2]
  have hC : 4 * T * Y ≤ 8 * T * y := by nlinarith
  have hD : T ^ 2 / 2 ≤ T * Y := by nlinarith
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 6 * Y) hden]
  nlinarith [hA, hC, hD]

/-- The shifted parameter is at most `6T/Y`. -/
private lemma zp_upper561 {Y T y z : ℝ} (hT : 0 < T) (hY : 1 ≤ Y)
    (hy : 0 < y) (hz : z ≤ 3 * T / Y) :
    (z * y - T / 2) / (y + T / 2) ≤ 6 * T / Y := by
  have hYpos : (0 : ℝ) < Y := by linarith
  have hden : (0 : ℝ) < y + T / 2 := by linarith
  have h1 : z * y ≤ (3 * T / Y) * y := mul_le_mul_of_nonneg_right hz (by linarith)
  have h1' : z * y * Y ≤ 3 * T * y := by
    have h := mul_le_mul_of_nonneg_right h1 (le_of_lt hYpos)
    have e : 3 * T / Y * y * Y = 3 * T * y := by field_simp
    linarith [h, e]
  rw [div_le_div_iff₀ hden hYpos]
  nlinarith [h1', hT, hYpos, hden]

section StageB

/-- `D = 3T/(2Y)` is positive. -/
private lemma hD_pos561 {Y T : ℝ} (hT : 0 < T) (hY : 1 ≤ Y) : 0 < 3 * T / (2 * Y) := by
  have : (0:ℝ) < Y := by linarith
  positivity

/-- `D` is above the bottom of the printed range. -/
private lemma hD_low561 {Y T : ℝ} (hT : 0 < T) (hY : 1 ≤ Y) :
    T / (6 * Y) ≤ 3 * T / (2 * Y) := by
  have hYpos : (0:ℝ) < Y := by linarith
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 6 * Y) (by positivity : (0:ℝ) < 2 * Y)]
  nlinarith

/-- Twice `D` is below the top of the printed range. -/
private lemma hD_high561 {Y T : ℝ} (hT : 0 < T) (hY : 1 ≤ Y) :
    2 * (3 * T / (2 * Y)) ≤ 6 * T / Y := by
  have hYpos : (0:ℝ) < Y := by linarith
  have e : 2 * (3 * T / (2 * Y)) = 3 * T / Y := by field_simp
  rw [e, div_le_div_iff₀ hYpos hYpos]
  nlinarith

/-- The shift is available: `T/2 ≤ y * z` for `y ≥ Y/2` and `z ≥ D`. -/
private lemma hshift561 {Y T y z : ℝ} (hT : 0 < T) (hTY : T ≤ Y)
    (hy : Y / 2 ≤ y) (hz : 3 * T / (2 * Y) ≤ z) :
    T / 2 ≤ y * z := by
  have hYpos : (0:ℝ) < Y := by linarith
  have h1 : Y / 2 * (3 * T / (2 * Y)) ≤ y * z :=
    mul_le_mul hy hz (by positivity) (by linarith)
  have e : Y / 2 * (3 * T / (2 * Y)) = 3 * T / 4 := by field_simp; ring
  rw [e] at h1
  linarith

/-- The defining identity of the shifted parameter. -/
private lemma hzp_def561 {Y T y z : ℝ} (hy : 0 < y) (hT : 0 < T) :
    (y + T / 2) * (1 + (z * y - T / 2) / (y + T / 2)) = y * (1 + z) := by
  have hden : (0:ℝ) < y + T / 2 := by linarith
  field_simp
  ring

end StageB

section StageC

/-- The multiplicative window integrand is interval integrable on every interval. -/
private lemma intervalIntegrable_gen561 (Y z a c : ℝ) (g : ℕ → ℂ) :
    IntervalIntegrable (fun y : ℝ =>
      ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
      volume a c := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound (C := (∑ m ∈ support561 Y, ‖g m‖) ^ 2) ?_ ?_ ?_
  · rw [Set.uIoc]
    exact measure_Ioc_lt_top
  · apply Measurable.aestronglyMeasurable
    have hrewrite : (fun y : ℝ =>
        ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
        = fun y : ℝ =>
          ‖∑ m ∈ support561 Y, (if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z) then g m else 0)‖ ^ 2 := by
      funext y
      rw [Finset.sum_filter]
    rw [hrewrite]
    have hinner : Measurable (fun y : ℝ =>
        ∑ m ∈ support561 Y,
          (if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z) then g m else 0)) := by
      refine Finset.measurable_sum _ (fun m _ => ?_)
      have hset : MeasurableSet {y : ℝ | y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)} := by
        have h1 : MeasurableSet {y : ℝ | y ≤ (m : ℝ)} :=
          measurableSet_le measurable_id measurable_const
        have h2 : MeasurableSet {y : ℝ | (m : ℝ) ≤ y * (1 + z)} :=
          measurableSet_le measurable_const (by fun_prop)
        exact h1.inter h2
      exact Measurable.ite hset measurable_const measurable_const
    exact (Measurable.norm hinner).pow_const 2
  · filter_upwards with y
    have hnn : (0 : ℝ) ≤ ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2 := by positivity
    rw [Real.norm_of_nonneg hnn]
    set B : ℝ := ∑ m ∈ support561 Y, ‖g m‖ with hB
    have hle : ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ≤ B :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun x _ _ => norm_nonneg _))
    have hBnn : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have h1 : 0 ≤ B - ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ := by linarith
    have h2 : 0 ≤ B + ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ :=
      add_nonneg hBnn (norm_nonneg _)
    nlinarith [mul_nonneg h1 h2]

end StageC

section StageD

/-- Splitting a fixed window at `y + T/2`: away from the integer points where `y + T/2`
is an integer, the fixed window is the difference of the multiplicative window at `z`
and the multiplicative window at `z` read from `y + T/2`. -/
private lemma window_split561 {Y T y z : ℝ} (hT : 0 < T) (hy : 0 < y)
    (hint : ∀ n : ℤ, y + T / 2 ≠ (n : ℝ)) (hshift : T / 2 ≤ y * z) (g : ℕ → ℂ) :
    (∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m) =
      (∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m) -
      (∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y + T / 2 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m) := by
  have htop : y + T / 2 ≤ y * (1 + z) := by nlinarith
  have hP2sub : (support561 Y).filter
        (fun m : ℕ => y + T / 2 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)) ⊆
      (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)) := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, by linarith [hm.2.1], hm.2.2⟩
  have hEq : (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)) \
        (support561 Y).filter (fun m : ℕ => y + T / 2 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)) =
      (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2) := by
    ext m
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hmS, h1, h2⟩, hnot⟩
      refine ⟨hmS, h1, ?_⟩
      by_contra hcon
      rw [not_le] at hcon
      exact hnot ⟨hmS, le_of_lt hcon, h2⟩
    · rintro ⟨hmS, h1, h3⟩
      refine ⟨⟨hmS, h1, by linarith⟩, ?_⟩
      rintro ⟨h4, _⟩
      exact hint m (by rw [Int.cast_natCast]; linarith)
  have hsdiff := Finset.sum_sdiff hP2sub (f := g)
  rw [hEq] at hsdiff
  rw [← hsdiff]
  ring

/-- The two term bound. -/
private lemma window_two_term561 {Y T y z : ℝ} (hT : 0 < T) (hy : 0 < y)
    (hint : ∀ n : ℤ, y + T / 2 ≠ (n : ℝ)) (hshift : T / 2 ≤ y * z) (g : ℕ → ℂ) :
    ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2 ≤
      2 * ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2 +
      2 * ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => y + T / 2 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2 := by
  set A1 : ℂ := ∑ m ∈ (support561 Y).filter
    (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m with hA1
  set A2 : ℂ := ∑ m ∈ (support561 Y).filter
    (fun m : ℕ => y + T / 2 ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m with hA2
  have hsplit : (∑ m ∈ (support561 Y).filter
      (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m) = A1 - A2 :=
    window_split561 hT hy hint hshift g
  rw [hsplit]
  have h1 : ‖A1 - A2‖ ≤ ‖A1‖ + ‖A2‖ := norm_sub_le _ _
  have h2 : (‖A1‖ + ‖A2‖) ^ 2 ≤ 2 * ‖A1‖ ^ 2 + 2 * ‖A2‖ ^ 2 := by
    nlinarith [sq_nonneg (‖A1‖ - ‖A2‖), norm_nonneg A1, norm_nonneg A2]
  calc ‖A1 - A2‖ ^ 2 ≤ (‖A1‖ + ‖A2‖) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _) h1
    _ ≤ 2 * ‖A1‖ ^ 2 + 2 * ‖A2‖ ^ 2 := h2

end StageD

section StageE

/-- The two dimensional multiplicative window integrand is integrable on every bounded
rectangle.  `sh` shifts the centre, which lets the same statement serve the window read
from `y` and the window read from `y + T/2`. -/
private lemma integrableOn_gen2d561 (Y sh : ℝ) (g : ℕ → ℂ) (a b c d : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ =>
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => p.1 + sh ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)), g m‖ ^ 2)
      (Set.uIoc a b ×ˢ Set.uIoc c d) (volume.prod volume) := by
  refine IntegrableOn.of_bound (C := (∑ m ∈ support561 Y, ‖g m‖) ^ 2) ?_ ?_ ?_
  · rcases le_total a b with hab | hab
    · rw [Set.uIoc_of_le hab, Measure.prod_prod]
      exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioc_lt_top
    · rw [Set.uIoc_of_ge hab, Measure.prod_prod]
      exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioc_lt_top
  · apply Measurable.aestronglyMeasurable
    have hrewrite : (fun p : ℝ × ℝ =>
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => p.1 + sh ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)), g m‖ ^ 2)
        = fun p : ℝ × ℝ =>
          ‖∑ m ∈ support561 Y,
            (if p.1 + sh ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2) then g m else 0)‖ ^ 2 := by
      funext p
      rw [Finset.sum_filter]
    rw [hrewrite]
    have hinner : Measurable (fun p : ℝ × ℝ =>
        ∑ m ∈ support561 Y,
          (if p.1 + sh ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2) then g m else 0)) := by
      refine Finset.measurable_sum _ (fun m _ => ?_)
      have hset : MeasurableSet
          {p : ℝ × ℝ | p.1 + sh ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)} := by
        have h1 : MeasurableSet {p : ℝ × ℝ | p.1 + sh ≤ (m : ℝ)} :=
          measurableSet_le (by fun_prop) measurable_const
        have h2 : MeasurableSet {p : ℝ × ℝ | (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)} :=
          measurableSet_le measurable_const (by fun_prop)
        exact h1.inter h2
      exact Measurable.ite hset measurable_const measurable_const
    exact (Measurable.norm hinner).pow_const 2
  · filter_upwards with p
    have hnn : (0 : ℝ) ≤ ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 + sh ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)), g m‖ ^ 2 := by
      positivity
    rw [Real.norm_of_nonneg hnn]
    set B : ℝ := ∑ m ∈ support561 Y, ‖g m‖ with hB
    have hle : ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 + sh ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)), g m‖ ≤ B :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun x _ _ => norm_nonneg _))
    have hBnn : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have h1 : 0 ≤ B - ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 + sh ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)), g m‖ := by
      linarith
    have h2 : 0 ≤ B + ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 + sh ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)), g m‖ :=
      add_nonneg hBnn (norm_nonneg _)
    nlinarith [mul_nonneg h1 h2]

end StageE

section StageC2

/-- The fixed window integrand is interval integrable on every interval. -/
private lemma intervalIntegrable_fixed561 (Y T a c : ℝ) (g : ℕ → ℂ) :
    IntervalIntegrable (fun y : ℝ =>
      ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
      volume a c := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound (C := (∑ m ∈ support561 Y, ‖g m‖) ^ 2) ?_ ?_ ?_
  · rw [Set.uIoc]
    exact measure_Ioc_lt_top
  · apply Measurable.aestronglyMeasurable
    have hrewrite : (fun y : ℝ =>
        ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
        = fun y : ℝ =>
          ‖∑ m ∈ support561 Y, (if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2 then g m else 0)‖ ^ 2 := by
      funext y
      rw [Finset.sum_filter]
    rw [hrewrite]
    have hinner : Measurable (fun y : ℝ =>
        ∑ m ∈ support561 Y,
          (if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2 then g m else 0)) := by
      refine Finset.measurable_sum _ (fun m _ => ?_)
      have hset : MeasurableSet {y : ℝ | y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2} := by
        have h1 : MeasurableSet {y : ℝ | y ≤ (m : ℝ)} :=
          measurableSet_le measurable_id measurable_const
        have h2 : MeasurableSet {y : ℝ | (m : ℝ) ≤ y + T / 2} :=
          measurableSet_le measurable_const (by fun_prop)
        exact h1.inter h2
      exact Measurable.ite hset measurable_const measurable_const
    exact (Measurable.norm hinner).pow_const 2
  · filter_upwards with y
    have hnn : (0 : ℝ) ≤ ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2 := by positivity
    rw [Real.norm_of_nonneg hnn]
    set B : ℝ := ∑ m ∈ support561 Y, ‖g m‖ with hB
    have hle : ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ≤ B :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun x _ _ => norm_nonneg _))
    have hBnn : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have h1 : 0 ≤ B - ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ := by linarith
    have h2 : 0 ≤ B + ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ :=
      add_nonneg hBnn (norm_nonneg _)
    nlinarith [mul_nonneg h1 h2]

/-- A nonnegative integrand has the interval integral monotone in the interval. -/
private lemma integral_le_of_subinterval561 {f : ℝ → ℝ}
    (hf : ∀ a c, IntervalIntegrable f volume a c) (hnn : ∀ x, 0 ≤ f x) {a b c d : ℝ}
    (h1 : a ≤ c) (h2 : c ≤ b) (h3 : b ≤ d) :
    (∫ x in c..b, f x) ≤ ∫ x in a..d, f x := by
  have e1 : (∫ x in a..d, f x) = (∫ x in a..c, f x) + (∫ x in c..d, f x) :=
    (intervalIntegral.integral_add_adjacent_intervals (hf a c) (hf c d)).symm
  have e2 : (∫ x in c..d, f x) = (∫ x in c..b, f x) + (∫ x in b..d, f x) :=
    (intervalIntegral.integral_add_adjacent_intervals (hf c b) (hf b d)).symm
  have h0a : 0 ≤ ∫ x in a..c, f x := intervalIntegral.integral_nonneg h1 (fun u _ => hnn u)
  have h0b : 0 ≤ ∫ x in b..d, f x := intervalIntegral.integral_nonneg h3 (fun u _ => hnn u)
  linarith

end StageC2

section StageG

private lemma integral_rect_prod561 (F : ℝ × ℝ → ℝ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hF : IntegrableOn F (Set.uIoc a b ×ˢ Set.uIoc c d) (volume.prod volume)) :
    ∫ p in Set.uIoc a b ×ˢ Set.uIoc c d, F p = ∫ y in a..b, ∫ z in c..d, F (y, z) := by
  have h1 := MeasureTheory.setIntegral_prod (μ := volume) (ν := volume) F hF
  refine h1.trans ?_
  have hIoc : ∀ y : ℝ, (∫ z in Set.uIoc c d, F (y, z)) = ∫ z in c..d, F (y, z) := fun y => by
    rw [intervalIntegral.integral_of_le (f := fun z => F (y, z)) hcd, Set.uIoc_of_le hcd]
  rw [show Set.uIoc a b = Set.Ioc a b from Set.uIoc_of_le hab]
  simp only [hIoc]
  exact (intervalIntegral.integral_of_le (a := a) (b := b)
    (f := fun y => ∫ z in c..d, F (y, z)) hab).symm

private lemma integrand_sm2d561 (Y sh : ℝ) (g : ℕ → ℂ) :
    StronglyMeasurable (fun p : ℝ × ℝ =>
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + sh) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)), g m‖ ^ 2) := by
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + sh) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)), g m‖ ^ 2) := by
    have hrewrite : (fun p : ℝ × ℝ =>
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (p.1 + sh) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)), g m‖ ^ 2)
        = fun p : ℝ × ℝ =>
          ‖∑ m ∈ support561 Y,
            (if (p.1 + sh) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2) then g m else 0)‖ ^ 2 := by
      funext p
      rw [Finset.sum_filter]
    rw [hrewrite]
    have hinner : Measurable (fun p : ℝ × ℝ =>
        ∑ m ∈ support561 Y,
          (if (p.1 + sh) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2) then g m else 0)) := by
      refine Finset.measurable_sum _ (fun m _ => ?_)
      have hset : MeasurableSet
          {p : ℝ × ℝ | (p.1 + sh) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)} := by
        have h1 : MeasurableSet {p : ℝ × ℝ | (p.1 + sh) ≤ (m : ℝ)} :=
          measurableSet_le (by fun_prop) measurable_const
        have h2 : MeasurableSet {p : ℝ × ℝ | (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)} :=
          measurableSet_le measurable_const (by fun_prop)
        exact h1.inter h2
      exact Measurable.ite hset measurable_const measurable_const
    exact (Measurable.norm hinner).pow_const 2
  exact hmeas.stronglyMeasurable

private lemma integrand_bound2d561 (Y sh : ℝ) (g : ℕ → ℂ) (p : ℝ × ℝ) :
    ‖‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + sh) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)), g m‖ ^ 2‖
      ≤ (∑ m ∈ support561 Y, ‖g m‖) ^ 2 := by
  have hnn : (0:ℝ) ≤ ‖∑ m ∈ (support561 Y).filter
      (fun m : ℕ => (p.1 + sh) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)), g m‖ ^ 2 := by
    positivity
  rw [Real.norm_of_nonneg hnn]
  set B : ℝ := ∑ m ∈ support561 Y, ‖g m‖ with hB
  have hle : ‖∑ m ∈ (support561 Y).filter
      (fun m : ℕ => (p.1 + sh) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)), g m‖ ≤ B :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun x _ _ => norm_nonneg _))
  have hBnn : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have h1 : 0 ≤ B - ‖∑ m ∈ (support561 Y).filter
      (fun m : ℕ => (p.1 + sh) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)), g m‖ := by linarith
  have h2 : 0 ≤ B + ‖∑ m ∈ (support561 Y).filter
      (fun m : ℕ => (p.1 + sh) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)), g m‖ :=
    add_nonneg hBnn (norm_nonneg _)
  nlinarith [mul_nonneg h1 h2]

private lemma intervalIntegrable_param561 (Y sh : ℝ) (g : ℕ → ℂ) {a b c d : ℝ} (hcd : c ≤ d) :
    IntervalIntegrable (fun y : ℝ => ∫ w in c..d,
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + sh) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (y + sh) * (1 + w)), g m‖ ^ 2)
      volume a b := by
  set F : ℝ × ℝ → ℝ := fun p =>
    ‖∑ m ∈ (support561 Y).filter
      (fun m : ℕ => (p.1 + sh) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (p.1 + sh) * (1 + p.2)), g m‖ ^ 2 with hFdef
  have hFsm : StronglyMeasurable F := integrand_sm2d561 Y sh g
  have hFb : ∀ p : ℝ × ℝ, ‖F p‖ ≤ (∑ m ∈ support561 Y, ‖g m‖) ^ 2 := integrand_bound2d561 Y sh g
  set C : ℝ := (∑ m ∈ support561 Y, ‖g m‖) ^ 2 with hCdef
  have hsm : StronglyMeasurable (fun y : ℝ => ∫ w in c..d, F (y, w)) := by
    have hEq : (fun y : ℝ => ∫ w in c..d, F (y, w))
        = fun y => ∫ w, (Set.Ioc c d).indicator (fun w => F (y, w)) w := by
      funext y
      rw [intervalIntegral.integral_of_le (f := fun w => F (y, w)) hcd,
        ← MeasureTheory.integral_indicator measurableSet_Ioc]
    rw [hEq]
    have hpt : StronglyMeasurable (fun p : ℝ × ℝ =>
        (Set.Ioc c d).indicator (fun w => F (p.1, w)) p.2) := by
      have hEq2 : (fun p : ℝ × ℝ => (Set.Ioc c d).indicator (fun w => F (p.1, w)) p.2)
          = ((Set.univ : Set ℝ) ×ˢ Set.Ioc c d).indicator F := by
        funext p
        by_cases hp : p.2 ∈ Set.Ioc c d
        · have hp' : p ∈ (Set.univ : Set ℝ) ×ˢ Set.Ioc c d := ⟨trivial, hp⟩
          rw [Set.indicator_of_mem hp', Set.indicator_of_mem hp]
        · have hp' : p ∉ (Set.univ : Set ℝ) ×ˢ Set.Ioc c d := fun h => hp h.2
          rw [Set.indicator_of_notMem hp', Set.indicator_of_notMem hp]
      rw [hEq2]
      exact hFsm.indicator (MeasurableSet.univ.prod measurableSet_Ioc)
    exact hpt.integral_prod_right'
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound (C := C * (d - c)) ?_ hsm.aestronglyMeasurable ?_
  · rw [Set.uIoc]
    exact measure_Ioc_lt_top
  · filter_upwards with y
    have h2 : (0:ℝ) ≤ ∫ w in c..d, F (y, w) :=
      intervalIntegral.integral_nonneg hcd (fun w _ => by positivity)
    rw [Real.norm_of_nonneg h2]
    have h3 := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := d) (C := C)
      (f := fun w => F (y, w)) (fun w _ => hFb (y, w))
    rwa [Real.norm_of_nonneg h2, abs_of_nonneg (by linarith : (0:ℝ) ≤ d - c)] at h3

end StageG

section StageH

/-- Parameter integrability: the inner integral over the second variable is interval
integrable in the first variable, on a rectangle where the integrand is bounded. -/
private lemma intervalIntegrable_param2d561 (F : ℝ × ℝ → ℝ) (hF : StronglyMeasurable F)
    {a b c d C : ℝ} (hcd : c ≤ d) (hbd : ∀ y ∈ Set.uIoc a b, ∀ w, ‖F (y, w)‖ ≤ C) :
    IntervalIntegrable (fun y : ℝ => ∫ w in c..d, F (y, w)) volume a b := by
  have hsm : StronglyMeasurable (fun y : ℝ => ∫ w in c..d, F (y, w)) := by
    have hEq : (fun y : ℝ => ∫ w in c..d, F (y, w))
        = fun y => ∫ w, (Set.Ioc c d).indicator (fun w => F (y, w)) w := by
      funext y
      rw [intervalIntegral.integral_of_le (f := fun w => F (y, w)) hcd,
        ← MeasureTheory.integral_indicator measurableSet_Ioc]
    rw [hEq]
    have hpt : StronglyMeasurable (fun p : ℝ × ℝ =>
        (Set.Ioc c d).indicator (fun w => F (p.1, w)) p.2) := by
      have hEq2 : (fun p : ℝ × ℝ => (Set.Ioc c d).indicator (fun w => F (p.1, w)) p.2)
          = ((Set.univ : Set ℝ) ×ˢ Set.Ioc c d).indicator F := by
        funext p
        by_cases hp : p.2 ∈ Set.Ioc c d
        · have hp' : p ∈ (Set.univ : Set ℝ) ×ˢ Set.Ioc c d := ⟨trivial, hp⟩
          rw [Set.indicator_of_mem hp', Set.indicator_of_mem hp]
        · have hp' : p ∉ (Set.univ : Set ℝ) ×ˢ Set.Ioc c d := fun h => hp h.2
          rw [Set.indicator_of_notMem hp', Set.indicator_of_notMem hp]
      rw [hEq2]
      exact hF.indicator (MeasurableSet.univ.prod measurableSet_Ioc)
    exact hpt.integral_prod_right'
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound (C := C * (d - c)) ?_ hsm.aestronglyMeasurable ?_
  · rw [Set.uIoc]
    exact measure_Ioc_lt_top
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with y hy
    have h3 := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := d) (C := C)
      (f := fun w => F (y, w)) (fun w _ => hbd y hy w)
    rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ d - c)] at h3

/-- The same in the other orientation: the inner integral over the first variable is
interval integrable in the second variable. -/
private lemma intervalIntegrable_param2d_swap561 (F : ℝ × ℝ → ℝ) (hF : StronglyMeasurable F)
    {a b c d C : ℝ} (hab : a ≤ b) (hbd : ∀ z ∈ Set.uIoc c d, ∀ y, ‖F (y, z)‖ ≤ C) :
    IntervalIntegrable (fun z : ℝ => ∫ y in a..b, F (y, z)) volume c d := by
  have hF' : StronglyMeasurable (fun p : ℝ × ℝ => F (p.2, p.1)) :=
    hF.comp_measurable measurable_swap
  have h := intervalIntegrable_param2d561 (fun p : ℝ × ℝ => F (p.2, p.1)) hF' (a := c) (b := d)
    (c := a) (d := b) (C := C) hab (fun z hz y => hbd z hz y)
  simpa only [Function.comp_apply] using h

/-- The raw mixed window integrand is integrable on every bounded rectangle. -/
private lemma integrableOn_B2d561 (Y T : ℝ) (g : ℕ → ℂ) (a b c d : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ =>
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
      (Set.uIoc a b ×ˢ Set.uIoc c d) (volume.prod volume) := by
  refine IntegrableOn.of_bound (C := (∑ m ∈ support561 Y, ‖g m‖) ^ 2) ?_ ?_ ?_
  · rcases le_total a b with hab | hab
    · rw [Set.uIoc_of_le hab, Measure.prod_prod]
      exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioc_lt_top
    · rw [Set.uIoc_of_ge hab, Measure.prod_prod]
      exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioc_lt_top
  · apply Measurable.aestronglyMeasurable
    have hrewrite : (fun p : ℝ × ℝ =>
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
        = fun p : ℝ × ℝ =>
          ‖∑ m ∈ support561 Y,
            (if (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2) then g m else 0)‖ ^ 2 := by
      funext p
      rw [Finset.sum_filter]
    rw [hrewrite]
    have hinner : Measurable (fun p : ℝ × ℝ =>
        ∑ m ∈ support561 Y,
          (if (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2) then g m else 0)) := by
      refine Finset.measurable_sum _ (fun m _ => ?_)
      have hset : MeasurableSet
          {p : ℝ × ℝ | (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)} := by
        have h1 : MeasurableSet {p : ℝ × ℝ | (p.1 + T / 2) ≤ (m : ℝ)} :=
          measurableSet_le (by fun_prop) measurable_const
        have h2 : MeasurableSet {p : ℝ × ℝ | (m : ℝ) ≤ p.1 * (1 + p.2)} :=
          measurableSet_le measurable_const (by fun_prop)
        exact h1.inter h2
      exact Measurable.ite hset measurable_const measurable_const
    exact (Measurable.norm hinner).pow_const 2
  · filter_upwards with p
    have hnn : (0 : ℝ) ≤ ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2 := by
      positivity
    rw [Real.norm_of_nonneg hnn]
    set B : ℝ := ∑ m ∈ support561 Y, ‖g m‖ with hB
    have hle : ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ≤ B :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun x _ _ => norm_nonneg _))
    have hBnn : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have h1 : 0 ≤ B - ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ := by linarith
    have h2 : 0 ≤ B + ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ :=
      add_nonneg hBnn (norm_nonneg _)
    nlinarith [mul_nonneg h1 h2]

end StageH

section StageI

/-- The substitution `w = (z y - T/2)/(y + T/2)` at a fixed centre `y > 0`. -/
private lemma integral_comp_zp561 {T y : ℝ} (hT : 0 < T) (hy : 0 < y) (F : ℝ → ℝ) (a b : ℝ) :
    (∫ z in a..b, F ((z * y - T / 2) / (y + T / 2)))
      = ((y + T / 2) / y) *
        ∫ w in ((a * y - T / 2) / (y + T / 2))..((b * y - T / 2) / (y + T / 2)), F w := by
  have hden : (0:ℝ) < y + T / 2 := by linarith
  have hc : (y / (y + T / 2)) ≠ 0 := by positivity
  have key := intervalIntegral.integral_comp_mul_add (f := F) (a := a) (b := b)
    (c := y / (y + T / 2)) (d := -(T / 2) / (y + T / 2)) hc
  have hy : ((y / (y + T / 2))⁻¹ : ℝ) = (y + T / 2) / y := by
    rw [inv_div]
  rw [hy] at key
  have harg : ∀ z : ℝ, y / (y + T / 2) * z + -(T / 2) / (y + T / 2)
      = (z * y - T / 2) / (y + T / 2) := by
    intro z
    field_simp
    ring
  simp only [harg] at key
  rw [key]
  norm_num [smul_eq_mul]

/-- The shifted parameter is monotone in `z`. -/
private lemma zp_mono561 {T y : ℝ} (hT : 0 < T) (hy : 0 < y) {z z' : ℝ} (h : z ≤ z') :
    (z * y - T / 2) / (y + T / 2) ≤ (z' * y - T / 2) / (y + T / 2) := by
  have hden : (0:ℝ) < y + T / 2 := by linarith
  apply div_le_div_of_nonneg_right _ (le_of_lt hden)
  nlinarith

end StageI

section StageJ

/-- The window integrand with a **fixed centre** is interval integrable in the parameter. -/
private lemma intervalIntegrable_param561b (Y u a c : ℝ) (g : ℕ → ℂ) :
    IntervalIntegrable (fun w : ℝ =>
      ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u * (1 + w)), g m‖ ^ 2)
      volume a c := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound (C := (∑ m ∈ support561 Y, ‖g m‖) ^ 2) ?_ ?_ ?_
  · rw [Set.uIoc]
    exact measure_Ioc_lt_top
  · apply Measurable.aestronglyMeasurable
    have hrewrite : (fun w : ℝ =>
        ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u * (1 + w)), g m‖ ^ 2)
        = fun w : ℝ =>
          ‖∑ m ∈ support561 Y, (if u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u * (1 + w) then g m else 0)‖ ^ 2 := by
      funext w
      rw [Finset.sum_filter]
    rw [hrewrite]
    have hinner : Measurable (fun w : ℝ =>
        ∑ m ∈ support561 Y, (if u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u * (1 + w) then g m else 0)) := by
      refine Finset.measurable_sum _ (fun m _ => ?_)
      have hset : MeasurableSet {w : ℝ | u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u * (1 + w)} := by
        have h1 : MeasurableSet {w : ℝ | u ≤ (m : ℝ)} :=
          measurableSet_le measurable_const measurable_const
        have h2 : MeasurableSet {w : ℝ | (m : ℝ) ≤ u * (1 + w)} :=
          measurableSet_le measurable_const (by fun_prop)
        exact h1.inter h2
      exact Measurable.ite hset measurable_const measurable_const
    exact (Measurable.norm hinner).pow_const 2
  · filter_upwards with w
    have hnn : (0 : ℝ) ≤ ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u * (1 + w)), g m‖ ^ 2 := by positivity
    rw [Real.norm_of_nonneg hnn]
    set B : ℝ := ∑ m ∈ support561 Y, ‖g m‖ with hB
    have hle : ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u * (1 + w)), g m‖ ≤ B :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun x _ _ => norm_nonneg _))
    have hBnn : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have h1 : 0 ≤ B - ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u * (1 + w)), g m‖ := by linarith
    have h2 : 0 ≤ B + ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u * (1 + w)), g m‖ :=
      add_nonneg hBnn (norm_nonneg _)
    nlinarith [mul_nonneg h1 h2]

/-- Step (ii) of the `B` bound: at a fixed centre inside `[Y/2, 2Y]`, the window with the
shifted parameter is dominated by the window over the printed `z` range. -/
private lemma B_le_shifted561 (Y T : ℝ) (hY : 1 ≤ Y) (hT : 0 < T) (hTY : T ≤ Y)
    (g : ℕ → ℂ) {y : ℝ} (hy1 : Y / 2 ≤ y) (hy2 : y ≤ 2 * Y) :
    (∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
      ≤ ((y + T / 2) / y) *
        (∫ w in (T / (6 * Y))..(6 * T / Y),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2) := by
  have hypos : 0 < y := by linarith
  have hstep : (∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
      = ∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
          (fun w : ℝ => ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2) ((z * y - T / 2) / (y + T / 2)) := by
    apply intervalIntegral.integral_congr
    intro z _
    dsimp only
    have h1 : y * (1 + z) = (y + T / 2) * (1 + ((z * y - T / 2) / (y + T / 2))) := by
      have hden : (0:ℝ) < y + T / 2 := by linarith
      field_simp
      ring
    rw [h1]
  rw [hstep]
  rw [integral_comp_zp561 (T := T) hT hypos
    (fun w : ℝ => ‖∑ m ∈ (support561 Y).filter
      (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2)
    (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hmono : ((3 * T / (2 * Y)) * y - T / 2) / (y + T / 2)
      ≤ ((2 * (3 * T / (2 * Y))) * y - T / 2) / (y + T / 2) := by
    apply zp_mono561 hT hypos
    have hD : (0:ℝ) < 3 * T / (2 * Y) := hD_pos561 hT hY
    linarith
  have hz2 : 2 * (3 * T / (2 * Y)) ≤ 3 * T / Y := by
    have e : 2 * (3 * T / (2 * Y)) = 3 * T / Y := by field_simp
    rw [e]
  exact integral_le_of_subinterval561
    (f := fun w : ℝ => ‖∑ m ∈ (support561 Y).filter
      (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2)
    (fun a c => intervalIntegrable_param561b Y (y + T / 2) a c g) (fun w => by positivity)
    (zp_lower561 (Y := Y) (T := T) (y := y) (z := 3 * T / (2 * Y)) hT hTY hy1
      (le_refl _)) hmono (zp_upper561 (Y := Y) (T := T) (y := y)
      (z := 2 * (3 * T / (2 * Y))) hT hY hypos hz2)

end StageJ

section StageK

/-- Measurability of the raw mixed window integrand in the pair `(centre, parameter)`. -/
private lemma integrand_sm_B561 (Y T : ℝ) (g : ℕ → ℂ) :
    StronglyMeasurable (fun p : ℝ × ℝ =>
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2) := by
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2) := by
    have hrewrite : (fun p : ℝ × ℝ =>
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
        = fun p : ℝ × ℝ =>
          ‖∑ m ∈ support561 Y,
            (if (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2) then g m else 0)‖ ^ 2 := by
      funext p
      rw [Finset.sum_filter]
    rw [hrewrite]
    have hinner : Measurable (fun p : ℝ × ℝ =>
        ∑ m ∈ support561 Y,
          (if (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2) then g m else 0)) := by
      refine Finset.measurable_sum _ (fun m _ => ?_)
      have hset : MeasurableSet
          {p : ℝ × ℝ | (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)} := by
        have h1 : MeasurableSet {p : ℝ × ℝ | (p.1 + T / 2) ≤ (m : ℝ)} :=
          measurableSet_le (by fun_prop) measurable_const
        have h2 : MeasurableSet {p : ℝ × ℝ | (m : ℝ) ≤ p.1 * (1 + p.2)} :=
          measurableSet_le measurable_const (by fun_prop)
        exact h1.inter h2
      exact Measurable.ite hset measurable_const measurable_const
    exact (Measurable.norm hinner).pow_const 2
  exact hmeas.stronglyMeasurable

/-- The boundedness of the raw mixed window integrand. -/
private lemma integrand_bound_B561 (Y T : ℝ) (g : ℕ → ℂ) (p : ℝ × ℝ) :
    ‖‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2‖
      ≤ (∑ m ∈ support561 Y, ‖g m‖) ^ 2 := by
  have hnn : (0:ℝ) ≤ ‖∑ m ∈ (support561 Y).filter
      (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2 := by
    positivity
  rw [Real.norm_of_nonneg hnn]
  set B : ℝ := ∑ m ∈ support561 Y, ‖g m‖ with hB
  have hle : ‖∑ m ∈ (support561 Y).filter
      (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ≤ B :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun x _ _ => norm_nonneg _))
  have hBnn : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have h1 : 0 ≤ B - ‖∑ m ∈ (support561 Y).filter
      (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ := by linarith
  have h2 : 0 ≤ B + ‖∑ m ∈ (support561 Y).filter
      (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ :=
    add_nonneg hBnn (norm_nonneg _)
  nlinarith [mul_nonneg h1 h2]

end StageK

section StageL

/-- **The `B` term.** The shifted window, integrated against `z` over `[D, 2D]` and against the
centre over `[Y - T/2, 2Y]`, is bounded by `2 M` times the length of the printed `z` range. -/
private lemma saffari_T2_561 (Y T : ℝ) (hY : 1 ≤ Y) (hT : 0 < T) (hTY : T ≤ Y)
    (g : ℕ → ℂ) (M : ℝ)
    (hfam : ∀ z : ℝ, T / (6 * Y) ≤ z → z ≤ 6 * T / Y →
      (∫ y in (Y / 2)..(3 * Y),
        ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2) ≤ M) :
    (∫ y in (Y - T / 2)..(2 * Y), ∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
      ≤ 2 * M * (6 * T / Y - T / (6 * Y)) := by
  have hYpos : (0 : ℝ) < Y := by linarith
  have hab : Y - T / 2 ≤ 2 * Y := by linarith
  have hDpos : (0 : ℝ) < 3 * T / (2 * Y) := hD_pos561 hT hY
  have hDle : 3 * T / (2 * Y) ≤ 2 * (3 * T / (2 * Y)) := by linarith
  have hcd : T / (6 * Y) ≤ 6 * T / Y := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 6 * Y) (by linarith : (0:ℝ) < Y)]
    nlinarith
  -- the two integrands on the rectangle
  have hGsm : StronglyMeasurable (fun p : ℝ × ℝ =>
      ((p.1 + T / 2) / p.1) * ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧
          (m : ℝ) ≤ (p.1 + T / 2) * (1 + p.2)), g m‖ ^ 2) := by
    have hfac : Measurable (fun p : ℝ × ℝ => (p.1 + T / 2) / p.1) := by fun_prop
    exact (hfac.mul (integrand_sm2d561 Y (T / 2) g).measurable).stronglyMeasurable
  have hGbd : ∀ y ∈ Set.uIoc (Y - T / 2) (2 * Y), ∀ w : ℝ,
      ‖((y + T / 2) / y) * ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
          (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2‖
        ≤ 2 * (∑ m ∈ support561 Y, ‖g m‖) ^ 2 := by
    intro y hy w
    rw [Set.uIoc_of_le hab] at hy
    have hy1 : T / 2 < y := by linarith [hy.1]
    have hfac : (y + T / 2) / y ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hfacnn : (0:ℝ) ≤ (y + T / 2) / y :=
      div_nonneg (by linarith) (le_of_lt (by linarith : (0:ℝ) < y))
    have hnn : (0:ℝ) ≤ ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
          (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := by positivity
    have hb := integrand_bound2d561 Y (T / 2) g (y, w)
    rw [Real.norm_of_nonneg (mul_nonneg hfacnn hnn)]
    have h2 : ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
          (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 ≤ (∑ m ∈ support561 Y, ‖g m‖) ^ 2 := by
      rw [Real.norm_of_nonneg hnn] at hb
      exact hb
    nlinarith [hnn, h2, hfac, hfacnn]
  -- step 1: pointwise in the centre, factor pulled inside the parameter integral
  have hpt : ∀ y ∈ Set.uIoc (Y - T / 2) (2 * Y),
      (∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
      ≤ ∫ w in (T / (6 * Y))..(6 * T / Y), ((y + T / 2) / y) *
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := by
    intro y hy
    rw [Set.uIoc_of_le hab] at hy
    refine (B_le_shifted561 Y T hY hT hTY g (by linarith [hy.1]) hy.2).trans_eq ?_
    exact (intervalIntegral.integral_const_mul _ _).symm
  -- step 2: monotone in the centre
  have hstep2 : (∫ y in (Y - T / 2)..(2 * Y), ∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
      ≤ ∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y), ((y + T / 2) / y) *
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hab
    · exact intervalIntegrable_param2d561 (fun p : ℝ × ℝ =>
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
        (integrand_sm_B561 Y T g) hDle (fun y _ w => integrand_bound_B561 Y T g (y, w))
    · exact intervalIntegrable_param2d561 _ hGsm hcd hGbd
    · intro y hy
      rw [Set.mem_Ioo] at hy
      exact hpt y (by rw [Set.uIoc_of_le hab]; exact ⟨hy.1, le_of_lt hy.2⟩)
  -- step 3: the factor is at most two
  have hstep3 : (∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y),
        ((y + T / 2) / y) * ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
            (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2)
      ≤ ∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y), 2 *
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hab
    · exact intervalIntegrable_param2d561 _ hGsm hcd hGbd
    · exact intervalIntegrable_param2d561 _
        ((integrand_sm2d561 Y (T / 2) g).const_mul 2) hcd
        (fun y _ w => by
          have hb := integrand_bound2d561 Y (T / 2) g (y, w)
          have hnn : (0:ℝ) ≤ ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
                (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := by positivity
          have h2 : ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
                (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2
              ≤ (∑ m ∈ support561 Y, ‖g m‖) ^ 2 := by
            rw [Real.norm_of_nonneg hnn] at hb
            exact hb
          rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) hnn)]
          exact mul_le_mul_of_nonneg_left h2 (by norm_num))
    · intro y hy
      rw [Set.mem_Ioo] at hy
      have hy1 : T / 2 < y := by linarith [hy.1]
      have hfac : (y + T / 2) / y ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      apply intervalIntegral.integral_mono_on_of_le_Ioo hcd
      · exact (intervalIntegrable_param561b Y (y + T / 2) _ _ g).const_mul _
      · exact (intervalIntegrable_param561b Y (y + T / 2) _ _ g).const_mul 2
      · intro w _
        exact mul_le_mul_of_nonneg_right hfac (by positivity)
  -- step 4: pull out the two
  have hstep4 : (∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y), 2 *
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
            (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2)
      = 2 * ∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := by
    simp_rw [intervalIntegral.integral_const_mul]
  -- step 5: Fubini
  have hswap : (∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2)
      = ∫ w in (T / (6 * Y))..(6 * T / Y), ∫ y in (Y - T / 2)..(2 * Y),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 :=
    intervalIntegral_intervalIntegral_swap
      (F := fun y w => ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2)
      (integrableOn_gen2d561 Y (T / 2) g (Y - T / 2) (2 * Y) (T / (6 * Y)) (6 * T / Y))
  -- step 6: each slice is bounded by M
  have hstep6 : (∫ w in (T / (6 * Y))..(6 * T / Y), ∫ y in (Y - T / 2)..(2 * Y),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2)
      ≤ ∫ w in (T / (6 * Y))..(6 * T / Y), M := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hcd
    · exact intervalIntegrable_param2d_swap561 (fun p : ℝ × ℝ =>
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧
            (m : ℝ) ≤ (p.1 + T / 2) * (1 + p.2)), g m‖ ^ 2)
        (integrand_sm2d561 Y (T / 2) g) hab (fun w _ y => integrand_bound2d561 Y (T / 2) g (y, w))
    · exact intervalIntegrable_const
    · intro w hw
      rw [Set.mem_Ioo] at hw
      have hsub : (∫ y in (Y - T / 2)..(2 * Y), ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2)
          = ∫ u in (Y - T / 2) + T / 2..(2 * Y) + T / 2, ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u * (1 + w)), g m‖ ^ 2 :=
        intervalIntegral.integral_comp_add_right
          (fun u : ℝ => ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u * (1 + w)), g m‖ ^ 2) (T / 2)
      rw [hsub]
      have hle := integral_le_of_subinterval561
        (f := fun u : ℝ => ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u * (1 + w)), g m‖ ^ 2)
        (fun a c => intervalIntegrable_gen561 Y w a c g) (fun u => by positivity)
        (by linarith : Y / 2 ≤ Y) (by linarith : Y ≤ 2 * Y + T / 2)
        (by linarith [hTY] : 2 * Y + T / 2 ≤ 3 * Y)
      have hb1 : Y - T / 2 + T / 2 = Y := by ring
      rw [hb1]
      exact hle.trans (hfam w (le_of_lt hw.1) (le_of_lt hw.2))
  -- step 7: the constant
  have hstep7 : (∫ w in (T / (6 * Y))..(6 * T / Y), M) = M * (6 * T / Y - T / (6 * Y)) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  calc (∫ y in (Y - T / 2)..(2 * Y), ∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
      ≤ ∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y), ((y + T / 2) / y) *
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := hstep2
    _ ≤ ∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y), 2 *
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := hstep3
    _ = 2 * ∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := hstep4
    _ = 2 * ∫ w in (T / (6 * Y))..(6 * T / Y), ∫ y in (Y - T / 2)..(2 * Y),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := by rw [hswap]
    _ ≤ 2 * ∫ w in (T / (6 * Y))..(6 * T / Y), M := by
        have := hstep6
        linarith
    _ = 2 * (M * (6 * T / Y - T / (6 * Y))) := by rw [hstep7]
    _ = 2 * M * (6 * T / Y - T / (6 * Y)) := by ring

end StageL

section StageM

/-- **The `A` term.** The window at the centre itself, integrated over the rectangle
`[Y - T/2, 2Y] x [D, 2D]`, is at most `M D`. -/
private lemma saffari_T1_561 (Y T : ℝ) (hY : 1 ≤ Y) (hT : 0 < T) (hTY : T ≤ Y)
    (g : ℕ → ℂ) (M : ℝ)
    (hfam : ∀ z : ℝ, T / (6 * Y) ≤ z → z ≤ 6 * T / Y →
      (∫ y in (Y / 2)..(3 * Y),
        ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2) ≤ M) :
    (∫ y in (Y - T / 2)..(2 * Y), ∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
      ≤ M * (3 * T / (2 * Y)) := by
  have hYpos : (0 : ℝ) < Y := by linarith
  have hab : Y - T / 2 ≤ 2 * Y := by linarith
  have hDpos : (0 : ℝ) < 3 * T / (2 * Y) := hD_pos561 hT hY
  have hDle : 3 * T / (2 * Y) ≤ 2 * (3 * T / (2 * Y)) := by linarith
  have hDlow : T / (6 * Y) ≤ 3 * T / (2 * Y) := hD_low561 hT hY
  have hDhigh : 2 * (3 * T / (2 * Y)) ≤ 6 * T / Y := hD_high561 hT hY
  have hInt : IntegrableOn (fun p : ℝ × ℝ =>
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y))))
      (volume.prod volume) := by
    simpa using integrableOn_gen2d561 Y 0 g (Y - T / 2) (2 * Y) (3 * T / (2 * Y))
      (2 * (3 * T / (2 * Y)))
  rw [intervalIntegral_intervalIntegral_swap
    (F := fun y z => ‖∑ m ∈ (support561 Y).filter
      (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2) hInt]
  have hle : (∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
        ∫ y in (Y - T / 2)..(2 * Y), ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
      ≤ ∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))), M := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hDle
    · exact intervalIntegrable_param2d_swap561 (fun p : ℝ × ℝ =>
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
        (by simpa using integrand_sm2d561 Y 0 g) hab (fun z _ y => by
          simpa using integrand_bound2d561 Y 0 g (y, z))
    · exact intervalIntegrable_const
    · intro z hz
      rw [Set.mem_Ioo] at hz
      exact (integral_le_of_subinterval561
        (f := fun y : ℝ => ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
        (fun a c => intervalIntegrable_gen561 Y z a c g) (fun y => by positivity)
        (by linarith : Y / 2 ≤ Y - T / 2) (by linarith : Y - T / 2 ≤ 2 * Y)
        (by linarith : 2 * Y ≤ 3 * Y)).trans
        (hfam z (le_of_lt (lt_of_le_of_lt hDlow hz.1))
          (le_of_lt (lt_of_lt_of_le hz.2 hDhigh)))
  refine hle.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

end StageM

section StageN

/-- The fixed window integrand, seen as a function on the rectangle (it ignores the second
coordinate), is integrable. -/
private lemma integrableOn_S2d561 (Y T : ℝ) (g : ℕ → ℂ) (a b c d : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ =>
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2), g m‖ ^ 2)
      (Set.uIoc a b ×ˢ Set.uIoc c d) (volume.prod volume) := by
  refine IntegrableOn.of_bound (C := (∑ m ∈ support561 Y, ‖g m‖) ^ 2) ?_ ?_ ?_
  · rcases le_total a b with hab | hab
    · rw [Set.uIoc_of_le hab, Measure.prod_prod]
      exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioc_lt_top
    · rw [Set.uIoc_of_ge hab, Measure.prod_prod]
      exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioc_lt_top
  · apply Measurable.aestronglyMeasurable
    have hrewrite : (fun p : ℝ × ℝ =>
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2), g m‖ ^ 2)
        = fun p : ℝ × ℝ =>
          ‖∑ m ∈ support561 Y,
            (if p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2 then g m else 0)‖ ^ 2 := by
      funext p
      rw [Finset.sum_filter]
    rw [hrewrite]
    have hinner : Measurable (fun p : ℝ × ℝ =>
        ∑ m ∈ support561 Y,
          (if p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2 then g m else 0)) := by
      refine Finset.measurable_sum _ (fun m _ => ?_)
      have hset : MeasurableSet {p : ℝ × ℝ | p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2} := by
        have h1 : MeasurableSet {p : ℝ × ℝ | p.1 ≤ (m : ℝ)} :=
          measurableSet_le (by fun_prop) measurable_const
        have h2 : MeasurableSet {p : ℝ × ℝ | (m : ℝ) ≤ p.1 + T / 2} :=
          measurableSet_le measurable_const (by fun_prop)
        exact h1.inter h2
      exact Measurable.ite hset measurable_const measurable_const
    exact (Measurable.norm hinner).pow_const 2
  · filter_upwards with p
    have hnn : (0 : ℝ) ≤ ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2), g m‖ ^ 2 := by positivity
    rw [Real.norm_of_nonneg hnn]
    set B : ℝ := ∑ m ∈ support561 Y, ‖g m‖ with hB
    have hle : ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2), g m‖ ≤ B :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun x _ _ => norm_nonneg _))
    have hBnn : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have h1 : 0 ≤ B - ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2), g m‖ := by linarith
    have h2 : 0 ≤ B + ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2), g m‖ :=
      add_nonneg hBnn (norm_nonneg _)
    nlinarith [mul_nonneg h1 h2]

/-- **The Saffari-Vaughan transfer**, fixed window moment bounded by the multiplicative window
moments over the printed range. -/
private lemma saffari_core561 (Y T : ℝ) (hY : 1 ≤ Y) (hT : 0 < T) (hTY : T ≤ Y)
    (g : ℕ → ℂ) (M : ℝ)
    (hfam : ∀ z : ℝ, T / (6 * Y) ≤ z → z ≤ 6 * T / Y →
      (∫ y in (Y / 2)..(3 * Y),
        ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2) ≤ M) :
    (∫ y in (Y - T / 2)..(3 * Y - T / 4),
      ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
      ≤ 18 * M := by
  have hYpos : (0 : ℝ) < Y := by linarith
  have hab : Y - T / 2 ≤ 2 * Y := by linarith
  have hDpos : (0 : ℝ) < 3 * T / (2 * Y) := hD_pos561 hT hY
  have hDle : 3 * T / (2 * Y) ≤ 2 * (3 * T / (2 * Y)) := by linarith
  have hcd : T / (6 * Y) ≤ 6 * T / Y := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 6 * Y) (by linarith : (0:ℝ) < Y)]
    nlinarith
  -- `M` is nonnegative
  have hM : 0 ≤ M := by
    have h := hfam (T / (6 * Y)) (le_refl _) hcd
    have hnn : (0:ℝ) ≤ ∫ y in (Y / 2)..(3 * Y),
        ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + (T / (6 * Y)))), g m‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun y _ => by positivity)
    linarith
  -- almost surely `y + T/2` is not an integer
  have haeP : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), ∀ n : ℤ, p.1 + T / 2 ≠ (n : ℝ) := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    have hzero : (volume.prod volume : Measure (ℝ × ℝ))
        {p : ℝ × ℝ | p.1 = (n:ℝ) - T / 2} = 0 := by
      have hset : {p : ℝ × ℝ | p.1 = (n:ℝ) - T / 2}
          = ({(n:ℝ) - T / 2} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
        ext p
        simp
      rw [hset, Measure.prod_prod, measure_singleton]
      simp
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at hzero
    filter_upwards [hzero] with p hp hcon
    exact hp (show p.1 = (n:ℝ) - T / 2 by linarith)
  -- the rectangle
  have hrect : MeasurableSet (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
      Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))) :=
    measurableSet_uIoc.prod measurableSet_uIoc
  -- the almost everywhere two term comparison
  have hpt : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)),
      p ∈ (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))) →
      ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2), g m‖ ^ 2 ≤
        2 * ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2
        + 2 * ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2 := by
    filter_upwards [haeP] with p hint hp
    rw [Set.mem_prod] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Set.uIoc_of_le hab] at hp1
    rw [Set.uIoc_of_le hDle] at hp2
    have hy1 : Y / 2 ≤ p.1 := by linarith [hp1.1]
    have hypos : 0 < p.1 := by linarith
    have hzp : 3 * T / (2 * Y) ≤ p.2 := le_of_lt hp2.1
    exact window_two_term561 hT hypos hint (hshift561 hT hTY hy1 hzp) g
  -- integrability of the three integrands on the rectangle
  have hIS : IntegrableOn (fun p : ℝ × ℝ =>
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2), g m‖ ^ 2)
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))) (volume.prod volume) :=
    integrableOn_S2d561 Y T g _ _ _ _
  have hIA : IntegrableOn (fun p : ℝ × ℝ =>
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))) (volume.prod volume) := by
    simpa using integrableOn_gen2d561 Y 0 g (Y - T / 2) (2 * Y)
      (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))
  have hIB : IntegrableOn (fun p : ℝ × ℝ =>
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))) (volume.prod volume) :=
    integrableOn_B2d561 Y T g _ _ _ _
  have hsum : IntegrableOn (fun p : ℝ × ℝ =>
      2 * ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2
      + 2 * ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))) (volume.prod volume) :=
    (hIA.const_mul 2).add (hIB.const_mul 2)
  have hcmp := MeasureTheory.setIntegral_mono_on_ae hIS hsum hrect hpt
  -- the left side as a rectangle integral
  have hleft : (3 * T / (2 * Y)) * (∫ y in (Y - T / 2)..(2 * Y),
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
      = ∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2), g m‖ ^ 2 := by
    rw [integral_rect_prod561 _ hab hDle hIS]
    have hinner : ∀ y : ℝ, (∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
        = (3 * T / (2 * Y)) *
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2 := by
      intro y
      rw [intervalIntegral.integral_const]
      have h2D : 2 * (3 * T / (2 * Y)) - 3 * T / (2 * Y) = 3 * T / (2 * Y) := by ring
      rw [h2D, smul_eq_mul]
    simp only [hinner]
    rw [intervalIntegral.integral_const_mul]
  have hdist : (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
        (2 * ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2
          + 2 * ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2))
      = 2 * (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
        + 2 * (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2) := by
    have h1 := MeasureTheory.integral_add (μ := (volume.prod volume).restrict
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))))
      (hIA.const_mul 2) (hIB.const_mul 2)
    have h2 := MeasureTheory.integral_const_mul (μ := (volume.prod volume).restrict
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y))))) 2
      (fun p : ℝ × ℝ => ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
    have h3 := MeasureTheory.integral_const_mul (μ := (volume.prod volume).restrict
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y))))) 2
      (fun p : ℝ × ℝ => ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
    refine h1.trans ?_
    rw [h2, h3]
    rfl
  -- the two rectangle bounds
  have hTA : (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2) ≤ M * (3 * T / (2 * Y)) := by
    rw [integral_rect_prod561 _ hab hDle hIA]
    exact saffari_T1_561 Y T hY hT hTY g M hfam
  have hTB : (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
      ≤ 2 * M * (6 * T / Y - T / (6 * Y)) := by
    rw [integral_rect_prod561 _ hab hDle hIB]
    exact saffari_T2_561 Y T hY hT hTY g M hfam
  -- assemble
  have hkey : (3 * T / (2 * Y)) * (∫ y in (Y - T / 2)..(2 * Y),
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
      ≤ 2 * (M * (3 * T / (2 * Y))) + 2 * (2 * M * (6 * T / Y - T / (6 * Y))) := by
    rw [hleft]
    calc (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2), g m‖ ^ 2)
        ≤ ∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
            (2 * ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2
            + 2 * ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2) := hcmp
      _ = 2 * (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
            Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
            ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
          + 2 * (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
            Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
            ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2) := hdist
      _ ≤ 2 * (M * (3 * T / (2 * Y))) + 2 * (2 * M * (6 * T / Y - T / (6 * Y))) := by
          linarith [hTA, hTB]
  -- the tail
  have htail : (∫ y in (2 * Y)..(3 * Y - T / 4),
      ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
      = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with y hy
    have hy2 : 2 * Y < y := by
      rw [Set.uIoc_of_le (by linarith : (2:ℝ) * Y ≤ 3 * Y - T / 4)] at hy
      exact hy.1
    have hz : (∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2),
        g m) = 0 := by
      refine Finset.sum_eq_zero (fun m hm => ?_)
      rw [Finset.mem_filter] at hm
      obtain ⟨hms, hp1, -⟩ := hm
      have h1 : (m : ℝ) ≤ 2 * Y := by
        have h2 : m ≤ ⌊2 * Y⌋₊ := (Finset.mem_Ioc.mp hms).2
        have h3 : (⌊2 * Y⌋₊ : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
        exact (Nat.cast_le.mpr h2).trans h3
      linarith
    rw [hz]
    simp
  -- finish
  have hsplit : (∫ y in (Y - T / 2)..(3 * Y - T / 4),
      ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
      = ∫ y in (Y - T / 2)..(2 * Y),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_fixed561 Y T (Y - T / 2) (2 * Y) g)
      (intervalIntegrable_fixed561 Y T (2 * Y) (3 * Y - T / 4) g)]
    rw [htail, add_zero]
  rw [hsplit]
  have hbound : (∫ y in (Y - T / 2)..(2 * Y),
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2) ≤ (158 / 9) * M := by
    have h1 : (3 * T / (2 * Y)) * (∫ y in (Y - T / 2)..(2 * Y),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
        ≤ (3 * T / (2 * Y)) * ((158 / 9) * M) := by
      refine hkey.trans ?_
      have hDval : (3 * T / (2 * Y)) * (158 / 9) = 2 * (3 * T / (2 * Y)) + 2 * (2 * (6 * T / Y - T / (6 * Y))) := by
        field_simp
        ring
      have hz1z0 : 2 * (6 * T / Y - T / (6 * Y)) = 2 * (35 * T / (6 * Y)) := by ring
      nlinarith [hDval, hz1z0]
    exact le_of_mul_le_mul_left h1 hDpos
  nlinarith [hbound, hM]

end StageN


section StageN2

private lemma saffari_mid561 (Y T : ℝ) (hY : 1 ≤ Y) (hT : 0 < T) (hTY : T ≤ Y)
    (g : ℕ → ℂ) :
    (∫ y in (Y - T / 2)..(3 * Y - T / 4),
      ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
      ≤ (2 / (3 * T / (2 * Y))) *
        ((∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
            Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
            ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
          + (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
            Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
            ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)) := by
  have hYpos : (0 : ℝ) < Y := by linarith
  have hab : Y - T / 2 ≤ 2 * Y := by linarith
  have hDpos : (0 : ℝ) < 3 * T / (2 * Y) := hD_pos561 hT hY
  have hDle : 3 * T / (2 * Y) ≤ 2 * (3 * T / (2 * Y)) := by linarith
  have hcd : T / (6 * Y) ≤ 6 * T / Y := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 6 * Y) (by linarith : (0:ℝ) < Y)]
    nlinarith
  -- almost surely `y + T/2` is not an integer
  have haeP : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), ∀ n : ℤ, p.1 + T / 2 ≠ (n : ℝ) := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    have hzero : (volume.prod volume : Measure (ℝ × ℝ))
        {p : ℝ × ℝ | p.1 = (n:ℝ) - T / 2} = 0 := by
      have hset : {p : ℝ × ℝ | p.1 = (n:ℝ) - T / 2}
          = ({(n:ℝ) - T / 2} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
        ext p
        simp
      rw [hset, Measure.prod_prod, measure_singleton]
      simp
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at hzero
    filter_upwards [hzero] with p hp hcon
    exact hp (show p.1 = (n:ℝ) - T / 2 by linarith)
  -- the rectangle
  have hrect : MeasurableSet (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
      Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))) :=
    measurableSet_uIoc.prod measurableSet_uIoc
  -- the almost everywhere two term comparison
  have hpt : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)),
      p ∈ (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))) →
      ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2), g m‖ ^ 2 ≤
        2 * ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2
        + 2 * ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2 := by
    filter_upwards [haeP] with p hint hp
    rw [Set.mem_prod] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Set.uIoc_of_le hab] at hp1
    rw [Set.uIoc_of_le hDle] at hp2
    have hy1 : Y / 2 ≤ p.1 := by linarith [hp1.1]
    have hypos : 0 < p.1 := by linarith
    have hzp : 3 * T / (2 * Y) ≤ p.2 := le_of_lt hp2.1
    exact window_two_term561 hT hypos hint (hshift561 hT hTY hy1 hzp) g
  -- integrability of the three integrands on the rectangle
  have hIS : IntegrableOn (fun p : ℝ × ℝ =>
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2), g m‖ ^ 2)
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))) (volume.prod volume) :=
    integrableOn_S2d561 Y T g _ _ _ _
  have hIA : IntegrableOn (fun p : ℝ × ℝ =>
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))) (volume.prod volume) := by
    simpa using integrableOn_gen2d561 Y 0 g (Y - T / 2) (2 * Y)
      (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))
  have hIB : IntegrableOn (fun p : ℝ × ℝ =>
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))) (volume.prod volume) :=
    integrableOn_B2d561 Y T g _ _ _ _
  have hsum : IntegrableOn (fun p : ℝ × ℝ =>
      2 * ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2
      + 2 * ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))) (volume.prod volume) :=
    (hIA.const_mul 2).add (hIB.const_mul 2)
  have hcmp := MeasureTheory.setIntegral_mono_on_ae hIS hsum hrect hpt
  -- the left side as a rectangle integral
  have hleft : (3 * T / (2 * Y)) * (∫ y in (Y - T / 2)..(2 * Y),
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
      = ∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2), g m‖ ^ 2 := by
    rw [integral_rect_prod561 _ hab hDle hIS]
    have hinner : ∀ y : ℝ, (∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
        = (3 * T / (2 * Y)) *
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2 := by
      intro y
      rw [intervalIntegral.integral_const]
      have h2D : 2 * (3 * T / (2 * Y)) - 3 * T / (2 * Y) = 3 * T / (2 * Y) := by ring
      rw [h2D, smul_eq_mul]
    simp only [hinner]
    rw [intervalIntegral.integral_const_mul]
  have hdist : (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
        (2 * ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2
          + 2 * ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2))
      = 2 * (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
        + 2 * (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2) := by
    have h1 := MeasureTheory.integral_add (μ := (volume.prod volume).restrict
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))))
      (hIA.const_mul 2) (hIB.const_mul 2)
    have h2 := MeasureTheory.integral_const_mul (μ := (volume.prod volume).restrict
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y))))) 2
      (fun p : ℝ × ℝ => ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
    have h3 := MeasureTheory.integral_const_mul (μ := (volume.prod volume).restrict
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y))))) 2
      (fun p : ℝ × ℝ => ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
    refine h1.trans ?_
    rw [h2, h3]
    rfl
  -- the tail
  have htail : (∫ y in (2 * Y)..(3 * Y - T / 4),
      ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
      = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with y hy
    have hy2 : 2 * Y < y := by
      rw [Set.uIoc_of_le (by linarith : (2:ℝ) * Y ≤ 3 * Y - T / 4)] at hy
      exact hy.1
    have hz : (∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2),
        g m) = 0 := by
      refine Finset.sum_eq_zero (fun m hm => ?_)
      rw [Finset.mem_filter] at hm
      obtain ⟨hms, hp1, -⟩ := hm
      have h1 : (m : ℝ) ≤ 2 * Y := by
        have h2 : m ≤ ⌊2 * Y⌋₊ := (Finset.mem_Ioc.mp hms).2
        have h3 : (⌊2 * Y⌋₊ : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
        exact (Nat.cast_le.mpr h2).trans h3
      linarith
    rw [hz]
    simp
  have hsplit : (∫ y in (Y - T / 2)..(3 * Y - T / 4),
      ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
      = ∫ y in (Y - T / 2)..(2 * Y),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_fixed561 Y T (Y - T / 2) (2 * Y) g)
      (intervalIntegrable_fixed561 Y T (2 * Y) (3 * Y - T / 4) g)]
    rw [htail, add_zero]

  rw [hsplit]
  have hkey : (3 * T / (2 * Y)) * (∫ y in (Y - T / 2)..(2 * Y),
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
      ≤ 2 * (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
            Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
        + 2 * (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
            Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2) := by
    have hstep : (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2), g m‖ ^ 2)
        ≤ 2 * (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
            Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
            ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
          + 2 * (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
            Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
            ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2) :=
      hcmp.trans hdist.le
    calc (3 * T / (2 * Y)) * (∫ y in (Y - T / 2)..(2 * Y),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
        = ∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
            Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
            ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 + T / 2), g m‖ ^ 2 := hleft
      _ ≤ 2 * (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
            Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
            ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
          + 2 * (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
            Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
            ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2) := hstep
  have hfin : (3 * T / (2 * Y)) * (∫ y in (Y - T / 2)..(2 * Y),
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), g m‖ ^ 2)
      ≤ (3 * T / (2 * Y)) * ((2 / (3 * T / (2 * Y))) *
        ((∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
            Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
            ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
          + (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
            Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
            ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2))) := by
    have hDA : (3 * T / (2 * Y)) * (2 / (3 * T / (2 * Y))) = 2 := by field_simp
    rw [← mul_assoc, hDA]
    linarith [hkey]
  exact le_of_mul_le_mul_left hfin hDpos


end StageN2

section StageN3

/-- The `A` rectangle integral is bounded by the `z`-integral of the family moment. -/
private lemma saffari_T1mid561 (Y T : ℝ) (hY : 1 ≤ Y) (hT : 0 < T) (hTY : T ≤ Y)
    (g : ℕ → ℂ) :
    (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
      ≤ ∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
          ∫ y in (Y / 2)..(3 * Y),
            ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2 := by
  have hYpos : (0 : ℝ) < Y := by linarith
  have hab : Y - T / 2 ≤ 2 * Y := by linarith
  have hDle : 3 * T / (2 * Y) ≤ 2 * (3 * T / (2 * Y)) := by
    have hD0 : (0:ℝ) < 3 * T / (2 * Y) := hD_pos561 hT hY
    linarith
  have hIA : IntegrableOn (fun p : ℝ × ℝ =>
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
      (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
        Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))) (volume.prod volume) := by
    simpa using integrableOn_gen2d561 Y 0 g (Y - T / 2) (2 * Y)
      (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))
  rw [integral_rect_prod561 _ hab hDle hIA]
  rw [intervalIntegral_intervalIntegral_swap
    (F := fun y z => ‖∑ m ∈ (support561 Y).filter
      (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2) hIA]
  apply intervalIntegral.integral_mono_on_of_le_Ioo hDle
  · exact intervalIntegrable_param2d_swap561 (fun p : ℝ × ℝ =>
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
      (by simpa using integrand_sm2d561 Y 0 g) hab (fun z _ y => by
        simpa using integrand_bound2d561 Y 0 g (y, z))
  · exact intervalIntegrable_param2d_swap561 (fun p : ℝ × ℝ =>
      ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
      (by simpa using integrand_sm2d561 Y 0 g) (by linarith : Y / 2 ≤ 3 * Y) (fun z _ y => by
        simpa using integrand_bound2d561 Y 0 g (y, z))
  · intro z _
    exact integral_le_of_subinterval561
      (f := fun y : ℝ => ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
      (fun a c => intervalIntegrable_gen561 Y z a c g) (fun y => by positivity)
      (by linarith : Y / 2 ≤ Y - T / 2) (by linarith : Y - T / 2 ≤ 2 * Y)
      (by linarith : 2 * Y ≤ 3 * Y)

/-- The `B` term is bounded by twice the `w`-integral of the family moment. -/
private lemma saffari_T2mid561 (Y T : ℝ) (hY : 1 ≤ Y) (hT : 0 < T) (hTY : T ≤ Y)
    (g : ℕ → ℂ) :
    (∫ y in (Y - T / 2)..(2 * Y), ∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
      ≤ 2 * (∫ w in (T / (6 * Y))..(6 * T / Y), ∫ y in (Y / 2)..(3 * Y),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + w)), g m‖ ^ 2) := by
  have hYpos : (0 : ℝ) < Y := by linarith
  have hab : Y - T / 2 ≤ 2 * Y := by linarith
  have hDpos : (0 : ℝ) < 3 * T / (2 * Y) := hD_pos561 hT hY
  have hDle : 3 * T / (2 * Y) ≤ 2 * (3 * T / (2 * Y)) := by linarith
  have hcd : T / (6 * Y) ≤ 6 * T / Y := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 6 * Y) (by linarith : (0:ℝ) < Y)]
    nlinarith
  -- the two integrands on the rectangle
  have hGsm : StronglyMeasurable (fun p : ℝ × ℝ =>
      ((p.1 + T / 2) / p.1) * ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧
          (m : ℝ) ≤ (p.1 + T / 2) * (1 + p.2)), g m‖ ^ 2) := by
    have hfac : Measurable (fun p : ℝ × ℝ => (p.1 + T / 2) / p.1) := by fun_prop
    exact (hfac.mul (integrand_sm2d561 Y (T / 2) g).measurable).stronglyMeasurable
  have hGbd : ∀ y ∈ Set.uIoc (Y - T / 2) (2 * Y), ∀ w : ℝ,
      ‖((y + T / 2) / y) * ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
          (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2‖
        ≤ 2 * (∑ m ∈ support561 Y, ‖g m‖) ^ 2 := by
    intro y hy w
    rw [Set.uIoc_of_le hab] at hy
    have hy1 : T / 2 < y := by linarith [hy.1]
    have hfac : (y + T / 2) / y ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hfacnn : (0:ℝ) ≤ (y + T / 2) / y :=
      div_nonneg (by linarith) (le_of_lt (by linarith : (0:ℝ) < y))
    have hnn : (0:ℝ) ≤ ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
          (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := by positivity
    have hb := integrand_bound2d561 Y (T / 2) g (y, w)
    rw [Real.norm_of_nonneg (mul_nonneg hfacnn hnn)]
    have h2 : ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
          (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 ≤ (∑ m ∈ support561 Y, ‖g m‖) ^ 2 := by
      rw [Real.norm_of_nonneg hnn] at hb
      exact hb
    nlinarith [hnn, h2, hfac, hfacnn]
  -- step 1: pointwise in the centre, factor pulled inside the parameter integral
  have hpt : ∀ y ∈ Set.uIoc (Y - T / 2) (2 * Y),
      (∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
      ≤ ∫ w in (T / (6 * Y))..(6 * T / Y), ((y + T / 2) / y) *
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := by
    intro y hy
    rw [Set.uIoc_of_le hab] at hy
    refine (B_le_shifted561 Y T hY hT hTY g (by linarith [hy.1]) hy.2).trans_eq ?_
    exact (intervalIntegral.integral_const_mul _ _).symm
  -- step 2: monotone in the centre
  have hstep2 : (∫ y in (Y - T / 2)..(2 * Y), ∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
      ≤ ∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y), ((y + T / 2) / y) *
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hab
    · exact intervalIntegrable_param2d561 (fun p : ℝ × ℝ =>
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
        (integrand_sm_B561 Y T g) hDle (fun y _ w => integrand_bound_B561 Y T g (y, w))
    · exact intervalIntegrable_param2d561 _ hGsm hcd hGbd
    · intro y hy
      rw [Set.mem_Ioo] at hy
      exact hpt y (by rw [Set.uIoc_of_le hab]; exact ⟨hy.1, le_of_lt hy.2⟩)
  -- step 3: the factor is at most two
  have hstep3 : (∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y),
        ((y + T / 2) / y) * ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
            (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2)
      ≤ ∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y), 2 *
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hab
    · exact intervalIntegrable_param2d561 _ hGsm hcd hGbd
    · exact intervalIntegrable_param2d561 _
        ((integrand_sm2d561 Y (T / 2) g).const_mul 2) hcd
        (fun y _ w => by
          have hb := integrand_bound2d561 Y (T / 2) g (y, w)
          have hnn : (0:ℝ) ≤ ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
                (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := by positivity
          have h2 : ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
                (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2
              ≤ (∑ m ∈ support561 Y, ‖g m‖) ^ 2 := by
            rw [Real.norm_of_nonneg hnn] at hb
            exact hb
          rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) hnn)]
          exact mul_le_mul_of_nonneg_left h2 (by norm_num))
    · intro y hy
      rw [Set.mem_Ioo] at hy
      have hy1 : T / 2 < y := by linarith [hy.1]
      have hfac : (y + T / 2) / y ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      apply intervalIntegral.integral_mono_on_of_le_Ioo hcd
      · exact (intervalIntegrable_param561b Y (y + T / 2) _ _ g).const_mul _
      · exact (intervalIntegrable_param561b Y (y + T / 2) _ _ g).const_mul 2
      · intro w _
        exact mul_le_mul_of_nonneg_right hfac (by positivity)
  -- step 4: pull out the two
  have hstep4 : (∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y), 2 *
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
            (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2)
      = 2 * ∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := by
    simp_rw [intervalIntegral.integral_const_mul]
  -- step 5: Fubini
  have hswap : (∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2)
      = ∫ w in (T / (6 * Y))..(6 * T / Y), ∫ y in (Y - T / 2)..(2 * Y),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 :=
    intervalIntegral_intervalIntegral_swap
      (F := fun y w => ‖∑ m ∈ (support561 Y).filter
        (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2)
      (integrableOn_gen2d561 Y (T / 2) g (Y - T / 2) (2 * Y) (T / (6 * Y)) (6 * T / Y))
  -- bound the shifted moment by the printed one
  have hshift : (∫ w in (T / (6 * Y))..(6 * T / Y), ∫ y in (Y - T / 2)..(2 * Y),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2)
      ≤ ∫ w in (T / (6 * Y))..(6 * T / Y), ∫ y in (Y / 2)..(3 * Y),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + w)), g m‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hcd
    · exact intervalIntegrable_param2d_swap561 (fun p : ℝ × ℝ =>
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧
            (m : ℝ) ≤ (p.1 + T / 2) * (1 + p.2)), g m‖ ^ 2)
        (integrand_sm2d561 Y (T / 2) g) hab (fun w _ y => integrand_bound2d561 Y (T / 2) g (y, w))
    · exact intervalIntegrable_param2d_swap561 (fun p : ℝ × ℝ =>
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), g m‖ ^ 2)
        (by simpa using integrand_sm2d561 Y 0 g) (by linarith : Y / 2 ≤ 3 * Y) (fun w _ y => by
          simpa using integrand_bound2d561 Y 0 g (y, w))
    · intro w _
      have hsub : (∫ y in (Y - T / 2)..(2 * Y), ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2)
          = ∫ u in (Y - T / 2) + T / 2..(2 * Y) + T / 2, ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u * (1 + w)), g m‖ ^ 2 :=
        intervalIntegral.integral_comp_add_right
          (fun u : ℝ => ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u * (1 + w)), g m‖ ^ 2) (T / 2)
      rw [hsub]
      have hb1 : Y - T / 2 + T / 2 = Y := by ring
      rw [hb1]
      exact integral_le_of_subinterval561
        (f := fun u : ℝ => ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u * (1 + w)), g m‖ ^ 2)
        (fun a c => intervalIntegrable_gen561 Y w a c g) (fun u => by positivity)
        (by linarith : Y / 2 ≤ Y) (by linarith : Y ≤ 2 * Y + T / 2)
        (by linarith : 2 * Y + T / 2 ≤ 3 * Y)

  calc (∫ y in (Y - T / 2)..(2 * Y), ∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), g m‖ ^ 2)
      ≤ ∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y), ((y + T / 2) / y) *
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := hstep2
    _ ≤ ∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y), 2 *
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := hstep3
    _ = 2 * ∫ y in (Y - T / 2)..(2 * Y), ∫ w in (T / (6 * Y))..(6 * T / Y),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := hstep4
    _ = 2 * ∫ w in (T / (6 * Y))..(6 * T / Y), ∫ y in (Y - T / 2)..(2 * Y),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => (y + T / 2) ≤ (m : ℝ) ∧
              (m : ℝ) ≤ (y + T / 2) * (1 + w)), g m‖ ^ 2 := by rw [hswap]
    _ ≤ 2 * ∫ w in (T / (6 * Y))..(6 * T / Y), ∫ y in (Y / 2)..(3 * Y),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + w)), g m‖ ^ 2 := by
        linarith [hshift]

end StageN3

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
  refine ⟨18, by norm_num, ?_⟩
  intro Y T hY hT hTY b v q E M hM hfam
  have hYpos : (0 : ℝ) < Y := by linarith
  have hab : Y - T / 2 ≤ 2 * Y := by linarith
  have hDpos : (0 : ℝ) < 3 * T / (2 * Y) := hD_pos561 hT hY
  have hDle : 3 * T / (2 * Y) ≤ 2 * (3 * T / (2 * Y)) := by linarith
  have hcd : T / (6 * Y) ≤ 6 * T / Y := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 6 * Y) (by linarith : (0:ℝ) < Y)]
    nlinarith
  have hDlow : T / (6 * Y) ≤ 3 * T / (2 * Y) := hD_low561 hT hY
  have hDhigh : 2 * (3 * T / (2 * Y)) ≤ 6 * T / Y := hD_high561 hT hY
  -- the hypothesis rewritten in the `y + y * z` shape of the definition
  have hfam' : ∀ z : ℝ, T / (6 * Y) ≤ z → z ≤ 6 * T / Y →
      (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
        ∫ y in (Y / 2)..(3 * Y),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)),
            centered561 Y b v χ m‖ ^ 2) ≤ M := by
    intro z h1 h2
    have hh := hfam z h1 h2
    simp only [multiplicativeWindowMoment561] at hh
    have hyz : ∀ y : ℝ, y * (1 + z) = y + y * z := fun y => by ring
    have hEqz : (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
          ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), centered561 Y b v χ m‖ ^ 2)
        = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
          ∫ y in (Y / 2)..(3 * Y),
            ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              centered561 Y b v χ m‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun χ _ => ?_)
      apply intervalIntegral.integral_congr
      intro y _
      dsimp only
      rw [hyz y]
    rw [hEqz]
    exact hh
  -- z integrability of each character's slice
  have hzint : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
      IntervalIntegrable (fun z : ℝ => ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), centered561 Y b v χ m‖ ^ 2)
      volume (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y))) := by
    intro χ _
    exact intervalIntegrable_param2d_swap561 (fun p : ℝ × ℝ => ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), centered561 Y b v χ m‖ ^ 2)
      (by simpa using integrand_sm2d561 Y 0 (centered561 Y b v χ)) (by linarith)
      (fun z _ y => by simpa using integrand_bound2d561 Y 0 (centered561 Y b v χ) (y, z))
  -- the `A` sum
  have hA : (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
        ∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), centered561 Y b v χ m‖ ^ 2)
      ≤ M * (3 * T / (2 * Y)) := by
    have h1 : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
        (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), centered561 Y b v χ m‖ ^ 2)
        ≤ ∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))), ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), centered561 Y b v χ m‖ ^ 2 := by
      intro χ _
      exact saffari_T1mid561 Y T hY hT hTY (centered561 Y b v χ)
    have h2 : (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
          ∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))), ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), centered561 Y b v χ m‖ ^ 2)
        = ∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E, ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), centered561 Y b v χ m‖ ^ 2 :=
      (intervalIntegral.integral_finsetSum (fun χ hχ => hzint χ hχ)).symm
    have h3 : (∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))),
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E, ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)), centered561 Y b v χ m‖ ^ 2)
        ≤ ∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))), M := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hDle
      · have hsum := IntervalIntegrable.sum (Finset.univ \ E) (fun χ hχ => hzint χ hχ)
        have hEqfun : ((∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            fun z : ℝ => ∫ y in (Y / 2)..(3 * Y),
              ‖∑ m ∈ (support561 Y).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + z)),
                centered561 Y b v χ m‖ ^ 2) : ℝ → ℝ)
            = fun u : ℝ => ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
                ∫ y in (Y / 2)..(3 * Y),
                  ‖∑ m ∈ (support561 Y).filter
                    (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + u)),
                    centered561 Y b v χ m‖ ^ 2 := by
          funext u
          rw [Finset.sum_apply]
        rw [hEqfun] at hsum
        exact hsum
      · exact intervalIntegrable_const
      · intro z hz
        rw [Set.mem_Ioo] at hz
        exact hfam' z (le_of_lt (lt_of_le_of_lt hDlow hz.1))
          (le_of_lt (lt_of_lt_of_le hz.2 hDhigh))
    have h4 : (∫ z in (3 * T / (2 * Y))..(2 * (3 * T / (2 * Y))), M)
        = M * (3 * T / (2 * Y)) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      have h2D : 2 * (3 * T / (2 * Y)) - 3 * T / (2 * Y) = 3 * T / (2 * Y) := by ring
      rw [h2D]
      ring
    exact ((Finset.sum_le_sum h1).trans h2.le).trans (h3.trans h4.le)
  -- z integrability for the `B` side
  have hzint2 : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
      IntervalIntegrable (fun w : ℝ => ∫ y in (Y / 2)..(3 * Y),
        ‖∑ m ∈ (support561 Y).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + w)),
          centered561 Y b v χ m‖ ^ 2) volume (T / (6 * Y)) (6 * T / Y) := by
    intro χ _
    exact intervalIntegrable_param2d_swap561 (fun p : ℝ × ℝ => ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), centered561 Y b v χ m‖ ^ 2)
      (by simpa using integrand_sm2d561 Y 0 (centered561 Y b v χ)) (by linarith)
      (fun z _ y => by simpa using integrand_bound2d561 Y 0 (centered561 Y b v χ) (y, z))
  -- the `B` sum
  have hB : (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
        ∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), centered561 Y b v χ m‖ ^ 2)
      ≤ 2 * M * (6 * T / Y - T / (6 * Y)) := by
    have h1 : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
        (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), centered561 Y b v χ m‖ ^ 2)
        ≤ 2 * (∫ w in (T / (6 * Y))..(6 * T / Y), ∫ y in (Y / 2)..(3 * Y),
              ‖∑ m ∈ (support561 Y).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + w)),
                centered561 Y b v χ m‖ ^ 2) := by
      intro χ _
      rw [integral_rect_prod561 _ hab hDle (integrableOn_B2d561 Y T (centered561 Y b v χ)
        (Y - T / 2) (2 * Y) (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y))))]
      exact saffari_T2mid561 Y T hY hT hTY (centered561 Y b v χ)
    have h2 : 2 * (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
          ∫ w in (T / (6 * Y))..(6 * T / Y), ∫ y in (Y / 2)..(3 * Y),
            ‖∑ m ∈ (support561 Y).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + w)),
              centered561 Y b v χ m‖ ^ 2)
        = 2 * (∫ w in (T / (6 * Y))..(6 * T / Y),
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
              ∫ y in (Y / 2)..(3 * Y),
                ‖∑ m ∈ (support561 Y).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + w)),
                  centered561 Y b v χ m‖ ^ 2) := by
      rw [intervalIntegral.integral_finsetSum (fun χ hχ => hzint2 χ hχ)]
    have h3 : (∫ w in (T / (6 * Y))..(6 * T / Y),
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ y in (Y / 2)..(3 * Y),
              ‖∑ m ∈ (support561 Y).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + w)),
                centered561 Y b v χ m‖ ^ 2)
        ≤ ∫ w in (T / (6 * Y))..(6 * T / Y), M := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hcd
      · have hsum := IntervalIntegrable.sum (Finset.univ \ E) (fun χ hχ => hzint2 χ hχ)
        have hEqfun : ((∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            fun w : ℝ => ∫ y in (Y / 2)..(3 * Y),
              ‖∑ m ∈ (support561 Y).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + w)),
                centered561 Y b v χ m‖ ^ 2) : ℝ → ℝ)
            = fun u : ℝ => ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
                ∫ y in (Y / 2)..(3 * Y),
                  ‖∑ m ∈ (support561 Y).filter
                    (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + u)),
                    centered561 Y b v χ m‖ ^ 2 := by
          funext u
          rw [Finset.sum_apply]
        rw [hEqfun] at hsum
        exact hsum
      · exact intervalIntegrable_const
      · intro w hw
        rw [Set.mem_Ioo] at hw
        exact hfam' w (le_of_lt hw.1) (le_of_lt hw.2)
    have h4 : (∫ w in (T / (6 * Y))..(6 * T / Y), M) = M * (6 * T / Y - T / (6 * Y)) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    calc (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
          ∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), centered561 Y b v χ m‖ ^ 2)
        ≤ 2 * (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ w in (T / (6 * Y))..(6 * T / Y), ∫ y in (Y / 2)..(3 * Y),
              ‖∑ m ∈ (support561 Y).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + w)),
                centered561 Y b v χ m‖ ^ 2) := by
          have hs := Finset.sum_le_sum h1
          rw [← Finset.mul_sum] at hs
          exact hs
      _ = 2 * (∫ w in (T / (6 * Y))..(6 * T / Y),
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
              ∫ y in (Y / 2)..(3 * Y),
                ‖∑ m ∈ (support561 Y).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y * (1 + w)),
                  centered561 Y b v χ m‖ ^ 2) := h2
      _ ≤ 2 * (∫ w in (T / (6 * Y))..(6 * T / Y), M) := by linarith [h3]
      _ = 2 * M * (6 * T / Y - T / (6 * Y)) := by rw [h4]; ring
  -- combine
  have hfin : (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
        ∫ y in (Y - T / 2)..(3 * Y - T / 4), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), centered561 Y b v χ m‖ ^ 2)
      ≤ (2 / (3 * T / (2 * Y))) *
        ((∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), centered561 Y b v χ m‖ ^ 2)
          + (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), centered561 Y b v χ m‖ ^ 2)) := by
    have h1 : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
        (∫ y in (Y - T / 2)..(3 * Y - T / 4), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), centered561 Y b v χ m‖ ^ 2)
        ≤ (2 / (3 * T / (2 * Y))) *
          ((∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), centered561 Y b v χ m‖ ^ 2)
            + (∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), centered561 Y b v χ m‖ ^ 2)) := by
      intro χ _
      exact saffari_mid561 Y T hY hT hTY (centered561 Y b v χ)
    have hs := Finset.sum_le_sum h1
    rw [← Finset.mul_sum] at hs
    rw [Finset.sum_add_distrib] at hs
    exact hs
  have hAB : (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
        ∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), centered561 Y b v χ m‖ ^ 2)
      + (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
        ∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
          Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)), centered561 Y b v χ m‖ ^ 2)
      ≤ M * (3 * T / (2 * Y)) + 2 * M * (6 * T / Y - T / (6 * Y)) := by
    linarith [hA, hB]
  have hstep : (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
        ∫ y in (Y - T / 2)..(3 * Y - T / 4), ‖∑ m ∈ (support561 Y).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2), centered561 Y b v χ m‖ ^ 2)
      ≤ (2 / (3 * T / (2 * Y))) *
        (M * (3 * T / (2 * Y)) + 2 * M * (6 * T / Y - T / (6 * Y))) := by
    have hpos : (0:ℝ) ≤ 2 / (3 * T / (2 * Y)) := by positivity
    have h1 : (2 / (3 * T / (2 * Y))) *
        ((∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
              Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
              ‖∑ m ∈ (support561 Y).filter
                (fun m : ℕ => p.1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)),
                centered561 Y b v χ m‖ ^ 2)
          + (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
            ∫ p in (Set.uIoc (Y - T / 2) (2 * Y) ×ˢ
              Set.uIoc (3 * T / (2 * Y)) (2 * (3 * T / (2 * Y)))),
              ‖∑ m ∈ (support561 Y).filter
                (fun m : ℕ => (p.1 + T / 2) ≤ (m : ℝ) ∧ (m : ℝ) ≤ p.1 * (1 + p.2)),
                centered561 Y b v χ m‖ ^ 2))
        ≤ (2 / (3 * T / (2 * Y))) *
          (M * (3 * T / (2 * Y)) + 2 * M * (6 * T / Y - T / (6 * Y))) :=
      mul_le_mul_of_nonneg_left hAB hpos
    exact le_trans hfin h1
  have hconv : (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
        ∫ y in (Y - T / 2)..(3 * Y - T / 4),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * (T / (2 * y))),
            centered561 Y b v χ m‖ ^ 2)
      = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E,
        ∫ y in (Y - T / 2)..(3 * Y - T / 4),
          ‖∑ m ∈ (support561 Y).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + T / 2),
            centered561 Y b v χ m‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (by linarith : Y - T / 2 ≤ 3 * Y - T / 4)] at hy
    have hypos : 0 < y := by linarith [hy.1]
    have hy0 : y ≠ 0 := ne_of_gt hypos
    have hz : y + y * (T / (2 * y)) = y + T / 2 := by
      field_simp
    dsimp only
    rw [hz]
  rw [hconv]
  refine hstep.trans ?_
  have hc : (2 / (3 * T / (2 * Y))) *
      (M * (3 * T / (2 * Y)) + 2 * M * (6 * T / Y - T / (6 * Y))) = (158 / 9) * M := by
    have hD : (3 * T / (2 * Y)) ≠ 0 := ne_of_gt hDpos
    have hTpos : T ≠ 0 := ne_of_gt hT
    have hYne : Y ≠ 0 := ne_of_gt hYpos
    field_simp
    ring
  rw [hc]
  nlinarith [hM]



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
