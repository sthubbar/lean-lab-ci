import LeanLab.ExceptionalSet.SPLIT_leaf_majorant_small_width524

/-!
Feed of `LeanLab.ExceptionalSet.Decomp524a.leaf_majorant_origin_narrow524`
and `leaf_majorant_origin_wide524`, burst-20261122 session S90.

Finding: both leaves are FALSE as written. A cosine polynomial
`P x = c₀ + ∑ A h * cos (2 * π * (h * x))` is even and one periodic, so if it
dominates the indicator of `[0, w)` it also dominates the indicator of
`(1 - w, 1)`, and it is nonnegative everywhere. Integrating over one period kills
every cosine, hence `c₀ = ∫₀¹ P ≥ 2 * w`. The leaves ask for
`c₀ ≤ w + 4 / (H + 1)`, which fails as soon as `w > 4 / (H + 1)`, for instance
`w = 1 / 6`, `H = 100` in the narrow band and `w = 1 / 3`, `H = 100` in the wide
band, where every hypothesis of the leaf holds.

The parent split in `SPLIT_leaf_majorant_small_width524` reduced the complex
exponential target, where a Beurling Selberg majorant centred at the interval is
available, to a real cosine majorant centred at the origin; the reduction loses
the phase freedom, and the reduced statements cannot hold. The cited source is
the Beurling Selberg extremal majorant as used in Bruedern Perelli 1998; the
counterexample here is elementary and independent of it.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp524a

open Real Finset

/-- One period of `cos (2 π h x)` integrates to zero for `h ≥ 1`. -/
theorem feed1122_integral_cos_period (h : ℕ) (hh : 1 ≤ h) :
    ∫ x in (0 : ℝ)..1, cos (2 * π * ((h : ℝ) * x)) = 0 := by
  have hc : (2 * π * (h : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < h := by exact_mod_cast hh
    positivity
  have hfun : (fun x : ℝ => cos (2 * π * ((h : ℝ) * x)))
      = fun x : ℝ => cos ((2 * π * (h : ℝ)) * x) := by
    funext x; ring_nf
  rw [hfun, intervalIntegral.integral_comp_mul_left (fun x => cos x) hc, integral_cos]
  have hs : sin (2 * π * (h : ℝ)) = 0 := by
    have := Real.sin_nat_mul_pi (2 * h)
    rw [show (2 * π * (h : ℝ)) = ((2 * h : ℕ) : ℝ) * π by push_cast; ring]
    exact this
  simp [hs]

/-- The integral of a cosine polynomial over one period is its constant term. -/
theorem feed1122_integral_cospoly (c₀ : ℝ) (A : ℕ → ℝ) (H : ℕ) :
    ∫ x in (0 : ℝ)..1, (c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x))) = c₀ := by
  have hcont : ∀ h : ℕ, Continuous fun x : ℝ => A h * cos (2 * π * ((h : ℝ) * x)) := by
    intro h; fun_prop
  rw [intervalIntegral.integral_add intervalIntegrable_const
      (by
        refine (continuous_finsetSum _ (fun h _ => hcont h)).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun h _ => (hcont h).intervalIntegrable _ _)]
  have hz : ∀ h ∈ Icc 1 H,
      ∫ x in (0 : ℝ)..1, A h * cos (2 * π * ((h : ℝ) * x)) = 0 := by
    intro h hh
    rw [intervalIntegral.integral_const_mul,
      feed1122_integral_cos_period h (Finset.mem_Icc.mp hh).1, mul_zero]
  rw [Finset.sum_eq_zero hz]
  simp

/-- The key obstruction: a cosine majorant of the indicator of `[0, w)` with
`w ≤ 1 / 2` has constant term at least `2 * w`. -/
theorem feed1122_two_w_le_const (w : ℝ) (H : ℕ) (hw0 : 0 < w) (hw : w ≤ 1 / 2)
    (c₀ : ℝ) (A : ℕ → ℝ)
    (hdom : ∀ x : ℝ, (if 0 ≤ Int.fract x ∧ Int.fract x < w then (1 : ℝ) else 0) ≤
      c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x))) :
    2 * w ≤ c₀ := by
  set P : ℝ → ℝ := fun x => c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x))
    with hP
  have hPc : Continuous P := by rw [hP]; fun_prop
  have hint : ∀ a b : ℝ, IntervalIntegrable P MeasureTheory.volume a b :=
    fun a b => hPc.intervalIntegrable a b
  have hnonneg : ∀ x, 0 ≤ P x := by
    intro x
    have := hdom x
    have h0 : (0 : ℝ) ≤ (if 0 ≤ Int.fract x ∧ Int.fract x < w then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    exact h0.trans this
  have hrefl : ∀ x, P (1 - x) = P x := by
    intro x
    rw [hP]
    simp only
    congr 1
    refine Finset.sum_congr rfl (fun h _ => ?_)
    congr 1
    have := Real.cos_nat_mul_two_pi_sub (2 * π * ((h : ℝ) * x)) h
    rw [← this]
    congr 1
    ring
  have hleft : ∀ x ∈ Set.Ioo (0 : ℝ) w, (1 : ℝ) ≤ P x := by
    intro x hx
    have hfr : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx.1.le, by linarith [hx.2]⟩
    have := hdom x
    rw [hfr, if_pos ⟨hx.1.le, hx.2⟩] at this
    exact this
  have hright : ∀ x ∈ Set.Ioo (1 - w) 1, (1 : ℝ) ≤ P x := by
    intro x hx
    rw [← hrefl x]
    exact hleft (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h1 : ∫ x in (0 : ℝ)..w, (1 : ℝ) ≤ ∫ x in (0 : ℝ)..w, P x :=
    intervalIntegral.integral_mono_on_of_le_Ioo hw0.le intervalIntegrable_const (hint _ _) hleft
  have h2 : ∫ x in w..(1 - w), (0 : ℝ) ≤ ∫ x in w..(1 - w), P x :=
    intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const (hint _ _)
      (fun x _ => hnonneg x)
  have h3 : ∫ x in (1 - w)..1, (1 : ℝ) ≤ ∫ x in (1 - w)..1, P x :=
    intervalIntegral.integral_mono_on_of_le_Ioo (by linarith) intervalIntegrable_const
      (hint _ _) hright
  have htot : ∫ x in (0 : ℝ)..1, P x = c₀ := by
    rw [hP]; exact feed1122_integral_cospoly c₀ A H
  have hsplit : ∫ x in (0 : ℝ)..1, P x =
      (∫ x in (0 : ℝ)..w, P x) + (∫ x in w..(1 - w), P x) + ∫ x in (1 - w)..1, P x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, mul_zero] at h1 h2 h3
  linarith

/-- FALSE finding for `leaf_majorant_origin_narrow524`: its universal closure
fails at `w = 1 / 6`, `H = 100`, where `2 * w = 1 / 3` exceeds the allowed
constant `1 / 6 + 4 / 101`. -/
theorem leaf_majorant_origin_narrow524_false :
    ¬ (∀ (w : ℝ) (H : ℕ), 0 < w → w ≤ 1 / 6 → 4 ≤ H →
      w + 4 / ((H : ℝ) + 1) < 1 →
      (w + 4 / ((H : ℝ) + 1)) * (1 + cos (π * w)) < 1 →
      ∃ c₀ : ℝ, ∃ A : ℕ → ℝ,
        c₀ ≤ w + 4 / ((H : ℝ) + 1) ∧
        (∀ h ∈ Icc 1 H, |A h| ≤ 4 / (h : ℝ)) ∧
        ∀ x : ℝ, (if 0 ≤ Int.fract x ∧ Int.fract x < w then (1 : ℝ) else 0) ≤
          c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x))) := by
  intro hall
  have hcos : cos (π * (1 / 6)) ≤ 1 := cos_le_one _
  have hcast : ((100 : ℕ) : ℝ) = 100 := by norm_num
  obtain ⟨c₀, A, hc₀, -, hdom⟩ := hall (1 / 6) 100 (by norm_num) le_rfl (by norm_num)
    (by rw [hcast]; norm_num) (by rw [hcast]; nlinarith [cos_le_one (π * (1 / 6))])
  have := feed1122_two_w_le_const (1 / 6) 100 (by norm_num) (by norm_num) c₀ A hdom
  rw [hcast] at hc₀
  linarith

/-- The concrete instance: no data satisfies the conclusion of
`leaf_majorant_origin_narrow524` at `w = 1 / 6`, `H = 100`. -/
theorem leaf_majorant_origin_narrow524_counterexample :
    ¬ ∃ c₀ : ℝ, ∃ A : ℕ → ℝ,
        c₀ ≤ (1 / 6 : ℝ) + 4 / (((100 : ℕ) : ℝ) + 1) ∧
        (∀ h ∈ Icc 1 100, |A h| ≤ 4 / (h : ℝ)) ∧
        ∀ x : ℝ, (if 0 ≤ Int.fract x ∧ Int.fract x < (1 / 6 : ℝ) then (1 : ℝ) else 0) ≤
          c₀ + ∑ h ∈ Icc 1 100, A h * cos (2 * π * ((h : ℝ) * x)) := by
  rintro ⟨c₀, A, hc₀, -, hdom⟩
  have := feed1122_two_w_le_const (1 / 6) 100 (by norm_num) (by norm_num) c₀ A hdom
  have hcast : ((100 : ℕ) : ℝ) = 100 := by norm_num
  rw [hcast] at hc₀
  linarith

end LeanLab.ExceptionalSet.Decomp524a
