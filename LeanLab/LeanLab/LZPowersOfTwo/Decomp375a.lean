/-
P0079 page 10, Section 5. Finite interval telescoping and weighted tails.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.PrimeMoment353
import LeanLab.LZPowersOfTwo.Decomp353d
import LeanLab.LZPowersOfTwo.ArcGeometry353

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 10, Section 5, the inverse-square tail summation.
A unit-interval bound C over b squared gives a full positive tail bound 2 C over a.
This finite telescoping proof uses the improper-integral limit from Mathlib. -/
theorem unit_tail_bound375 (f : ℝ → ℝ) (hf : Integrable f) (a C : ℝ) (ha : 1 ≤ a) (hC : 0 ≤ C)
    (hu : ∀ b : ℝ, a ≤ b → (∫ x in b..b + 1, f x) ≤ C / b ^ 2) :
    (∫ x in Set.Ioi a, f x) ≤ 2 * C / a := by
  have hfinite (N : ℕ) : (∫ x in a..a + N, f x) ≤
      2 * C * (a⁻¹ - (a + N)⁻¹) := by
    induction N with
    | zero => simp
    | succ N ih =>
      have hb : 1 ≤ a + (N : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
      have hb0 : 0 < a + (N : ℝ) := by linarith
      have hb1 : 0 < a + (N : ℝ) + 1 := by linarith
      have ht : 1 / (a + (N : ℝ)) ^ 2 ≤
          2 * ((a + N)⁻¹ - (a + N + 1)⁻¹) := by
        field_simp
        nlinarith only [hb]
      have htC := mul_le_mul_of_nonneg_left ht hC
      have hu' := hu (a + N) (by linarith [Nat.cast_nonneg (α := ℝ) N])
      rw [Nat.cast_succ, show a + ((N : ℝ) + 1) = (a + N) + 1 by ring,
        ← intervalIntegral.integral_add_adjacent_intervals (b := a + (N : ℝ))
          hf.intervalIntegrable hf.intervalIntegrable]
      have he : C / (a + (N : ℝ)) ^ 2 = C * (1 / (a + N) ^ 2) := by ring
      rw [he] at hu'
      linarith only [ih, hu', htC]
  have hb : Tendsto (fun N : ℕ => a + (N : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_add_const_left atTop a tendsto_natCast_atTop_atTop
  have hlim := intervalIntegral_tendsto_integral_Ioi a hf.integrableOn hb
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro N
  refine (hfinite N).trans ?_
  have hn : 0 ≤ (a + (N : ℝ))⁻¹ := inv_nonneg.mpr (by positivity)
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (sub_le_self _ hn) (by positivity)

/-- P0079 page 10, Section 5. The full positive tail for the unscaled prime sum
is bounded using the proved unit moment and Chebyshev's estimate. -/
theorem primeMoment_unit_tail375 (ε X η a : ℝ) (hX : 2 ≤ X) (ha : 1 ≤ a) :
    (∫ α in Set.Ioi a, primeMoment353 1 η ε X α) ≤
      2 * ((1 / Real.pi ^ 2) * (log 4 * X * log X)) / a := by
  apply unit_tail_bound375 _ (primeMoment_integrable353 1 η ε X) _ _ ha
    (by have : 0 ≤ log X := log_nonneg (by linarith); positivity)
  intro b hb
  have hb0 : 0 < b := by linarith
  simp only [primeMoment353, one_mul]
  convert primeMoment_unit_le353 ε X η b hX hb0 using 1 <;> ring

/-- P0079 page 10, Section 5. Reflection preserves the weighted prime moment.
The prime sum is conjugated and the squared sinc kernel is even. -/
theorem primeMoment_even375 (l η ε X α : ℝ) :
    primeMoment353 l η ε X (-α) = primeMoment353 l η ε X α := by
  have hs : primeSum293 ε X (-(l * α)) =
      starRingEnd ℂ (primeSum293 ε X (l * α)) := by
    unfold primeSum293
    simp only [map_sum, map_mul, Complex.conj_ofReal]
    apply sum_congr rfl
    intro p hp
    rw [show (p : ℝ) * -(l * α) = -((p : ℝ) * (l * α)) by ring,
      character_neg353]
  simp only [primeMoment353, mul_neg, hs, Complex.norm_conj, kernel293, Real.sinc_neg]

/-- P0079 page 10, Section 5. The sign of a nonzero coefficient is irrelevant
to its weighted second moment. -/
theorem primeMoment_abs375 (l η ε X α : ℝ) :
    primeMoment353 |l| η ε X α = primeMoment353 l η ε X α := by
  by_cases hl : 0 ≤ l
  · rw [abs_of_nonneg hl]
  · rw [abs_of_neg (lt_of_not_ge hl)]
    have he : primeMoment353 (-l) η ε X α = primeMoment353 l η ε X (-α) := by
      simp only [primeMoment353, neg_mul, mul_neg, kernel293, Real.sinc_neg]
    rw [he, primeMoment_even375]

/-- P0079 page 10, Section 5, the change of variable before the unit intervals.
Rescaling the phase divides eta by the coefficient and multiplies the kernel by its square. -/
theorem primeMoment_scale375 (l η ε X α : ℝ) (hl : l ≠ 0) :
    primeMoment353 l η ε X α =
      l ^ 2 * primeMoment353 1 (η / l) ε X (l * α) := by
  have harg : Real.pi * (η / l) * (l * α) = Real.pi * η * α := by
    field_simp
  simp only [primeMoment353, one_mul, kernel293, harg]
  field_simp

/-- P0079 page 10, Section 5. The positive tail estimate holds for any
positive coefficient once its rescaled cutoff is at least one. -/
theorem primeMoment_positive_tail375 (l ε X η a : ℝ) (hl : 0 < l)
    (hX : 2 ≤ X) (ha : 1 ≤ l * a) :
    (∫ α in Set.Ioi a, primeMoment353 l η ε X α) ≤
      2 * ((1 / Real.pi ^ 2) * (log 4 * X * log X)) / a := by
  have ha0 : 0 < a := by nlinarith only [hl, ha]
  have hfun : (fun α => primeMoment353 l η ε X α) =
      (fun α => l ^ 2 * primeMoment353 1 (η / l) ε X (l * α)) :=
    funext (fun α => primeMoment_scale375 l η ε X α hl.ne')
  rw [hfun, integral_const_mul, integral_comp_mul_left_Ioi _ a hl, smul_eq_mul]
  calc
    _ ≤ l ^ 2 * (l⁻¹ *
        (2 * ((1 / Real.pi ^ 2) * (log 4 * X * log X)) / (l * a))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left
        (primeMoment_unit_tail375 ε X (η / l) (l * a) hX ha) (inv_nonneg.mpr hl.le)
    _ = _ := by field_simp

/-- P0079 page 10, Section 5. Reflection doubles the positive tail bound.
Both signs of the prime coefficient are included through its absolute value. -/
theorem primeMoment_tail375 (l ε X η a : ℝ) (hl : l ≠ 0)
    (hX : 2 ≤ X) (ha : 1 ≤ |l| * a) :
    (∫ α in {α : ℝ | a < |α|}, primeMoment353 l η ε X α) ≤
      4 * ((1 / Real.pi ^ 2) * (log 4 * X * log X)) / a := by
  have habs : 0 < |l| := abs_pos.mpr hl
  have ha0 : 0 < a := by nlinarith only [habs, ha]
  have hs : {α : ℝ | a < |α|} = Set.Iio (-a) ∪ Set.Ioi a := by
    ext α
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hd : Disjoint (Set.Iio (-a)) (Set.Ioi a) := by
    rw [Set.disjoint_left]
    intro α hleft hright
    simp only [Set.mem_Iio, Set.mem_Ioi] at hleft hright
    linarith
  have hi := primeMoment_integrable353 l η ε X
  have he : (∫ α in Set.Iio (-a), primeMoment353 l η ε X α) =
      ∫ α in Set.Ioi a, primeMoment353 l η ε X α := by
    rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi]
    exact setIntegral_congr_fun measurableSet_Ioi (fun α _ => primeMoment_even375 l η ε X α)
  have hp : (∫ α in Set.Ioi a, primeMoment353 l η ε X α) ≤
      2 * ((1 / Real.pi ^ 2) * (log 4 * X * log X)) / a := by
    have hf : primeMoment353 |l| η ε X = primeMoment353 l η ε X :=
      funext (primeMoment_abs375 l η ε X)
    rw [← hf]
    exact primeMoment_positive_tail375 |l| ε X η a habs hX ha
  rw [hs, setIntegral_union hd measurableSet_Ioi hi.integrableOn hi.integrableOn, he]
  calc
    _ ≤ 2 * ((1 / Real.pi ^ 2) * (log 4 * X * log X)) / a +
        2 * ((1 / Real.pi ^ 2) * (log 4 * X * log X)) / a := add_le_add hp hp
    _ = _ := by ring

/-- P0079 page 10, Section 5, the chain ending in X divided by log X.
The exact single-prime target follows from periodicity, Chebyshev's bound,
the two-sided tail bound and logarithmic growth. No analytic OPEN leaf is used. -/
theorem trivial_moment375 (s : ℕ) (l : ℝ) (μ : ℕ → ℝ) (η ε : ℝ)
    (hs : 2 ≤ s) (hl : l ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℝ in atTop,
      (∫ α in trivial293 X (cutoff293 s μ ε X), primeMoment353 l η ε X α) ≤
        C * X / log X := by
  have hmass : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  let A : ℝ := 1 / (2 * log 2)
  have hA : 0 < A := by dsimp [A]; positivity
  let C : ℝ := (4 * (1 / Real.pi ^ 2) * log 4) / A ^ 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have hLt := cutoff_tendsto353 s μ ε hmass hε
  have habs : 0 < |l| := abs_pos.mpr hl
  filter_upwards [trivial_eventually_tail353 s μ ε hmass hε,
    cutoff_log_lower293 s μ ε hmass hε,
    hLt.eventually (eventually_ge_atTop (1 : ℝ)),
    hLt.eventually (eventually_ge_atTop (1 / |l|)),
    eventually_ge_atTop (2 : ℝ)] with X htail hlogL hL1 hLl hX
  have hlog : 0 < log X := log_pos (by linarith)
  have hL0 : 0 < cutoff293 s μ ε X := by linarith
  have hscaledL : 1 ≤ |l| * cutoff293 s μ ε X := by
    have H := (div_le_iff₀ habs).mp hLl
    linarith only [H]
  have hLsq : cutoff293 s μ ε X ≤ (cutoff293 s μ ε X) ^ 2 := by nlinarith only [hL1]
  have hscaled : 1 ≤ |l| * (cutoff293 s μ ε X) ^ 2 := by
    nlinarith only [hscaledL, mul_le_mul_of_nonneg_left hLsq habs.le]
  rw [htail]
  refine (primeMoment_tail375 l ε X η ((cutoff293 s μ ε X) ^ 2) hl hX hscaled).trans ?_
  have hsq : (A * log X) ^ 2 ≤ (cutoff293 s μ ε X) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlogL 2
  calc
    _ ≤ 4 * ((1 / Real.pi ^ 2) * (log 4 * X * log X)) / (A * log X) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
    _ = C * X / log X := by dsimp [C]; field_simp <;> ring

/-- P0079 page 10, Section 5, display 17. The exact trivial-arc target
now follows from the proved single-prime moment estimate. -/
theorem trivial_small375 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : l1 ≠ 0) (h2 : l2 ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in trivial293 X (cutoff293 s μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
        δ * X * (cutoff293 s μ ε X) ^ s := by
  obtain ⟨C1, hC1, H1⟩ := trivial_moment375 s l1 μ η ε hs h1 hμ hη hε hε'
  obtain ⟨C2, hC2, H2⟩ := trivial_moment375 s l2 μ η ε hs h2 hμ hη hε hε'
  have hmass : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  intro δ hδ
  have Hlog := tendsto_log_atTop.eventually
    (eventually_ge_atTop ((C1 + C2) / (2 * δ)))
  filter_upwards [H1, H2, Hlog, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop ((2 * ∑ i : Fin s, |μ i|) / ε)] with X hm1 hm2 hlogbound hX hmassX
  have hL : 0 ≤ cutoff293 s μ ε X := cutoff_nonneg293 s μ ε X hmass
    (by simpa [mul_comm] using (div_le_iff₀ hε).mp hmassX)
  have hlog : 0 < log X := log_pos (by linarith)
  have hmean : (∫ α in trivial293 X (cutoff293 s μ ε X), primeMoment353 l1 η ε X α) +
      (∫ α in trivial293 X (cutoff293 s μ ε X), primeMoment353 l2 η ε X α) ≤ 2 * δ * X := by
    calc
      _ ≤ C1 * X / log X + C2 * X / log X := add_le_add hm1 hm2
      _ = ((C1 + C2) / log X) * X := by ring
      _ ≤ (2 * δ) * X := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        apply (div_le_iff₀ hlog).mpr
        have H := (div_le_iff₀ (by positivity : 0 < 2 * δ)).mp hlogbound
        nlinarith only [H]
  calc
    _ ≤ (cutoff293 s μ ε X) ^ s / 2 *
        ((∫ α in trivial293 X (cutoff293 s μ ε X), primeMoment353 l1 η ε X α) +
          (∫ α in trivial293 X (cutoff293 s μ ε X), primeMoment353 l2 η ε X α)) :=
      trivial_reduction353 s l1 l2 μ γ η ε X hL
    _ ≤ (cutoff293 s μ ε X) ^ s / 2 * (2 * δ * X) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = _ := by ring

end LeanLab.LZPowersOfTwo
