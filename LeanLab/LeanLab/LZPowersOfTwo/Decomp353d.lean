/-
P0079 page 10, Section 5, reduction to a weighted prime second moment.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.CountBounds293
import LeanLab.LZPowersOfTwo.PrimeMoment353
import LeanLab.LZPowersOfTwo.TailSummation418
import LeanLab.LZPowersOfTwo.ArcGeometry353

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 10, Section 5. The weighted second moment of one prime sum. -/
def primeMoment353 (l η ε X α : ℝ) : ℝ :=
  ‖primeSum293 ε X (l * α)‖ ^ 2 * kernel293 η α

/-- P0079 page 10, Section 5. The weighted prime second moment is integrable. -/
theorem primeMoment_integrable353 (l η ε X : ℝ) :
    Integrable (primeMoment353 l η ε X) := by
  let P := ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)), |log p|
  have hP : 0 ≤ P := sum_nonneg (fun _ _ => abs_nonneg _)
  have hc : Continuous (fun α : ℝ => ‖primeSum293 ε X (l * α)‖ ^ 2) := by
    unfold primeSum293 character293
    fun_prop
  apply (kernel_integrable293 η).bdd_mul (c := P ^ 2) hc.aestronglyMeasurable
  apply Eventually.of_forall
  intro α
  change |‖primeSum293 ε X (l * α)‖ ^ 2| ≤ P ^ 2
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (primeSum_norm_le293 ε X (l * α)) 2

/-- P0079 page 10, Section 5. Bounding the power sums by L and applying
2 a b at most a squared plus b squared gives this pointwise majorant. -/
theorem integrand_norm_le353 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X α : ℝ)
    (hL : 0 ≤ cutoff293 s μ ε X) :
    ‖integrand293 s l1 l2 μ γ η ε X α‖ ≤
      (cutoff293 s μ ε X) ^ s / 2 *
        (primeMoment353 l1 η ε X α + primeMoment353 l2 η ε X α) := by
  have hG : ‖∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ ≤
      (cutoff293 s μ ε X) ^ s := by
    calc
      _ ≤ ∏ i : Fin s, ‖powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ := norm_prod_le _ _
      _ ≤ ∏ _ : Fin s, cutoff293 s μ ε X := by
        apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro i hi
        refine (powerSum_norm_le293 _ _).trans ?_
        simpa using Nat.floor_le hL
      _ = _ := by simp
  have hab : ‖primeSum293 ε X (l1 * α)‖ * ‖primeSum293 ε X (l2 * α)‖ ≤
      (‖primeSum293 ε X (l1 * α)‖ ^ 2 + ‖primeSum293 ε X (l2 * α)‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖primeSum293 ε X (l1 * α)‖ - ‖primeSum293 ε X (l2 * α)‖)]
  simp only [integrand293, norm_mul, character_norm293, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg293 η α)]
  calc
    _ ≤ ((‖primeSum293 ε X (l1 * α)‖ ^ 2 + ‖primeSum293 ε X (l2 * α)‖ ^ 2) / 2) *
        (cutoff293 s μ ε X) ^ s * kernel293 η α :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hab hG (norm_nonneg _) (by positivity)) (kernel_nonneg293 η α)
    _ = _ := by unfold primeMoment353; ring

/-- P0079 page 10, Section 5. Real logarithmic weights make the prime-sum norm even. -/
theorem primeSum_norm_neg353d (ε X α : ℝ) :
    ‖primeSum293 ε X (-α)‖ = ‖primeSum293 ε X α‖ := by
  have hc : primeSum293 ε X (-α) = starRingEnd ℂ (primeSum293 ε X α) := by
    simp only [primeSum293, mul_neg, character_neg353, map_sum, map_mul, Complex.conj_ofReal]
  rw [hc, Complex.norm_conj]

/-- P0079 page 10, Section 5. The kernel-weighted prime moment is even. -/
theorem primeMoment_even353d (l η ε X α : ℝ) :
    primeMoment353 l η ε X (-α) = primeMoment353 l η ε X α := by
  simp only [primeMoment353, mul_neg, primeSum_norm_neg353d, kernel293, Real.sinc_neg]

/-- P0079 page 10, Section 5. Replacing lambda by its absolute value preserves the moment. -/
theorem primeMoment_abs353d (l η ε X α : ℝ) :
    primeMoment353 |l| η ε X α = primeMoment353 l η ε X α := by
  rcases le_total 0 l with hl | hl
  · rw [abs_of_nonneg hl]
  · rw [abs_of_nonpos hl]
    simp only [primeMoment353, neg_mul, primeSum_norm_neg353d]

/-- P0079 page 10, Section 5, the change of variable before the unit-interval sum.
A positive lambda changes the period to its reciprocal. -/
theorem prime_second_moment_scaled353d (l ε X a : ℝ) (hl : 0 < l) :
    (∫ α in a..a + 1 / l, ‖primeSum293 ε X (l * α)‖ ^ 2) =
      (1 / l) * ∑ p ∈ (range (⌊X⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)), (log p) ^ 2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ => ‖primeSum293 ε X t‖ ^ 2) hl.ne']
  rw [show l * (a + 1 / l) = l * a + 1 by field_simp]
  rw [prime_second_moment_unit353]
  simp only [inv_eq_one_div, smul_eq_mul]

/-- P0079 page 10, Section 5. Kernel decay bounds each interval of the scaled period. -/
theorem primeMoment_scaled_unit_le353d (l ε X η a : ℝ)
    (hl : 0 < l) (hX : 2 ≤ X) (ha : 0 < a) :
    (∫ α in a..a + 1 / l, primeMoment353 l η ε X α) ≤
      ((1 / Real.pi ^ 2) / a ^ 2) * (1 / l) * (log 4 * X * log X) := by
  have hk : ∀ α ∈ Set.Icc a (a + 1 / l),
      kernel293 η α ≤ (1 / Real.pi ^ 2) / a ^ 2 := by
    intro α hα
    apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
    have hsq : a ^ 2 ≤ α ^ 2 := by nlinarith [hα.1]
    nlinarith [kernel_mul_sq_le293 η α, kernel_nonneg293 η α]
  have hs : Continuous (fun α : ℝ => ‖primeSum293 ε X (l * α)‖ ^ 2) := by
    unfold primeSum293 character293
    fun_prop
  have hker : Continuous (kernel293 η) := by unfold kernel293; fun_prop
  calc
    _ ≤ ∫ α in a..a + 1 / l,
        ((1 / Real.pi ^ 2) / a ^ 2) * ‖primeSum293 ε X (l * α)‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on (by linarith [one_div_pos.mpr hl])
        ((hs.mul hker).intervalIntegrable _ _)
        ((hs.const_mul _).intervalIntegrable _ _)
      intro α hα
      change ‖primeSum293 ε X (l * α)‖ ^ 2 * kernel293 η α ≤ _
      calc
        _ ≤ ‖primeSum293 ε X (l * α)‖ ^ 2 * ((1 / Real.pi ^ 2) / a ^ 2) :=
          mul_le_mul_of_nonneg_left (hk α hα) (sq_nonneg _)
        _ = _ := mul_comm _ _
    _ = ((1 / Real.pi ^ 2) / a ^ 2) * (1 / l) *
        (∫ α in -(1 / 2 : ℝ)..(1 / 2 : ℝ), ‖primeSum293 ε X α‖ ^ 2) := by
      rw [intervalIntegral.integral_const_mul, prime_second_moment_scaled353d l ε X a hl,
        prime_second_moment353]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (prime_second_moment_le353 ε X hX) (by positivity)

/-- P0079 page 10, Section 5. Summing the scaled unit intervals bounds the positive tail. -/
theorem primeMoment_positive_tail353d (l ε X η R : ℝ)
    (hl : 0 < l) (hX : 2 ≤ X) (hR : 1 / l ≤ R) :
    (∫ α in Set.Ioi R, primeMoment353 l η ε X α) ≤
      (2 / Real.pi ^ 2) * (log 4 * X * log X) / R := by
  let B := log 4 * X * log X
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (log_nonneg (by norm_num)) (by linarith))
      (log_nonneg (by linarith))
  have hh : 0 < 1 / l := one_div_pos.mpr hl
  have hR0 : 0 < R := hh.trans_le hR
  have hinterval (n : ℕ) :
      (∫ α in (R + (n : ℝ) * (1 / l))..(R + ((n + 1 : ℕ) : ℝ) * (1 / l)),
        primeMoment353 l η ε X α) ≤
          ((1 / Real.pi ^ 2) * (1 / l) * B) / (R + (n : ℝ) * (1 / l)) ^ 2 := by
    have hn : 0 ≤ (n : ℝ) * (1 / l) := mul_nonneg (Nat.cast_nonneg _) hh.le
    have ha : 0 < R + (n : ℝ) * (1 / l) := by linarith
    have H := primeMoment_scaled_unit_le353d l ε X η (R + (n : ℝ) * (1 / l)) hl hX ha
    have he : R + ((n + 1 : ℕ) : ℝ) * (1 / l) =
        (R + (n : ℝ) * (1 / l)) + 1 / l := by push_cast; ring
    rw [he]
    convert H using 1
    dsimp [B]
    ring
  calc
    _ ≤ 2 * ((1 / Real.pi ^ 2) * (1 / l) * B) / ((1 / l) * R) :=
      integral_tail_of_interval_bounds418 _ (primeMoment_integrable353 l η ε X)
        R (1 / l) ((1 / Real.pi ^ 2) * (1 / l) * B) hh hR (by positivity) hinterval
    _ = _ := by dsimp [B]; field_simp

/-- P0079 page 10, Section 5. Both tails have an explicit bound for every nonzero lambda. -/
theorem primeMoment_tail353d (l ε X η R : ℝ)
    (hl : l ≠ 0) (hX : 2 ≤ X) (hR : 1 / |l| ≤ R) :
    (∫ α in {α : ℝ | R < |α|}, primeMoment353 l η ε X α) ≤
      (4 / Real.pi ^ 2) * (log 4 * X * log X) / R := by
  have habs : 0 < |l| := abs_pos.mpr hl
  have hR0 : 0 ≤ R := (one_div_pos.mpr habs).le.trans hR
  rw [integral_abs_tail_even418 _ (primeMoment_integrable353 l η ε X)
    (primeMoment_even353d l η ε X) R hR0]
  have H := primeMoment_positive_tail353d |l| ε X η R habs hX hR
  simp_rw [primeMoment_abs353d] at H
  calc
    _ ≤ 2 * ((2 / Real.pi ^ 2) * (log 4 * X * log X) / R) := by linarith
    _ = _ := by ring

/-- P0079 page 10, Section 5, the chain of estimates ending in
X divided by log X. Periodicity, the kernel tail and the prime number theorem
bound the trivial-arc second moment of one prime sum. This leaf contains no
product of two prime sums and no shift character. Formerly a LEAF, now proved
from primeMoment_tail353d, the arc geometry and the cutoff logarithm bound. -/
theorem trivial_moment353 (s : ℕ) (l : ℝ) (μ : ℕ → ℝ) (η ε : ℝ)
    (hs : 2 ≤ s) (hl : l ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℝ in atTop,
      (∫ α in trivial293 X (cutoff293 s μ ε X), primeMoment353 l η ε X α) ≤
        C * X / log X := by
  let a : ℝ := 1 / (2 * log 2)
  let K : ℝ := (4 / Real.pi ^ 2) * log 4
  have ha : 0 < a := by dsimp [a]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmass : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  refine ⟨K / a ^ 2, by positivity, ?_⟩
  filter_upwards [trivial_eventually_tail353 s μ ε hmass hε,
    (cutoff_tendsto353 s μ ε hmass hε).eventually
      (eventually_ge_atTop (max 1 (1 / |l|))),
    cutoff_log_lower293 s μ ε hmass hε,
    eventually_ge_atTop (2 : ℝ)] with X ht hL hlogL hX
  have hL1 : 1 ≤ cutoff293 s μ ε X := (le_max_left _ _).trans hL
  have hLl : 1 / |l| ≤ cutoff293 s μ ε X := (le_max_right _ _).trans hL
  have hL0 : 0 < cutoff293 s μ ε X := by linarith
  have hlog : 0 < log X := log_pos (by linarith)
  have hR : 1 / |l| ≤ (cutoff293 s μ ε X) ^ 2 := by nlinarith
  rw [ht]
  calc
    _ ≤ (4 / Real.pi ^ 2) * (log 4 * X * log X) / (cutoff293 s μ ε X) ^ 2 :=
      primeMoment_tail353d l ε X η _ hl hX hR
    _ = K * X * log X / (cutoff293 s μ ε X) ^ 2 := by dsimp [K]; ring
    _ ≤ (K / a ^ 2) * X / log X := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hL0) hlog).mpr
      have hpow : (a * log X) ^ 2 ≤ (cutoff293 s μ ε X) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hlogL 2
      calc
        K * X * log X * log X = (K / a ^ 2 * X) * (a * log X) ^ 2 := by
          field_simp
        _ ≤ (K / a ^ 2 * X) * (cutoff293 s μ ε X) ^ 2 :=
          mul_le_mul_of_nonneg_left hpow (by positivity)

/-- P0079 page 10, Section 5. The norm of the trivial integral is bounded
by the sum of its two weighted prime second moments times L to the s over two. -/
theorem trivial_reduction353 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X : ℝ)
    (hL : 0 ≤ cutoff293 s μ ε X) :
    ‖∫ α in trivial293 X (cutoff293 s μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
      (cutoff293 s μ ε X) ^ s / 2 *
        ((∫ α in trivial293 X (cutoff293 s μ ε X), primeMoment353 l1 η ε X α) +
          (∫ α in trivial293 X (cutoff293 s μ ε X), primeMoment353 l2 η ε X α)) := by
  have h1 := (primeMoment_integrable353 l1 η ε X).integrableOn
    (s := trivial293 X (cutoff293 s μ ε X))
  have h2 := (primeMoment_integrable353 l2 η ε X).integrableOn
    (s := trivial293 X (cutoff293 s μ ε X))
  calc
    _ ≤ ∫ α in trivial293 X (cutoff293 s μ ε X), ‖integrand293 s l1 l2 μ γ η ε X α‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ α in trivial293 X (cutoff293 s μ ε X),
        (cutoff293 s μ ε X) ^ s / 2 *
          (primeMoment353 l1 η ε X α + primeMoment353 l2 η ε X α) := by
      apply integral_mono
        (integrand_integrable293 s l1 l2 μ γ η ε X).integrableOn.norm
        ((h1.add h2).const_mul _)
      exact fun α => integrand_norm_le353 s l1 l2 μ γ η ε X α hL
    _ = _ := by rw [integral_const_mul, integral_add h1 h2]

/-- P0079 page 10, Section 5 and display 17. CONDITIONAL ON trivial_moment353.
The exact trivial target follows from the second moments and logarithmic growth. -/
theorem trivial_small353 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : l1 ≠ 0) (h2 : l2 ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in trivial293 X (cutoff293 s μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
        δ * X * (cutoff293 s μ ε X) ^ s := by
  obtain ⟨C1, hC1, H1⟩ := trivial_moment353 s l1 μ η ε hs h1 hμ hη hε hε'
  obtain ⟨C2, hC2, H2⟩ := trivial_moment353 s l2 μ η ε hs h2 hμ hη hε hε'
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
