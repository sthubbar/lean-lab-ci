/-
P0079 page 10, Section 5, reduction to a weighted prime second moment.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.CountBounds293

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

/-- LEAF. P0079 page 10, Section 5, the chain of estimates ending in
X divided by log X. Periodicity, the kernel tail and the prime number theorem
bound the trivial-arc second moment of one prime sum. This leaf contains no
product of two prime sums and no shift character. -/
theorem trivial_moment353 (s : ℕ) (l : ℝ) (μ : ℕ → ℝ) (η ε : ℝ)
    (hs : 2 ≤ s) (hl : l ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℝ in atTop,
      (∫ α in trivial293 X (cutoff293 s μ ε X), primeMoment353 l η ε X α) ≤
        C * X / log X := by
  sorry

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
