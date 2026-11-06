import LeanLab.HelfgottMajor.Sampling431

/-!
Separate positive and negative zero sampling on book Part IV pages 433 and 434.
Each OPEN child treats just one signed half of the middle zero range.
The original sealed sampling leaf is unchanged.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- The positive middle zero contribution on book page 433 before display 16.26. -/
noncomputable def positiveMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => mellinMassTerm χ δ ρ.val) ρ

/-- The negative middle zero contribution on book page 434 after display 16.26. -/
noncomputable def negativeMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
    Set.indicator {ρ | ρ.val.im < -1} (fun ρ => mellinMassTerm χ δ ρ.val) ρ

/-- The middle range is the disjoint union of its two signed halves.
CONDITIONAL ON hzeros for summability. Book pages 433 and 434.
-/
theorem middle_mass_signed_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T = positiveMass χ δ T + negativeMass χ δ T := by
  classical
  have hm : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => mellinMassTerm χ δ ρ.val) := by
    apply (Zeros269.low_zero_terms_summable χ δ 1 T hzeros).norm.congr
    intro ρ
    simp [zeroTerm, mellinMassTerm, nsmul_eq_mul]
  unfold positiveMass negativeMass middleMass
  rw [← (hm.indicator _).tsum_add (hm.indicator _)]
  apply tsum_congr
  intro ρ
  by_cases hp : 1 < ρ.val.im
  · have hn : ¬ρ.val.im < -1 := by linarith
    have ha : ¬|ρ.val.im| ≤ 1 := by
      intro ha
      have hh := (abs_le.mp ha).2
      linarith
    simp [Set.indicator, hp, hn, ha]
  · by_cases hn : ρ.val.im < -1
    · have ha : ¬|ρ.val.im| ≤ 1 := by
        intro ha
        have hh := (abs_le.mp ha).1
        linarith
      simp [Set.indicator, hp, hn, ha]
    · have ha : |ρ.val.im| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      simp [Set.indicator, hp, hn, ha]

/-- The signed range is empty when T ≤ 1.
This gives the trivial zero case of the raw sampling bound. -/
theorem positive_sampling_raw_empty {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : T ≤ 1) (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T) :
    positiveMass χ δ T = 0 := by
  have hT' : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, ¬ (1 < ρ.val.im) := by
    intro ρ
    have hmem := ρ.property.2.2.2
    intro hlt
    have : 1 < |ρ.val.im| := by
      have hpos : 0 ≤ ρ.val.im := by linarith
      rw [abs_of_nonneg hpos]
      exact hlt
    linarith
  unfold positiveMass
  apply tsum_eq_zero_of_not_nonempty
  intro ρ
  simp [Set.indicator, hT' ρ]

/-- The signed range is empty when T ≤ 1.
This gives the trivial zero case of the raw sampling bound. -/
theorem negative_sampling_raw_empty {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : T ≤ 1) (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T) :
    negativeMass χ δ T = 0 := by
  have hT' : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, ¬ (ρ.val.im < -1) := by
    intro ρ
    have hmem := ρ.property.2.2.2
    intro hlt
    have : 1 ≤ |ρ.val.im| := by
      have hneg : ρ.val.im ≤ 0 := by linarith
      rw [abs_of_nonpos hneg]
      linarith
    linarith
  unfold negativeMass
  apply tsum_eq_zero_of_not_nonempty
  intro ρ
  simp [Set.indicator, hT' ρ]

/-- LEAF. Book pages 433 and 434, display 16.26 before the scalar weight estimates.
Only the positive signed zero samples are bounded. Both scalar weight integrals remain explicit.
The continuous cutoff justification remains a source QUESTION.

BLOCKED OUT OF REACH: requires the "continuous cutoff" lemma that relates
∑_{ρ: 1<ρ.im≤T} mellinMassTerm to the integral ∫₁^T (log term)² dt.
This is the analytic crux of display 16.26. No per-zero bound lemma exists in the codebase
to bypass it.
-/
theorem positive_sampling_raw (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    positiveMass χ δ T ≤
      sqrt (lineEnergy δ 1) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) +
      sqrt (derivativeEnergy δ 1) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ *
        (0.15 * log (q : ℝ) + 3.389) := by
  by_cases hT' : T ≤ 1
  · have hzero := positive_sampling_raw_empty q χ δ T hT' hlarge
    have hRHS_nonneg : 0 ≤ sqrt (lineEnergy δ 1) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) +
      sqrt (derivativeEnergy δ 1) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ *
        (0.15 * log (q : ℝ) + 3.389) := by
      positivity
    linarith
  · -- T > 1: the signed range may be nonempty
    -- The analytic estimate requires the "continuous cutoff" step
    sorry

/-- LEAF. Book pages 433 and 434, display 16.26 before the scalar weight estimates.
Only the negative signed zero samples are bounded. Both scalar weight integrals remain explicit.
The continuous cutoff justification remains a source QUESTION.

BLOCKED OUT OF REACH: same bridge lemma needed as positive_sampling_raw, sign-flipped.
-/
theorem negative_sampling_raw (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    negativeMass χ δ T ≤
      sqrt (lineEnergy δ (-1)) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) +
      sqrt (derivativeEnergy δ (-1)) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ *
        (0.15 * log (q : ℝ) + 3.389) := by
  by_cases hT' : T ≤ 1
  · have hzero := negative_sampling_raw_empty q χ δ T hT' hlarge
    have hRHS_nonneg : 0 ≤ sqrt (lineEnergy δ (-1)) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) +
      sqrt (derivativeEnergy δ (-1)) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ *
        (0.15 * log (q : ℝ) + 3.389) := by
      positivity
    linarith
  · -- T > 1: the signed range may be nonempty
    sorry

/-- LEAF. Book pages 433 and 434, display 16.26.
The positive half of the zero sampling estimate, before summing the two signs.
No opposite sign energy or opposite sign endpoint is used.
The cutoff justification in the written proof remains a recorded QUESTION.
-/
theorem positive_sampling_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    positiveMass χ δ T ≤
      sqrt (lineEnergy δ 1) / (2 * π) * sqrt T *
        log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) +
      sqrt (derivativeEnergy δ 1) *
        (0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ *
        (0.15 * log (q : ℝ) + 3.389) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hM := mul_le_mul_of_nonneg_left
    (Sampling431.main_weight_root_bound (q : ℝ) T hq hT hlarge)
    (by positivity : 0 ≤ sqrt (lineEnergy δ 1) / (2 * π))
  have hE := mul_le_mul_of_nonneg_left
    (Sampling431.error_weight_root_bound (q : ℝ) T hq hT hlarge)
    (sqrt_nonneg (derivativeEnergy δ 1))
  calc
    _ ≤ _ := positive_sampling_raw q χ hχ δ T hT hlarge hzeros
    _ ≤ _ := add_le_add (add_le_add hM hE) le_rfl
    _ = _ := by ring

/-- LEAF. Book pages 433 and 434, display 16.26.
The negative half of the zero sampling estimate, before summing the two signs.
No opposite sign energy or opposite sign endpoint is used.
The cutoff justification in the written proof remains a recorded QUESTION.
-/
theorem negative_sampling_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    negativeMass χ δ T ≤
      sqrt (lineEnergy δ (-1)) / (2 * π) * sqrt T *
        log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) +
      sqrt (derivativeEnergy δ (-1)) *
        (0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T +
      ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ *
        (0.15 * log (q : ℝ) + 3.389) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hM := mul_le_mul_of_nonneg_left
    (Sampling431.main_weight_root_bound (q : ℝ) T hq hT hlarge)
    (by positivity : 0 ≤ sqrt (lineEnergy δ (-1)) / (2 * π))
  have hE := mul_le_mul_of_nonneg_left
    (Sampling431.error_weight_root_bound (q : ℝ) T hq hT hlarge)
    (sqrt_nonneg (derivativeEnergy δ (-1)))
  calc
    _ ≤ _ := negative_sampling_raw q χ hχ δ T hT hlarge hzeros
    _ ≤ _ := add_le_add (add_le_add hM hE) le_rfl
    _ = _ := by ring

/-- Exactly Decomp389b.middle_sampling_bound, assembled from its two signed halves.
Book pages 433 and 434. The two signed children remain OPEN.
-/
theorem middle_sampling_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1))) / (2 * π) * sqrt T *
        log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) +
      (sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1))) *
        (0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T +
      (‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ +
        ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖) *
        (0.15 * log (q : ℝ) + 3.389) := by
  rw [middle_mass_signed_split χ δ T hzeros]
  have hp := positive_sampling_bound q χ hχ δ T hT hlarge hzeros
  have hn := negative_sampling_bound q χ hχ δ T hT hlarge hzeros
  calc
    _ ≤ _ := add_le_add hp hn
    _ = _ := by ring

end LeanLab.HelfgottMajor.Decomp431a
