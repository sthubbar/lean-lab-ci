/-
AI-written Lean code, Gemini task1062.
Decomposition of LowerSieveInput.
Goldbach is open.
-/
import LeanLab.AlmostPrimeSums.TogashiUchiyamaScale

open Filter Real

noncomputable section
namespace LeanLab.AlmostPrimeSums

open TogashiUchiyamaScale

/-- LEAF 1: p. 64. Main term lower bound. -/
theorem lower_sieve_main_term (T ε : ℝ) :
    ∀ᶠ N : ℕ in atTop, Even N → 26.4612 * M T N ≤ (TogashiUchiyamaSection5.S1set N).card + ε * M T N / 2 := sorry

/-- LEAF 2: p. 64. Error term scaling. -/
theorem lower_sieve_error_term (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ε * M T N / 2 < ε * M T N := by
  have hm := section5_size_inputs hT hε
  filter_upwards [hm] with N hN he
  have hM : 0 < M T N := by linarith [hN.2]
  nlinarith

/-- LEAF 3: p. 64. Sieve setup condition. -/
theorem lower_sieve_setup (T ε : ℝ) :
    ∀ᶠ N : ℕ in atTop, 0 ≤ M T N := sorry

/-- LEAF 4: p. 64. Extracted constant. -/
theorem lower_sieve_constant (T ε : ℝ) :
    26.4612 - ε / 2 < 26.4612 := sorry

/-- LEAF 5: p. 64. Combination. -/
theorem lower_sieve_combination (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) :
    LowerSieveInput T ε := by
  unfold LowerSieveInput
  have h1 := lower_sieve_main_term T ε
  have h2 := lower_sieve_error_term T ε hT hε
  filter_upwards [h1, h2] with N hh1 hh2
  intro he
  have h3 := hh1 he
  have h4 := hh2 he
  linarith

end LeanLab.AlmostPrimeSums
