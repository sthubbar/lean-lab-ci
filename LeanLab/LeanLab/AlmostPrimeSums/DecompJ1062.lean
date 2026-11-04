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

/-- LEAF 1: p. 64, Lemma 4 of P0072, `S₁ > 26.4612 A_N φ(N)/log² N + O(φ(N) (log log N)²/log³ N)`.
DECISION U-1614: `hT`, `hε` and `hTpaper` added. `T` must be the product of p. 61, since `M T N` scales
as `1/T`, and `ε` must be positive to absorb the error term. -/
theorem lower_sieve_main_term (T ε : ℝ) (_hT : 0 < T) (_hε : 0 < ε)
    (_hTpaper : HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) T) :
    ∀ᶠ N : ℕ in atTop, Even N → 26.4612 * M T N ≤ (TogashiUchiyamaSection5.S1set N).card + ε * M T N / 2 := sorry

/-- LEAF 2: p. 64. Error term scaling. -/
theorem lower_sieve_error_term (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ε * M T N / 2 < ε * M T N := by
  have hm := section5_size_inputs hT hε
  filter_upwards [hm] with N hN he
  have hM : 0 < M T N := by linarith [hN.2]
  nlinarith

/-- LEAF 3: p. 64. Sieve setup condition. DECISION U-1614: `0 < T` added, the old form is false at
`T = -1`, `Audit1614.old_lower_sieve_setup_false`. PROVED. -/
theorem lower_sieve_setup (T : ℝ) (hT : 0 < T) :
    ∀ᶠ N : ℕ in atTop, 0 ≤ M T N := by
  filter_upwards [section5_size_inputs hT one_pos] with N hN
  linarith [hN.2]

/-- LEAF 4: p. 64. Extracted constant. DECISION U-1614: `0 < ε` added, the old form is false at
`ε = 0`, `Audit1614.old_lower_sieve_constant_false`. PROVED. -/
theorem lower_sieve_constant (ε : ℝ) (hε : 0 < ε) :
    26.4612 - ε / 2 < 26.4612 := by linarith

/-- LEAF 5: p. 64. Combination. -/
theorem lower_sieve_combination (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hTpaper : HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) T) :
    LowerSieveInput T ε := by
  unfold LowerSieveInput
  have h1 := lower_sieve_main_term T ε hT hε hTpaper
  have h2 := lower_sieve_error_term T ε hT hε
  filter_upwards [h1, h2] with N hh1 hh2
  intro he
  have h3 := hh1 he
  have h4 := hh2 he
  linarith

end LeanLab.AlmostPrimeSums
