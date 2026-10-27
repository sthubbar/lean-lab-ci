/-
AI-written Lean code, OpenAI Codex, task33, 2026-10-23, T1.
P0072 Togashi and Uchiyama 1964, pp. 61 to 62 and p. 67.
T is the fixed positive infinite product in the paper's C_N.
The final wrapper is conditional on two named sieve inputs.
Goldbach is open.
-/
import LeanLab.AlmostPrimeSums.S3Small
import LeanLab.AlmostPrimeSums.TogashiUchiyamaEpsilon

open Finset Real Filter

noncomputable section
namespace LeanLab.AlmostPrimeSums.TogashiUchiyamaScale

/-- The finite product in C_N on p. 61. -/
def Q (N : ℕ) : ℝ := ∏ p ∈ N.primeFactors.filter (2 < ·), ((p : ℝ) - 2) / p

/-- T stands for the fixed positive infinite product in C_N on p. 61. -/
def Cpaper (T : ℝ) (N : ℕ) : ℝ := T * Q N / 8

/-- The normalization on p. 62. -/
def Apaper (T : ℝ) (N : ℕ) : ℝ := (2 * exp (2 * eulerMascheroniConstant) * Cpaper T N)⁻¹

def M (T : ℝ) (N : ℕ) : ℝ := Apaper T N * N.totient / (log N) ^ 2

def a (T : ℝ) : ℝ := 4 * T⁻¹ * exp (-(2 * eulerMascheroniConstant))

lemma Q_bounds (N : ℕ) : 0 < Q N ∧ Q N ≤ 1 := by
  constructor
  · apply prod_pos
    intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    exact div_pos (by linarith) (by linarith)
  · apply prod_le_one₀
    · intro p hp
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
      exact div_nonneg (by linarith) (by linarith)
    · intro p hp
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
      exact (div_le_one (by linarith)).mpr (by linarith)

lemma a_pos {T : ℝ} (hT : 0 < T) : 0 < a T := by unfold a; positivity

lemma a_le_Apaper {T : ℝ} (hT : 0 < T) (N : ℕ) : a T ≤ Apaper T N := by
  obtain ⟨hQ, hQ1⟩ := Q_bounds N
  have hInv : 1 ≤ (Q N)⁻¹ := (one_le_inv₀ hQ).mpr hQ1
  have he := TogashiUchiyamaConvex.lemma2_constant hT hQ
  change a T * (Q N)⁻¹ = Apaper T N at he
  rw [← he]
  exact le_mul_of_one_le_right (a_pos hT).le hInv

lemma M_lower {T : ℝ} (hT : 0 < T) (N : ℕ) :
    a T * (N.totient : ℝ) / (log N) ^ 2 ≤ M T N := by
  unfold M
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (a_le_Apaper hT N) (Nat.cast_nonneg _)) (sq_nonneg _)

/-- The S3 and large-size hypotheses on p. 67 hold for this actual normalization. -/
theorem section5_size_inputs {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ((TogashiUchiyamaSection5.S3set N).card : ℝ) ≤ ε * M T N ∧ 2 < 0.0269 * M T N := by
  have hM : ∀ᶠ N : ℕ in atTop, a T * (N.totient : ℝ) / (log N) ^ 2 ≤ M T N :=
    Eventually.of_forall (M_lower hT)
  exact (S3Small.S3_eventually_le_scaled (a_pos hT) hε hM).and
    (S3Small.scaled_size_eventually (a_pos hT) hM)

/-- Choose epsilon so every elementary error and size condition on p. 67 holds. -/
theorem epsilon_and_error_budget {T : ℝ} (hT : 0 < T) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 30 ∧ TogashiUchiyamaEpsilon.I ε < 79.3026 ∧
      ∀ᶠ N : ℕ in atTop,
        ((TogashiUchiyamaSection5.S3set N).card : ℝ) ≤ ε * M T N ∧
        3 * (ε * M T N) ≤ 0.0001 * M T N ∧ 2 < 0.0269 * M T N := by
  obtain ⟨η, hη, hη30, hI⟩ := TogashiUchiyamaEpsilon.exists_epsilon_interval
  let ε : ℝ := min η (1 / 30000)
  have hε : 0 < ε := lt_min hη (by norm_num)
  have hεη : ε ≤ η := min_le_left _ _
  have hεsmall : ε ≤ 1 / 30000 := min_le_right _ _
  refine ⟨ε, hε, hεη.trans_lt hη30, hI ε hε.le hεη, ?_⟩
  filter_upwards [section5_size_inputs hT hε] with N hs
  refine ⟨hs.1, ?_, hs.2⟩
  have hM : 0 < M T N := by linarith [hs.2]
  have h3ε : 3 * ε ≤ (0.0001 : ℝ) := by linarith
  nlinarith [mul_le_mul_of_nonneg_right h3ε hM.le]

/-- P0072 Lemma 4, as the remaining cited lower sieve input. -/
def LowerSieveInput (T ε : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, Even N →
    26.4612 * M T N - ε * M T N < (TogashiUchiyamaSection5.S1set N).card

/-- P0072 Section 3 summed upper sieve bound, as the remaining cited input. -/
def UpperSieveInput (T ε : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, Even N →
    ((∑ q ∈ TogashiUchiyamaSection5.Qset N, (TogashiUchiyamaSection5.Sq N q).card : ℕ) : ℝ) ≤
      TogashiUchiyamaEpsilon.I ε * M T N + 3 * (ε * M T N)

/-- CONDITIONAL ON LowerSieveInput and UpperSieveInput. All other Section 5 inputs are proved. -/
theorem section5_of_two_sieve_inputs {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 30000) (hI : TogashiUchiyamaEpsilon.I ε < 79.3026)
    (hlower : LowerSieveInput T ε) (hupper : UpperSieveInput T ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∃ n : ℕ,
      1 < n ∧ n < N - 1 ∧ n.Coprime N ∧ ArithmeticFunction.cardFactors n ≤ 3 ∧
        ArithmeticFunction.cardFactors (N - n) ≤ 3 := by
  filter_upwards [hlower, hupper, section5_size_inputs hT hε, eventually_ge_atTop 2]
    with N hl hu hs hN
  intro he
  have hM : 0 < M T N := by linarith [hs.2]
  have hE : 3 * (ε * M T N) ≤ 0.0001 * M T N := by
    have h3ε : 3 * ε ≤ (0.0001 : ℝ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h3ε hM.le]
  exact TogashiUchiyamaSection5.togashiUchiyama_of_sieve hN (hl he) (hu he) hI hs.1 hE hs.2

end LeanLab.AlmostPrimeSums.TogashiUchiyamaScale

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaScale.Q_bounds

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaScale.a_pos

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaScale.a_le_Apaper

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaScale.M_lower

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaScale.section5_size_inputs

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaScale.epsilon_and_error_budget

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaScale.section5_of_two_sieve_inputs
