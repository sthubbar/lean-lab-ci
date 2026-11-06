import LeanLab.HardyLittlewood1923.Decomp276c
import LeanLab.HardyLittlewood1923.WeightedCharacterExpansion

/-!
AI wrote this Lean code for CODEX task415.
P0004 pages 19 to 21 equations 2.811 to 2.834.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp415c

open Real Finset
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp276b
open LeanLab.HardyLittlewood1923.Decomp276c

/-- The character weighted series after subtracting its principal pole.
P0004 page 19 equations 2.811 and 2.812, before the Gauss average. -/
noncomputable def characterError (n q : ℕ) (χ : DirichletCharacter ℂ q) (θ : ℝ) : ℂ := by
  classical
  exact Task52.weightedSum χ (localY n θ) - if χ = 1 then (localY n θ)⁻¹ else 0

/-- The zero sum angular envelope before the square root modulus factor.
P0004 pages 19 and 20 equations 2.823 and 2.826. -/
noncomputable def characterEnvelope (Θ : ℝ) (n : ℕ) (θ : ℝ) : ℝ :=
  ‖localY n θ‖ ^ (-Θ) * (angularGap n θ) ^ (-Θ - 1 / 2) *
    Real.log (1 / angularGap n θ + 2)

/-- LEAF. P0004 page 19 Lemma 8 equations 2.811 to 2.813 and page 21 averaging step.
Prime power and nonunit corrections leave the Gauss weighted character errors.
The Gauss coefficient norm is at most square root q over phi q.
This reduction has no zero free premise and no bound on a character error. -/
theorem prime_character_reduction :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤
          (Real.sqrt q / (q.totient : ℝ)) *
            (∑ χ : DirichletCharacter ℂ q, ‖characterError n q χ θ‖) +
          C * Real.sqrt q * ((q : ℝ) + Real.sqrt n) * Real.log ((q : ℝ) + 1) ^ A := by
  sorry

/-- LEAF. P0004 pages 19 to 21 equations 2.825 to 2.834.
The high zeros use the damped Gamma sum and the unit height zero count.
The low strip zeros and the imprimitive boundary zeros are estimated separately.
This is one character estimate with no additive prime phase or Gauss averaging. -/
theorem weighted_character_bound {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ∀ χ : DirichletCharacter ℂ q,
          ‖characterError n q χ θ‖ ≤
            C * ((q : ℝ) + Real.sqrt n + characterEnvelope Θ n θ) *
              Real.log ((q : ℝ) + 1) ^ A := by
  sorry

/-- P0004 page 23 equation 3.121, the scalar angular envelope is nonnegative. -/
theorem characterEnvelope_nonneg (Θ : ℝ) {n : ℕ} (hn : 0 < n) (θ : ℝ) :
    0 ≤ characterEnvelope Θ n θ := by
  have hg := angularGap_pos hn θ
  have hl : 0 ≤ Real.log (1 / angularGap n θ + 2) :=
    Real.log_nonneg (by
      have : 0 < 1 / angularGap n θ := by positivity
      linarith)
  unfold characterEnvelope
  positivity

/-- P0004 page 21 after equation 2.834.
Averaging uniformly bounded character errors cancels the totient denominator. -/
theorem average_character_bound {n q : ℕ} [NeZero q] (hq : 1 ≤ q) (θ : ℝ) {D : ℝ}
    (hD : ∀ χ : DirichletCharacter ℂ q, ‖characterError n q χ θ‖ ≤ D) :
    (Real.sqrt q / (q.totient : ℝ)) *
      (∑ χ : DirichletCharacter ℂ q, ‖characterError n q χ θ‖) ≤ Real.sqrt q * D := by
  haveI : NeZero q := ⟨by omega⟩
  have hphi : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < q)).ne'
  have hcard : (univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  calc
    _ ≤ (Real.sqrt q / (q.totient : ℝ)) *
          ∑ _χ : DirichletCharacter ℂ q, D := by
      gcongr
      exact hD _
    _ = Real.sqrt q * D := by simp only [sum_const, nsmul_eq_mul, hcard]; field_simp

/-- P0004 page 19 equation 2.823, specialized on the paper circle.
The exact sealed Lemma 9 target follows from the correction and character leaves.
CONDITIONAL on prime_character_reduction and weighted_character_bound. -/
theorem lemma9_on_circle {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤
          C * (Real.sqrt q * ((q : ℝ) + Real.sqrt n) + angularTerm Θ n q θ) *
            Real.log ((q : ℝ) + 1) ^ A := by
  obtain ⟨A, C, hC, hc⟩ := prime_character_reduction
  obtain ⟨B, D, hD, hd⟩ := weighted_character_bound hΘ0 hΘ1 hZ
  refine ⟨A + B, (C + D) * (Real.log 2)⁻¹ ^ (A + B), by positivity,
    4, fun n hn q hq hqN p hp hpq θ hθ => ?_⟩
  haveI : NeZero q := ⟨by omega⟩
  have hnpos : 0 < n := by omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ q + 1))
  have hlog0 : 0 ≤ Real.log ((q : ℝ) + 1) := hlog2.le.trans hlog
  have hlog2_le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hscale : 1 ≤ (Real.log 2)⁻¹ := (one_le_inv₀ hlog2).mpr hlog2_le
  have hprod : 1 ≤ (Real.log 2)⁻¹ * Real.log ((q : ℝ) + 1) := by
    rw [← div_eq_inv_mul]
    exact (one_le_div hlog2).mpr hlog
  have hA : Real.log ((q : ℝ) + 1) ^ A ≤
      (Real.log 2)⁻¹ ^ (A + B) * Real.log ((q : ℝ) + 1) ^ (A + B) := by
    calc
      _ ≤ ((Real.log 2)⁻¹ * Real.log ((q : ℝ) + 1)) ^ A := by
        gcongr
        exact le_mul_of_one_le_left hlog0 hscale
      _ ≤ ((Real.log 2)⁻¹ * Real.log ((q : ℝ) + 1)) ^ (A + B) :=
        pow_le_pow_right₀ hprod (by omega)
      _ = _ := by rw [mul_pow]
  have hB : Real.log ((q : ℝ) + 1) ^ B ≤
      (Real.log 2)⁻¹ ^ (A + B) * Real.log ((q : ℝ) + 1) ^ (A + B) := by
    calc
      _ ≤ ((Real.log 2)⁻¹ * Real.log ((q : ℝ) + 1)) ^ B := by
        gcongr
        exact le_mul_of_one_le_left hlog0 hscale
      _ ≤ ((Real.log 2)⁻¹ * Real.log ((q : ℝ) + 1)) ^ (A + B) :=
        pow_le_pow_right₀ hprod (by omega)
      _ = _ := by rw [mul_pow]
  have he0 := characterEnvelope_nonneg Θ hnpos θ
  have hav := average_character_bound hq θ (hd n hn q hq hqN p hp hpq θ hθ)
  have hr := hc n hn q hq hqN p hp hpq θ hθ
  have heq : angularTerm Θ n q θ = Real.sqrt q * characterEnvelope Θ n θ := by
    unfold angularTerm characterEnvelope
    ring
  rw [heq]
  calc
    _ ≤ Real.sqrt q * (D * ((q : ℝ) + Real.sqrt n + characterEnvelope Θ n θ) *
          Real.log ((q : ℝ) + 1) ^ B) +
        C * Real.sqrt q * ((q : ℝ) + Real.sqrt n) * Real.log ((q : ℝ) + 1) ^ A :=
      hr.trans (add_le_add hav le_rfl)
    _ ≤ Real.sqrt q * (D * ((q : ℝ) + Real.sqrt n + characterEnvelope Θ n θ) *
          ((Real.log 2)⁻¹ ^ (A + B) * Real.log ((q : ℝ) + 1) ^ (A + B))) +
        C * Real.sqrt q * ((q : ℝ) + Real.sqrt n) *
          ((Real.log 2)⁻¹ ^ (A + B) * Real.log ((q : ℝ) + 1) ^ (A + B)) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left hB (by positivity)
      · exact mul_le_mul_of_nonneg_left hA (by positivity)
    _ ≤ _ := by
      have hnonneg : 0 ≤ C * Real.sqrt q * characterEnvelope Θ n θ *
          ((Real.log 2)⁻¹ ^ (A + B) * Real.log ((q : ℝ) + 1) ^ (A + B)) := by positivity
      nlinarith only [hnonneg]

#print axioms prime_character_reduction
#print axioms weighted_character_bound
#print axioms characterEnvelope_nonneg
#print axioms average_character_bound
#print axioms lemma9_on_circle

end LeanLab.HardyLittlewood1923.Decomp415c
