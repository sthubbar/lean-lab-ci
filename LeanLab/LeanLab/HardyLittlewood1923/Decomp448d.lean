import LeanLab.HardyLittlewood1923.Decomp415c
import LeanLab.HardyLittlewood1923.Decomp354h
import LeanLab.HardyLittlewood1923.Inducing448

/-!
AI wrote this Lean code for CODEX task448.
P0004 pages 19 and 20 equations 2.825 to 2.834.
Goldbach is OPEN.
-/
namespace LeanLab.HardyLittlewood1923.Decomp448d
open Real
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp415c

/-- LEAF. P0004 pages 19 and 20 equations 2.825, 2.826 and 2.832.
For a primitive character the strip zero sum gives the angular envelope.
The principal residue is already subtracted in characterError.
There are no imprimitive Euler factors or additive Gauss averages here. -/
theorem primitive_character_bound {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ χ : DirichletCharacter ℂ q,
      χ.IsPrimitive → ∀ θ : ℝ, |θ| ≤ 2 * π →
        ‖characterError n q χ θ‖ ≤
          C * ((q : ℝ) + Real.sqrt n + characterEnvelope Θ n θ) *
            Real.log ((q : ℝ) + 1) ^ A := by
  sorry

/-- LEAF. P0004 page 20 equation 2.833 and the imprimitive product on page 10.
The inducing primitive series differs only at prime powers dividing the level.
Their smoothed mass costs square root n times a power of log of q plus one.
This correction uses no zero free hypothesis and has no angular zero envelope. -/
theorem inducing_character_correction :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, ∀ θ : ℝ,
        ‖characterError n q χ θ -
          characterError n χ.conductor χ.primitiveCharacter θ‖ ≤
            C * Real.sqrt n * Real.log ((q : ℝ) + 1) ^ A := by
  exact Inducing448.inducing_character_correction

/-- P0004 page 21 after equation 2.834.
A common logarithmic power absorbs two levels and their two exponents. -/
theorem log_level_power_le {d q : ℕ} (hd : 1 ≤ d) (hdq : d ≤ q) (A B : ℕ) :
    Real.log ((d : ℝ) + 1) ^ A ≤
      (Real.log 2)⁻¹ ^ (A + B) * Real.log ((q : ℝ) + 1) ^ (A + B) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdlog : 0 ≤ Real.log ((d : ℝ) + 1) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d + 1))
  have hqlog : Real.log 2 ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ q + 1))
  have hlog : Real.log ((d : ℝ) + 1) ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (Nat.add_le_add_right hdq 1))
  have hsmall : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hs : 1 ≤ (Real.log 2)⁻¹ := (one_le_inv₀ h2).mpr hsmall
  have hp : 1 ≤ (Real.log 2)⁻¹ * Real.log ((q : ℝ) + 1) := by
    rw [← div_eq_inv_mul]
    exact (one_le_div h2).mpr hqlog
  calc
    _ ≤ Real.log ((q : ℝ) + 1) ^ A := pow_le_pow_left₀ hdlog hlog A
    _ ≤ ((Real.log 2)⁻¹ * Real.log ((q : ℝ) + 1)) ^ A := by
      exact pow_le_pow_left₀ (h2.le.trans hqlog)
        (le_mul_of_one_le_left (h2.le.trans hqlog) hs) A
    _ ≤ ((Real.log 2)⁻¹ * Real.log ((q : ℝ) + 1)) ^ (A + B) :=
      pow_le_pow_right₀ hp (by omega)
    _ = _ := by rw [mul_pow]

/-- P0004 pages 19 to 21 equations 2.825 to 2.834.
The exact sealed one character target follows from its primitive case and inducing correction.
CONDITIONAL only on primitive_character_bound. The inducing correction is proved. -/
theorem weighted_character_bound {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ∀ χ : DirichletCharacter ℂ q,
          ‖characterError n q χ θ‖ ≤
            C * ((q : ℝ) + Real.sqrt n + characterEnvelope Θ n θ) *
              Real.log ((q : ℝ) + 1) ^ A := by
  obtain ⟨A, C, hC, hc⟩ := primitive_character_bound hΘ0 hΘ1 hZ
  obtain ⟨B, D, hD, hd⟩ := inducing_character_correction
  obtain ⟨W, _, hw⟩ := Decomp354h.farey_upper_width
  refine ⟨A + B, (C + D) * (Real.log 2)⁻¹ ^ (A + B), by positivity,
    fun n hn q hq hqN p hp hpq θ hθ χ => ?_⟩
  haveI : NeZero q := ⟨by omega⟩
  have hcond : 1 ≤ χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hcondq : χ.conductor ≤ q := Nat.le_of_dvd (by omega) χ.conductor_dvd_level
  have ht := (hw n hn q hq hqN p hp hpq θ hθ).1
  have hprim := hc n hn χ.conductor hcond (hcondq.trans hqN)
    χ.primitiveCharacter χ.primitiveCharacter_isPrimitive θ ht
  have hdiff := hd n hn q hq χ θ
  have hE := characterEnvelope_nonneg Θ (by omega : 0 < n) θ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : 0 ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) q])
  have hlogcond : 0 ≤ Real.log ((χ.conductor : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) χ.conductor])
  have hA := log_level_power_le hcond hcondq A B
  have hB : Real.log ((q : ℝ) + 1) ^ B ≤
      (Real.log 2)⁻¹ ^ (A + B) * Real.log ((q : ℝ) + 1) ^ (A + B) := by
    simpa only [Nat.add_comm] using log_level_power_le hq (le_refl q) B A
  have hdc : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hcondq
  have htri : ‖characterError n q χ θ‖ ≤
      ‖characterError n q χ θ - characterError n χ.conductor χ.primitiveCharacter θ‖ +
        ‖characterError n χ.conductor χ.primitiveCharacter θ‖ := by
    simpa only [sub_add_cancel] using
      norm_add_le (characterError n q χ θ - characterError n χ.conductor χ.primitiveCharacter θ)
        (characterError n χ.conductor χ.primitiveCharacter θ)
  calc
    _ ≤ D * Real.sqrt n * Real.log ((q : ℝ) + 1) ^ B +
        C * ((χ.conductor : ℝ) + Real.sqrt n + characterEnvelope Θ n θ) *
          Real.log ((χ.conductor : ℝ) + 1) ^ A := htri.trans (add_le_add hdiff hprim)
    _ ≤ D * Real.sqrt n *
          ((Real.log 2)⁻¹ ^ (A + B) * Real.log ((q : ℝ) + 1) ^ (A + B)) +
        C * ((q : ℝ) + Real.sqrt n + characterEnvelope Θ n θ) *
          ((Real.log 2)⁻¹ ^ (A + B) * Real.log ((q : ℝ) + 1) ^ (A + B)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hB (by positivity)
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_left (by linarith :
            (χ.conductor : ℝ) + Real.sqrt n + characterEnvelope Θ n θ ≤
              (q : ℝ) + Real.sqrt n + characterEnvelope Θ n θ) hC)
          hA (by positivity) (by positivity)
    _ ≤ _ := by
      have hnonneg : 0 ≤ D * ((q : ℝ) + characterEnvelope Θ n θ) *
          ((Real.log 2)⁻¹ ^ (A + B) * Real.log ((q : ℝ) + 1) ^ (A + B)) := by positivity
      nlinarith only [hnonneg]

#print axioms log_level_power_le
#print axioms primitive_character_bound
#print axioms inducing_character_correction
#print axioms weighted_character_bound
end LeanLab.HardyLittlewood1923.Decomp448d
