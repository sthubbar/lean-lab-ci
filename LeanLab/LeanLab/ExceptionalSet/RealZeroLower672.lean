/-
P0082 page 358 display 10, as a bound with an unspecified positive constant.
The existing lab Siegel theorem supplies a stronger ineffective zero gap.
Character lifting handles every positive modulus.
This does not assert an effective constant or existence of an exceptional zero.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelectedDecisions
import LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelectedDecisions
import LeanLab.PNTPort.DirichletZF.Siegel

namespace LeanLab.ExceptionalSet.Task672

open Real

/-- Derived from the lab Siegel theorem by lifting the modulus to eight times itself. -/
theorem realZeroGapHalf672 :
    ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
      χ ≠ 1 → χ ^ 2 = 1 → ∀ β : ℝ, β ≤ 1 → χ.LFunction β = 0 →
        c * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 - β := by
  obtain ⟨c, hc, hgap⟩ := LeanLab.PNTPort.DirichletZF.siegel_zero (1 / 2) (by norm_num)
  refine ⟨c * (8 : ℝ) ^ (-(1 / 2 : ℝ)), by positivity, ?_⟩
  intro r hr χ hχ hreal β hβ hz
  letI : NeZero r := hr
  have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  haveI : NeZero (8 * r) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne r)⟩
  let hd : r ∣ 8 * r := Nat.dvd_mul_left r 8
  have hzlift : (DirichletCharacter.changeLevel hd χ).LFunction β = 0 := by
    rw [DirichletCharacter.LFunction_changeLevel hd χ (Or.inl hχ), hz, zero_mul]
  have hb := hgap (8 * r) (by omega) (DirichletCharacter.changeLevel hd χ)
    (LeanLab.PNTPort.DirichletZF.lift_ne_one hd hχ)
    (LeanLab.PNTPort.DirichletZF.lift_sq hd hreal) β hβ hzlift
  have hfactor : ((8 * r : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
      (8 : ℝ) ^ (-(1 / 2 : ℝ)) * (r : ℝ) ^ (-(1 / 2 : ℝ)) := by
    push_cast
    exact Real.mul_rpow (by norm_num) (Nat.cast_nonneg r)
  rw [hfactor] at hb
  nlinarith

/-- The existing display 10 input needs existence, not effectivity, of its constant. -/
theorem landauRealZeroHyp_proved672 :
    UpJ200.DQLeafCoprimeSelected.LandauRealZeroHyp := by
  obtain ⟨c, hc, hgap⟩ := realZeroGapHalf672
  refine ⟨c * Real.log 2 ^ 2, by positivity, ?_⟩
  intro r hr χ β hp hreal hχ hβ hz
  letI : NeZero r := hr
  have hr2 : 2 ≤ r := by
    have hr0 : r ≠ 0 := NeZero.ne r
    have hr1 : r ≠ 1 := by
      intro heq
      subst r
      exact hχ (DirichletCharacter.level_one χ)
    omega
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlog : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < r))
  have hlower : Real.log 2 ^ 2 ≤ Real.log (r : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (Real.log_nonneg (by norm_num))
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hr2)
  have hb := hgap r hr χ hχ hreal β hβ.le hz
  have hcancel : (r : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt r = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hrpos]
    norm_num
  have hscaled := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg (r : ℝ))
  rw [mul_assoc, hcancel, mul_one] at hscaled
  apply (div_le_iff₀ (by positivity : 0 < Real.sqrt (r : ℝ) * Real.log (r : ℝ) ^ 2)).mpr
  calc c * Real.log 2 ^ 2 ≤ c * Real.log (r : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hlower hc.le
    _ ≤ (1 - β) * (Real.sqrt (r : ℝ) * Real.log (r : ℝ) ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hscaled (sq_nonneg (Real.log (r : ℝ)))]

/-- The positive real zero variant follows from the proved display 10 input. -/
theorem realZeroDistanceHyp_proved672 :
    UpJ200.DQLeafNearZeroSelected.RealZeroDistanceHyp := by
  obtain ⟨c, hc, hgap⟩ := landauRealZeroHyp_proved672
  refine ⟨c, hc, ?_⟩
  intro r hr χ hp hreal hχ β hβ0 hβ hz
  letI : NeZero r := hr
  have hr2 : 2 ≤ r := by
    have hr0 : r ≠ 0 := NeZero.ne r
    have hr1 : r ≠ 1 := by
      intro heq
      subst r
      exact hχ (DirichletCharacter.level_one χ)
    omega
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlog : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < r))
  have hb := hgap r hr χ β hp hreal hχ hβ hz
  have hd : 0 < Real.sqrt (r : ℝ) * Real.log (r : ℝ) ^ 2 := by positivity
  have h := (div_le_iff₀ hd).mp hb
  simpa [Real.sqrt_eq_rpow, mul_assoc] using h

end LeanLab.ExceptionalSet.Task672

#print axioms LeanLab.PNTPort.DirichletZF.siegel_zero
#print axioms LeanLab.ExceptionalSet.Task672.realZeroGapHalf672
#print axioms LeanLab.ExceptionalSet.Task672.landauRealZeroHyp_proved672
#print axioms LeanLab.ExceptionalSet.Task672.realZeroDistanceHyp_proved672
