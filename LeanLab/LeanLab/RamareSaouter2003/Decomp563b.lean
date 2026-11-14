import Mathlib

/-!
Backlund pp. 368 and 369 displays 74 through 76.
The zeta functional equation is supplied by Mathlib.
The remaining leaf concerns only the Gamma norm from the shifted Stirling remainder.
AI wrote the Lean code. Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp563b
open Real Complex

/-- Backlund p. 369 display 75, the exact functional equation multiplier. -/
noncomputable def functionalMultiplier (s : ℂ) : ℂ :=
  2 * (2 * π) ^ (-s) * Complex.Gamma s * Complex.cos (π * s / 2)

/-- Backlund p. 369 display 75, the reflected zeta norm identity. -/
theorem reflection_norm_identity (a t : ℝ) (ht : 0 < t) :
    ‖riemannZeta (((1 - a : ℝ) : ℂ) + t * I)‖ =
      ‖functionalMultiplier ((a : ℂ) - t * I)‖ *
        ‖riemannZeta ((a : ℂ) + t * I)‖ := by
  let s : ℂ := (a : ℂ) - t * I
  have hs : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have hi := congrArg Complex.im h
    simp [s] at hi
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp [s] at hi
    linarith
  have he : 1 - s = (((1 - a : ℝ) : ℂ) + t * I) := by dsimp [s]; push_cast; ring
  have hc : s = starRingEnd ℂ ((a : ℂ) + t * I) := by simp [s, map_add, map_mul, sub_eq_add_neg]
  have h := riemannZeta_one_sub hs hs1
  rw [he] at h
  rw [h, norm_mul]
  change ‖functionalMultiplier s‖ * ‖riemannZeta s‖ = _
  have hz : ‖riemannZeta s‖ = ‖riemannZeta ((a : ℂ) + t * I)‖ := by
    rw [hc, riemannZeta_conj, Complex.norm_conj]
  rw [hz]

/-- Backlund p. 369, the elementary three-factor budget in display 76. -/
theorem multiplier_error_budget (t : ℝ) (ht : 50 ≤ t) :
    (1 + 1 / (4 * t ^ 2)) * (1 + 1 / (8 * t ^ 2)) *
      (1 + 1 / (16 * t ^ 2)) ≤ 1 + 1 / (2 * t ^ 2) := by
  let x : ℝ := 1 / t ^ 2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxu : x ≤ 1 / 2500 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : 0 < t ^ 2)).mpr
    nlinarith
  have he4 : 1 / (4 * t ^ 2) = x / 4 := by dsimp [x]; ring
  have he8 : 1 / (8 * t ^ 2) = x / 8 := by dsimp [x]; ring
  have he16 : 1 / (16 * t ^ 2) = x / 16 := by dsimp [x]; ring
  have he2 : 1 / (2 * t ^ 2) = x / 2 := by dsimp [x]; ring
  rw [he4, he8, he16, he2]
  have hxx : x ^ 2 ≤ x / 2500 := by nlinarith
  have hxxx : x ^ 3 ≤ x ^ 2 / 2500 := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hxu)]
  nlinarith [pow_nonneg hx 3]

/-- Backlund p. 369, the exponentially small cosine error has a rational majorant. -/
theorem exp_cosine_error (t : ℝ) (ht : 50 ≤ t) :
    Real.exp (-π * t) ≤ 1 / (16 * t ^ 2) := by
  have htpos : 0 < t := by linarith
  have hp : 3 * t ≤ π * t := mul_le_mul_of_nonneg_right Real.pi_gt_three.le htpos.le
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 3 * t) hp 3
  have h3 := Real.pow_div_factorial_le_exp (π * t) (by positivity : (0 : ℝ) ≤ π * t) 3
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at h3
  have ht3 : 50 * t ^ 2 ≤ t ^ 3 := by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht)]
  have he : 16 * t ^ 2 ≤ Real.exp (π * t) := by nlinarith
  rw [show -π * t = -(π * t) by ring, Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 16 * t ^ 2) he

/-- Backlund p. 369 before display 75, the complex cosine factor bound. -/
theorem cosine_factor_bound (a t : ℝ) (ht : 50 ≤ t) :
    ‖Complex.cos (π * ((a : ℂ) - t * I) / 2)‖ ≤
      Real.exp (π * t / 2) / 2 * (1 + 1 / (16 * t ^ 2)) := by
  let z : ℂ := π * ((a : ℂ) - t * I) / 2
  have hpos : (z * I).re = π * t / 2 := by simp [z, Complex.mul_re, Complex.mul_im]; ring
  have hneg : (-z * I).re = -(π * t / 2) := by simp [z, Complex.mul_re, Complex.mul_im]; ring
  have h := norm_add_le (Complex.exp (z * I)) (Complex.exp (-z * I))
  rw [Complex.norm_exp, Complex.norm_exp, hpos, hneg] at h
  have he : Real.exp (-(π * t / 2)) = Real.exp (π * t / 2) * Real.exp (-π * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  have hsmall := exp_cosine_error t ht
  change ‖Complex.cos z‖ ≤ _
  rw [Complex.cos, norm_div]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ (Real.exp (π * t / 2) + Real.exp (π * t / 2) * Real.exp (-π * t)) / 2 :=
      div_le_div_of_nonneg_right h (by norm_num)
    _ ≤ (Real.exp (π * t / 2) + Real.exp (π * t / 2) * (1 / (16 * t ^ 2))) / 2 := by gcongr
    _ = _ := by ring

/-- LEAF. Backlund pp. 368 and 369 display 74 and the Gamma recurrence.
The shifted real Stirling remainder gives the factor one plus one over four t squared.
The recurrence contributes the factor one plus one over eight t squared.
No cosine, zeta value or functional equation occurs in this leaf. -/
theorem gamma74_upper (a t : ℝ) (ha : a ∈ Set.Icc (1 : ℝ) (3 / 2)) (ht : 50 ≤ t) :
    ‖Complex.Gamma ((a : ℂ) - t * I)‖ ≤
      Real.sqrt (2 * π) * t ^ (a - 1 / 2) * Real.exp (-π * t / 2) *
        (1 + 1 / (4 * t ^ 2)) * (1 + 1 / (8 * t ^ 2)) := by
  sorry

/-- Backlund pp. 368 and 369 displays 74 through 76.
CONDITIONAL ON gamma74_upper.
Bound only the explicit Gamma and cosine multiplier.
The real Stirling remainder at s minus one is display 74.
The recurrence, cosine formula and scalar error product give this bound.
No zeta growth estimate occurs in this leaf. -/
theorem multiplier76_bound (a t : ℝ) (ha : a ∈ Set.Icc (1 : ℝ) (3 / 2)) (ht : 50 ≤ t) :
    ‖functionalMultiplier ((a : ℂ) - t * I)‖ ≤
      (t / (2 * π)) ^ (a - 1 / 2) * (1 + 1 / (2 * t ^ 2)) := by
  have htpos : 0 < t := by linarith
  have hb : 0 < 2 * π := by positivity
  have hpow : ‖(2 * π : ℂ) ^ (-((a : ℂ) - t * I))‖ = (2 * π : ℝ) ^ (-a) := by
    have he : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_cpow_eq_rpow_re_of_pos hb]
    simp
  have hscale : (2 * π : ℝ) ^ (-a) * Real.sqrt (2 * π) * t ^ (a - 1 / 2) =
      (t / (2 * π)) ^ (a - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hb]
    rw [show -a + 1 / 2 = -(a - 1 / 2) by ring, Real.rpow_neg hb.le,
      Real.div_rpow htpos.le hb.le]
    ring
  have he : Real.exp (-π * t / 2) * Real.exp (π * t / 2) = 1 := by
    rw [← Real.exp_add, show -π * t / 2 + π * t / 2 = 0 by ring, Real.exp_zero]
  have hg := gamma74_upper a t ha ht
  have hc := cosine_factor_bound a t ht
  unfold functionalMultiplier
  simp only [norm_mul, Complex.norm_ofNat]
  rw [hpow]
  calc
    _ ≤ 2 * (2 * π : ℝ) ^ (-a) *
        (Real.sqrt (2 * π) * t ^ (a - 1 / 2) * Real.exp (-π * t / 2) *
          (1 + 1 / (4 * t ^ 2)) * (1 + 1 / (8 * t ^ 2))) *
        (Real.exp (π * t / 2) / 2 * (1 + 1 / (16 * t ^ 2))) := by gcongr
    _ = ((2 * π : ℝ) ^ (-a) * Real.sqrt (2 * π) * t ^ (a - 1 / 2)) *
        (Real.exp (-π * t / 2) * Real.exp (π * t / 2)) *
        ((1 + 1 / (4 * t ^ 2)) * (1 + 1 / (8 * t ^ 2)) * (1 + 1 / (16 * t ^ 2))) := by ring
    _ = (t / (2 * π)) ^ (a - 1 / 2) *
        ((1 + 1 / (4 * t ^ 2)) * (1 + 1 / (8 * t ^ 2)) * (1 + 1 / (16 * t ^ 2))) := by rw [hscale, he, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left (multiplier_error_budget t ht) (by positivity)

/-- Backlund p. 369 display 76, the exact original reflected norm comparison.
CONDITIONAL ON multiplier76_bound. -/
theorem reflection76 (σ t : ℝ) (hσ : σ ∈ Set.Icc (-1 / 2 : ℝ) 0) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      (t / (2 * π)) ^ (1 / 2 - σ) * (1 + 1 / (2 * t ^ 2)) *
        ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ := by
  have ha : 1 - σ ∈ Set.Icc (1 : ℝ) (3 / 2) := by
    constructor <;> linarith [hσ.1, hσ.2]
  have h := multiplier76_bound (1 - σ) t ha ht
  have he : 1 - σ - 1 / 2 = 1 / 2 - σ := by ring
  rw [he] at h
  have hi := reflection_norm_identity (1 - σ) t (by linarith)
  have hs : 1 - (1 - σ) = σ := by ring
  rw [hs] at hi
  rw [hi]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

end LeanLab.RamareSaouter2003.Decomp563b

#print axioms LeanLab.RamareSaouter2003.Decomp563b.functionalMultiplier
#print axioms LeanLab.RamareSaouter2003.Decomp563b.reflection_norm_identity
#print axioms LeanLab.RamareSaouter2003.Decomp563b.multiplier_error_budget
#print axioms LeanLab.RamareSaouter2003.Decomp563b.multiplier76_bound
#print axioms LeanLab.RamareSaouter2003.Decomp563b.reflection76

#print axioms LeanLab.RamareSaouter2003.Decomp563b.exp_cosine_error

#print axioms LeanLab.RamareSaouter2003.Decomp563b.cosine_factor_bound

#print axioms LeanLab.RamareSaouter2003.Decomp563b.gamma74_upper
