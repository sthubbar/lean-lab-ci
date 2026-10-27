/-
P0028, arXiv 1610.02017, section 4.3, equation 4.1 on page 10.
The Fourier identity for double averaging over a finite set of integer shifts.
No lower bound on the Bohr set size is asserted here.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSIntegerFourier

namespace LeanLab.Ternary.MMS
open Finset
open scoped ComplexConjugate

/-- The exponential sum over the averaging set. -/
noncomputable def bohrSum (B : Finset ℤ) (γ : ℝ) : ℂ :=
  ∑ b ∈ B, e ((b : ℝ) * γ)

/-- The normalized exponential sum over the averaging set. -/
noncomputable def bohrMean (B : Finset ℤ) (γ : ℝ) : ℂ := bohrSum B γ / B.card

/-- The double average of translations, retaining the whole integer support. -/
noncomputable def intSmooth (B : Finset ℤ) (f : ℤ →₀ ℝ) : ℤ →₀ ℝ :=
  (1 / (B.card : ℝ) ^ 2) • ∑ b₁ ∈ B, ∑ b₂ ∈ B, intShift (b₂ - b₁) f

/-- The additive character has absolute value one. -/
theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  simp [e, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- Conjugation negates the phase. -/
theorem conj_e (x : ℝ) : conj (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Complex.ofReal_neg]
  ring

/-- Every nonempty averaging set has a normalized exponential sum of norm at most one. -/
theorem bohrMean_norm_le_one (B : Finset ℤ) (hB : B.Nonempty) (γ : ℝ) :
    ‖bohrMean B γ‖ ≤ 1 := by
  have hc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hs : ‖bohrSum B γ‖ ≤ B.card := by
    unfold bohrSum
    exact (norm_sum_le _ _).trans (by simp [norm_e])
  have hden : ‖(B.card : ℂ)‖ = (B.card : ℝ) := by simp
  rw [bohrMean, norm_div, hden]
  exact (div_le_one hc).mpr hs

/-- Pointwise form of translation on the integers. -/
theorem intShift_apply (t : ℤ) (f : ℤ →₀ ℝ) (n : ℤ) :
    intShift t f n = f (n - t) := by
  have hi : Function.Injective (fun a : ℤ => a + t) := by
    intro a b hab
    change a + t = b + t at hab
    omega
  simpa only [intShift, sub_add_cancel] using
    Finsupp.mapDomain_apply_of_injective hi f (n - t)

/-- The finitely supported smoothing is exactly the paper's double average. -/
theorem intSmooth_apply (B : Finset ℤ) (f : ℤ →₀ ℝ) (n : ℤ) :
    intSmooth B f n = (1 / (B.card : ℝ) ^ 2) *
      ∑ b₁ ∈ B, ∑ b₂ ∈ B, f (n + b₁ - b₂) := by
  simp only [intSmooth, Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul, intShift_apply]
  congr 1
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  congr 1
  ring

/-- Fourier multiplier of the full integer smoothing. -/
theorem intHat_smooth (B : Finset ℤ) (f : ℤ →₀ ℝ) (γ : ℝ) :
    intHat (intSmooth B f) γ = intHat f γ * ((‖bohrMean B γ‖ ^ 2 : ℝ) : ℂ) := by
  rw [intSmooth, intHat_smul]
  simp_rw [intHat_sum, intHat_shift]
  have hp (a b : ℤ) : e (-((b - a : ℤ) : ℝ) * γ) =
      e ((a : ℝ) * γ) * conj (e ((b : ℝ) * γ)) := by
    rw [conj_e, ← e_add]
    congr 1
    push_cast
    ring
  simp_rw [hp]
  have hs : (∑ a ∈ B, ∑ b ∈ B,
      intHat f γ * (e ((a : ℝ) * γ) * conj (e ((b : ℝ) * γ)))) =
      intHat f γ * (bohrSum B γ * conj (bohrSum B γ)) := by
    unfold bohrSum
    rw [map_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
  rw [hs, Complex.mul_conj']
  have hden : ‖(B.card : ℂ)‖ = (B.card : ℝ) := by simp
  unfold bohrMean
  rw [norm_div, hden, div_pow]
  push_cast
  ring

/-- Equation 4.1 with full integer transforms and no truncation. -/
theorem intHat_uniform_part (B : Finset ℤ) (f : ℤ →₀ ℝ) (γ : ℝ) :
    intHat (f - intSmooth B f) γ =
      intHat f γ * (1 - ((‖bohrMean B γ‖ ^ 2 : ℝ) : ℂ)) := by
  have hsub : intHat (f - intSmooth B f) γ = intHat f γ - intHat (intSmooth B f) γ := by
    simp [intHat]
  rw [hsub, intHat_smooth]
  ring

end LeanLab.Ternary.MMS
