/-
P0045, journal page 774, the real zero bound before Lemma 4.1.
The encoded bound asks for existence of a positive constant.
The lab Siegel theorem gives that existence without a claim of effectivity.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LPZ2007.Statements
import LeanLab.PNTPort.DirichletZF.Siegel

namespace LeanLab.LPZ2007.RealZeroProof

open Finset Real Complex
open LeanLab.LPZ2007 LeanLab.PNTPort.DirichletZF

noncomputable section

/-- A character with real values has square equal to the principal character. -/
theorem sq_of_real {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (hreal : ∀ a, (χ a).im = 0) : χ ^ 2 = 1 := by
  have hstar : star χ = χ := by
    ext a
    change star (χ a) = χ a
    apply Complex.ext <;> simp [hreal a]
  rw [MulChar.star_eq_inv] at hstar
  calc χ ^ 2 = χ⁻¹ * χ := by rw [hstar, pow_two]
    _ = 1 := inv_mul_cancel _

/-- A principal character has no real zero between zero and one. -/
theorem principal_ne_zero {r : ℕ} [NeZero r] {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ r) (β : ℂ) ≠ 0 := by
  have hne : (β : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at this
    linarith
  change DirichletCharacter.LFunctionTrivChar r (β : ℂ) ≠ 0
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hne]
  apply mul_ne_zero
  · apply prod_ne_zero_iff.2
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpr : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hlt : (p : ℝ) ^ (-β) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hpr (by linarith)
    intro hz
    have heq : (p : ℂ) ^ (-(β : ℂ)) = 1 := (sub_eq_zero.1 hz).symm
    have hn := norm_cpow_neg hpp.ne_zero (β : ℂ)
    rw [heq, norm_one, Complex.ofReal_re] at hn
    linarith
  · intro hz
    have hneg := (riemannZeta_real_neg hβ0 hβ1).2
    rw [hz, Complex.zero_re] at hneg
    exact (lt_irrefl (0 : ℝ)) hneg

/-- The existing real zero bound follows from Siegel with exponent one half. -/
theorem realZeroBound_proved : RealZeroBound := by
  obtain ⟨c, hc, H⟩ := siegel_zero (1 / 2) (by norm_num)
  let C := min (c * (8 : ℝ) ^ (-(1 / 2 : ℝ))) (1 / 2)
  have hC : 0 < C := lt_min (by positivity) (by norm_num)
  refine ⟨C, hC, fun r hr χ hreal δ hδ hz => ?_⟩
  have hr0 : 0 < r := by omega
  have hrne : r ≠ 0 := by omega
  haveI : NeZero r := ⟨hrne⟩
  have hrreal : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpow : (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hrreal (by norm_num)
  by_cases hfar : 1 / 2 ≤ δ
  · have hCle : C ≤ 1 / 2 := min_le_right _ _
    calc C * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ C * 1 :=
        mul_le_mul_of_nonneg_left hrpow hC.le
      _ ≤ δ := by linarith
  have hβ0 : 0 < 1 - δ := by linarith
  have hβ1 : 1 - δ < 1 := by linarith
  have hz' : DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ) = 0 := by
    simpa [Lfun, hrne, Complex.ofReal_sub] using hz
  have hχ : χ ≠ 1 := by
    rintro rfl
    exact principal_ne_zero hβ0 hβ1 hz'
  have hχ2 : χ ^ 2 = 1 := sq_of_real χ hreal
  let M := 8 * r
  haveI : NeZero M := ⟨Nat.mul_ne_zero (by decide) hrne⟩
  have hd : r ∣ M := Dvd.intro_left 8 rfl
  have hM : 8 ≤ M := by dsimp [M]; omega
  have hzlift : DirichletCharacter.LFunction (DirichletCharacter.changeLevel hd χ)
      ((1 - δ : ℝ) : ℂ) = 0 := by
    rw [L_lift hd hχ, hz', zero_mul]
  have hb := H M hM (DirichletCharacter.changeLevel hd χ) (lift_ne_one hd hχ)
    (lift_sq hd hχ2) (1 - δ) hβ1.le hzlift
  have hMr : (M : ℝ) = 8 * r := by simp [M]
  rw [hMr, Real.mul_rpow (by norm_num) (Nat.cast_nonneg r)] at hb
  have hcoeff : C ≤ c * (8 : ℝ) ^ (-(1 / 2 : ℝ)) := min_le_left _ _
  have hmul := mul_le_mul_of_nonneg_right hcoeff
    (Real.rpow_nonneg (Nat.cast_nonneg r) (-(1 / 2 : ℝ)))
  nlinarith

/-- A trivial zero gives a concrete instance of all zero hypotheses. -/
theorem real_zero_instance :
    (∀ a : ZMod 1, ((1 : DirichletCharacter ℂ 1) a).im = 0) ∧
      Lfun (1 : DirichletCharacter ℂ 1) (-2) = 0 := by
  constructor
  · intro a
    rw [MulChar.one_apply (isUnit_of_subsingleton a)]
    norm_num
  · change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) (-2) = 0
    rw [DirichletCharacter.LFunction_modOne_eq]
    simpa using riemannZeta_neg_two_mul_nat_add_one 0

end
end LeanLab.LPZ2007.RealZeroProof

#print axioms LeanLab.LPZ2007.RealZeroProof.sq_of_real

#print axioms LeanLab.LPZ2007.RealZeroProof.principal_ne_zero

#print axioms LeanLab.LPZ2007.RealZeroProof.realZeroBound_proved

#print axioms LeanLab.LPZ2007.RealZeroProof.real_zero_instance

namespace LeanLab.LPZ2007

/-- The former cited statement with its exact type, now proved. -/
theorem realZeroBound : RealZeroBound := RealZeroProof.realZeroBound_proved

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.realZeroBound
