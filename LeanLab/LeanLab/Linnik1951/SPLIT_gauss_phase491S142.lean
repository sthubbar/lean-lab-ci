/-
Split, by burst session S142, of the two HARD leaves of SPLIT_gauss_phase491, P0093 page 160
equation 5.5, along the primitive character of conductor c inducing a character mod q.
* the Gauss coefficient mod q is at most the primitive Gauss sum mod c in modulus, HARD;
* a primitive Gauss sum mod c has modulus the square root of c, proved here by Fourier
  inversion;
* the residue phase at n is at most the square root of c times the gcd of n and the cofactor
  q over c, HARD.
The original two leaves follow from these with sorry free glue below.
The gcd bound and the Gauss bound were checked in floating point for every character mod q,
every q up to 120 and every residue n mod q.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_mixed_pair_bound491
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Fourier.ZMod

namespace LeanLab.Linnik1951

open Finset

/-- LEAF: P0093 page 160, equation 5.5, reduction of the imprimitive Gauss sum to the primitive
one. Class: HARD. For a character mod a positive q induced by the primitive character of
conductor c, the Gauss sum mod q is the Moebius value of q over c times the primitive character
at q over c times the primitive Gauss sum, so the conjugate Gauss coefficient is at most the
primitive Gauss sum in modulus. -/
theorem conjugateGauss_le_primitive_gaussSum491S142 (q : ℕ) (hq : 1 ≤ q)
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] :
    ‖conjugateGauss491 q χ‖ ≤ ‖gaussSum χ.primitiveCharacter (ZMod.stdAddChar)‖ := by
  sorry

open ZMod DirichletCharacter in
/-- P0093 page 160, equation 5.5, the classical modulus of a primitive Gauss sum, proved here
by Fourier inversion on ZMod N: a primitive character mod a positive N has Gauss sum of modulus
the square root of N. -/
theorem norm_gaussSum_primitive491S142 (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N)
    (hψ : ψ.IsPrimitive) :
    ‖gaussSum ψ (ZMod.stdAddChar)‖ = Real.sqrt (N : ℝ) := by
  set τ := gaussSum ψ (ZMod.stdAddChar (N := N)) with hτ
  have hF : 𝓕 (fun k => ψ k) = fun k => ψ⁻¹ (-k) * τ := by
    funext k
    exact hψ.fourierTransform_eq_inv_mul_gaussSum k
  have h := congrFun (ZMod.dft_dft (N := N) (fun k => ψ k)) (-1)
  rw [hF] at h
  simp only [neg_neg, map_one, smul_eq_mul, mul_one, dft_apply] at h
  have hstar : star τ = ∑ x : ZMod N, ψ⁻¹ x * ZMod.stdAddChar (-x) := by
    rw [hτ, star_gaussSum_eq]
    simp [gaussSum]
  have hsum : (∑ j : ZMod N, ZMod.stdAddChar (-(j * -1)) * (ψ⁻¹ (-j) * τ))
      = star τ * τ := by
    rw [hstar, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun j => ?_)
    simp only [Equiv.neg_apply, mul_neg, mul_one, neg_neg]
    ring
  rw [hsum] at h
  have hn : (‖τ‖ : ℝ) ^ 2 = N := by
    have : (star τ * τ) = ((‖τ‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      rfl
    rw [this] at h
    exact_mod_cast h
  rw [← hn, Real.sqrt_sq (norm_nonneg _)]


/-- LEAF: P0093 page 160, equation 5.5, the residue phase through the primitive character.
Class: HARD. For a character mod a positive q of conductor c and every integer n, the residue
phase at n has modulus at most the square root of c times the gcd of n and the cofactor q over c,
the size of the Ramanujan factor of the cofactor. -/
theorem residuePhase_le_sqrt_conductor_mul_gcd491S142 (q : ℕ) (hq : 1 ≤ q) (n : ℤ)
    (χ : DirichletCharacter ℂ q) :
    ‖residuePhase555 q n χ‖ ≤
      Real.sqrt (χ.conductor : ℝ) * (Int.gcd n ((q / χ.conductor : ℕ) : ℤ) : ℝ) := by
  sorry

/-- The Gauss coefficient bound of SPLIT_gauss_phase491, from the two Gauss sum leaves. -/
theorem gauss_coefficient_le_sqrt_conductor491S142 (q : ℕ) (hq : 1 ≤ q)
    (χ : DirichletCharacter ℂ q) :
    ‖conjugateGauss491 q χ‖ ≤ Real.sqrt (χ.conductor : ℝ) := by
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  calc ‖conjugateGauss491 q χ‖
      ≤ ‖gaussSum χ.primitiveCharacter (ZMod.stdAddChar)‖ :=
        conjugateGauss_le_primitive_gaussSum491S142 q hq χ
    _ = Real.sqrt (χ.conductor : ℝ) :=
        norm_gaussSum_primitive491S142 χ.conductor χ.primitiveCharacter
          (DirichletCharacter.primitiveCharacter_isPrimitive χ)

/-- The residue phase bound of SPLIT_gauss_phase491, from the gcd leaf. -/
theorem residue_phase_mul_sqrt_conductor_le491S142 (q : ℕ) (hq : 1 ≤ q) (n : ℤ)
    (χ : DirichletCharacter ℂ q) :
    ‖residuePhase555 q n χ‖ * Real.sqrt (χ.conductor : ℝ) ≤ (q : ℝ) := by
  haveI : NeZero q := ⟨by omega⟩
  have hc0 : χ.conductor ≠ 0 := DirichletCharacter.conductor_ne_zero χ
  have hdvd : χ.conductor ∣ q := DirichletCharacter.conductor_dvd_level χ
  set c := χ.conductor with hc
  set r := q / c with hr
  have hcr : c * r = q := Nat.mul_div_cancel' hdvd
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h, mul_zero] at hcr; omega
    · exact h
  have hg : Int.gcd n (r : ℤ) ≤ r := by
    apply Nat.le_of_dvd hr0
    have := Int.gcd_dvd_right (a := n) (b := (r : ℤ))
    exact Int.natCast_dvd_natCast.mp (by simpa using this)
  have hsq : Real.sqrt (c : ℝ) * Real.sqrt (c : ℝ) = (c : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hs0 : 0 ≤ Real.sqrt (c : ℝ) := Real.sqrt_nonneg _
  have h1 := residuePhase_le_sqrt_conductor_mul_gcd491S142 q hq n χ
  calc ‖residuePhase555 q n χ‖ * Real.sqrt (c : ℝ)
      ≤ Real.sqrt (c : ℝ) * (Int.gcd n (r : ℤ) : ℝ) * Real.sqrt (c : ℝ) :=
        mul_le_mul_of_nonneg_right h1 hs0
    _ = (c : ℝ) * (Int.gcd n (r : ℤ) : ℝ) := by rw [mul_right_comm, hsq]
    _ ≤ (c : ℝ) * (r : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact_mod_cast hg
    _ = (q : ℝ) := by exact_mod_cast hcr

#print axioms norm_gaussSum_primitive491S142
#print axioms gauss_coefficient_le_sqrt_conductor491S142
#print axioms residue_phase_mul_sqrt_conductor_le491S142

end LeanLab.Linnik1951
