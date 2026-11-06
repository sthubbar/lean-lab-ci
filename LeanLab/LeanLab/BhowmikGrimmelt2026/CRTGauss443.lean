/-
Finite CRT phases used in the coefficient identity.
Source: Pintz Part I pages 19 and 20, displays 7.9 to 7.14.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.ReducedFrequency443

namespace LeanLab.BhowmikGrimmelt2026

/-- The standard additive phase splits using integer Bezout coefficients.
Source: the finite CRT phase cancellation behind Pintz page 20 display 7.13.
This is a derived finite identity and not an extra analytic assumption. -/
theorem crt_phase443 {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (A B : ℤ) (hAB : A * m + B * n = 1) (a : ZMod (m * n)) :
    ZMod.stdAddChar a =
      ZMod.stdAddChar ((B : ZMod m) * (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) a)) *
      ZMod.stdAddChar ((A : ZMod n) * (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) a)) := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hab : (A : ℂ) / n + (B : ℂ) / m = 1 / ((m : ℂ) * n) := by
    have h : (A : ℂ) * m + (B : ℂ) * n = 1 := by exact_mod_cast hAB
    field_simp
    linear_combination h
  have hc₁ : ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) a = (a.val : ZMod m) := by
    rw [← ZMod.natCast_zmod_val a]
    simp
  have hc₂ : ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) a = (a.val : ZMod n) := by
    rw [← ZMod.natCast_zmod_val a]
    simp
  rw [hc₁, hc₂,
    show (B : ZMod m) * (a.val : ZMod m) = ((B * (a.val : ℤ) : ℤ) : ZMod m) by push_cast; rfl,
    show (A : ZMod n) * (a.val : ZMod n) = ((A * (a.val : ℤ) : ℤ) : ZMod n) by push_cast; rfl]
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [show ((a.val : ℕ) : ZMod (m * n)) = ((a.val : ℤ) : ZMod (m * n)) by simp,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  push_cast
  calc
    _ = (2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ)) *
        ((A : ℂ) / n + (B : ℂ) / m) := by rw [hab]; ring
    _ = _ := by ring

/-- Unit residues split independently under the Chinese remainder equivalence.
Source: finite residue reindexing for Pintz page 20 display 7.13. -/
theorem unit_crt_sum443 {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (F : (ZMod m)ˣ → ℂ) (G : (ZMod n)ˣ → ℂ) :
    (∑ a : (ZMod (m * n))ˣ,
      F (ZMod.unitsMap (Nat.dvd_mul_right m n) a) *
      G (ZMod.unitsMap (Nat.dvd_mul_left n m) a)) =
        (∑ u : (ZMod m)ˣ, F u) * ∑ v : (ZMod n)ˣ, G v := by
  let e := (Units.mapEquiv (ZMod.chineseRemainder hcop).toMulEquiv).trans MulEquiv.prodUnits
  have he (a : (ZMod (m * n))ˣ) : e a =
      (ZMod.unitsMap (Nat.dvd_mul_right m n) a,
        ZMod.unitsMap (Nat.dvd_mul_left n m) a) := by
    apply Prod.ext <;> apply Units.ext
    · change (ZMod.cast (a : ZMod (m * n)) : ZMod m × ZMod n).1 =
        (ZMod.cast (a : ZMod (m * n)) : ZMod m)
      exact Prod.fst_zmod_cast _
    · change (ZMod.cast (a : ZMod (m * n)) : ZMod m × ZMod n).2 =
        (ZMod.cast (a : ZMod (m * n)) : ZMod n)
      exact Prod.snd_zmod_cast _
  calc
    _ = ∑ a : (ZMod (m * n))ˣ, F (e a).1 * G (e a).2 := by simp only [he]
    _ = ∑ uv : (ZMod m)ˣ × (ZMod n)ˣ, F uv.1 * G uv.2 :=
      Equiv.sum_comp e.toEquiv (fun uv : (ZMod m)ˣ × (ZMod n)ˣ => F uv.1 * G uv.2)
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_mul]; simp_rw [← Finset.mul_sum]

/-- A Gauss sum can be restricted to unit residues for any additive character.
Source: Montgomery Vaughan page 359, the restriction before display 5.3. -/
theorem gaussSum_units443 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ψ : AddChar (ZMod q) ℂ) :
    gaussSum χ ψ = ∑ a : (ZMod q)ˣ, χ a * ψ a := by
  classical
  unfold gaussSum
  symm
  apply Fintype.sum_of_injective (fun a : (ZMod q)ˣ => (a : ZMod q))
    Units.val_injective (fun a => χ a * ψ a) (fun a => χ a * ψ a) ?_ (fun _ => rfl)
  intro a ha
  rw [MulChar.map_nonunit χ (fun hu => ha ⟨hu.unit, hu.unit_spec⟩), zero_mul]

/-- The twisted sum of a CRT product factors with the exact Bezout frequency shifts.
Source: the finite CRT expansion behind Pintz page 20 display 7.13.
Both frequency factors remain explicit. -/
theorem cChi_crt_shift443 {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (χ : DirichletCharacter ℂ m) (ψ : DirichletCharacter ℂ n)
    (A B : ℤ) (hAB : A * m + B * n = 1) (N : ℤ) :
    cChi (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ *
      DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) ψ) N =
        cChi χ (B * N) * cChi ψ (A * N) := by
  rw [cChi_int_gauss436, cChi_int_gauss436, cChi_int_gauss436,
    gaussSum_units443, gaussSum_units443, gaussSum_units443]
  simp only [AddChar.mulShift_apply, Int.cast_mul]
  have ht (a : (ZMod (m * n))ˣ) :
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ *
          DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) ψ) a *
          ZMod.stdAddChar ((N : ZMod (m * n)) * (a : ZMod (m * n))) =
        (χ (ZMod.unitsMap (Nat.dvd_mul_right m n) a) *
          ZMod.stdAddChar (((B : ZMod m) * (N : ZMod m)) *
            (ZMod.unitsMap (Nat.dvd_mul_right m n) a : ZMod m))) *
        (ψ (ZMod.unitsMap (Nat.dvd_mul_left n m) a) *
          ZMod.stdAddChar (((A : ZMod n) * (N : ZMod n)) *
            (ZMod.unitsMap (Nat.dvd_mul_left n m) a : ZMod n))) := by
    rw [MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd,
      DirichletCharacter.changeLevel_eq_cast_of_dvd,
      crt_phase443 A B hAB ((N : ZMod (m * n)) * (a : ZMod (m * n)))]
    simp only [map_mul, map_intCast, ZMod.castHom_apply, ZMod.unitsMap_val, mul_assoc]
    ring
  simp_rw [ht]
  exact unit_crt_sum443 hcop
    (fun a => χ a * ZMod.stdAddChar (((B : ZMod m) * (N : ZMod m)) * (a : ZMod m)))
    (fun a => ψ a * ZMod.stdAddChar (((A : ZMod n) * (N : ZMod n)) * (a : ZMod n)))

/-- A unit frequency multiplier contributes the inverse character value.
Source: Montgomery Vaughan page 358 Lemma 5.3, applied at an arbitrary frequency. -/
theorem cChi_mul_unit443 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (M N : ℤ) (hM : IsUnit (M : ZMod q)) :
    cChi χ (M * N) = χ⁻¹ (M : ZMod q) * cChi χ N := by
  rw [cChi_int_gauss436, cChi_int_gauss436]
  have he : (ZMod.stdAddChar (N := q)).mulShift ((M * N : ℤ) : ZMod q) =
      ((ZMod.stdAddChar (N := q)).mulShift (N : ZMod q)).mulShift hM.unit := by
    ext a
    simp only [AddChar.mulShift_apply, IsUnit.unit_spec, Int.cast_mul]
    congr 1
    ring
  rw [he, gaussSum_mulShift_eq, IsUnit.unit_spec]

/-- The common unit frequency factors cancel across the three coefficient sums.
Source: the Gauss phase cancellation behind Pintz page 20 display 7.13. -/
theorem coefficient_phase_cancel443 {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (M N : ℤ) (hM : IsUnit (M : ZMod q)) :
    cChi χ₁⁻¹ M * cChi χ₂⁻¹ M * cChi (χ₁ * χ₂) (M * N) =
      tauConj χ₁ * tauConj χ₂ * cChi (χ₁ * χ₂) N := by
  have h₁ : χ₁ (M : ZMod q) * χ₁⁻¹ (M : ZMod q) = 1 := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply hM]
  have h₂ : χ₂ (M : ZMod q) * χ₂⁻¹ (M : ZMod q) = 1 := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply hM]
  have he₁ := cChi_mul_unit443 χ₁⁻¹ M 1 hM
  have he₂ := cChi_mul_unit443 χ₂⁻¹ M 1 hM
  simp only [mul_one, inv_inv] at he₁ he₂
  rw [he₁, he₂, cChi_mul_unit443 (χ₁ * χ₂) M N hM,
    tauConj_eq_cChi_inv436, tauConj_eq_cChi_inv436]
  simp only [mul_inv_rev, MulChar.mul_apply]
  calc
    _ = (χ₁ (M : ZMod q) * χ₁⁻¹ (M : ZMod q)) *
        (χ₂ (M : ZMod q) * χ₂⁻¹ (M : ZMod q)) *
        (cChi χ₁⁻¹ 1 * cChi χ₂⁻¹ 1 * cChi (χ₁ * χ₂) N) := by ring
    _ = _ := by rw [h₁, h₂, one_mul, one_mul]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.crt_phase443
#print axioms LeanLab.BhowmikGrimmelt2026.unit_crt_sum443

#print axioms LeanLab.BhowmikGrimmelt2026.gaussSum_units443
#print axioms LeanLab.BhowmikGrimmelt2026.cChi_crt_shift443

#print axioms LeanLab.BhowmikGrimmelt2026.cChi_mul_unit443
#print axioms LeanLab.BhowmikGrimmelt2026.coefficient_phase_cancel443
