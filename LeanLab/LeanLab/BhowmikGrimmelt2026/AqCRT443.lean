/-
Two factor CRT identity for the normalized generalized coefficient.
Source: Pintz Part I pages 19 and 20, displays 7.9 to 7.14.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.CRTGauss443

namespace LeanLab.BhowmikGrimmelt2026

/-- The three shifted Gauss sums factor with exact cancellation of their common phases.
Source: Pintz Part I page 20 display 7.13, finite CRT step. -/
theorem Aq_crt443 {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (χ₁ χ₂ : DirichletCharacter ℂ m)
    (ψ₁ ψ₂ : DirichletCharacter ℂ n) (N : ℤ) :
    Aq (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ₁ *
        DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) ψ₁)
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ₂ *
        DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) ψ₂) N (m * n) =
      Aq χ₁ χ₂ N m * Aq ψ₁ ψ₂ N n := by
  let A := (m : ℤ).gcdA n
  let B := (m : ℤ).gcdB n
  have hAB : A * m + B * n = 1 := by
    have h := Int.gcd_eq_gcd_ab (m : ℤ) (n : ℤ)
    rw [Int.gcd_natCast_natCast, hcop.gcd_eq_one] at h
    dsimp [A, B]
    linear_combination -h
  have hAeq : (A : ZMod n) * (m : ZMod n) = 1 := by
    have h := congrArg (Int.castRingHom (ZMod n)) hAB
    simpa using h
  have hBeq : (B : ZMod m) * (n : ZMod m) = 1 := by
    have h := congrArg (Int.castRingHom (ZMod m)) hAB
    simpa using h
  have hA : IsUnit (A : ZMod n) :=
    ⟨⟨A, m, hAeq, by simpa only [mul_comm] using hAeq⟩, rfl⟩
  have hB : IsUnit (B : ZMod m) :=
    ⟨⟨B, n, hBeq, by simpa only [mul_comm] using hBeq⟩, rfl⟩
  have ht (χ : DirichletCharacter ℂ m) (ψ : DirichletCharacter ℂ n) :
      tauConj (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ *
        DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) ψ) =
        cChi χ⁻¹ B * cChi ψ⁻¹ A := by
    rw [tauConj_eq_cChi_inv436]
    simpa only [map_inv, mul_inv_rev, mul_one, mul_comm] using
      cChi_crt_shift443 hcop χ⁻¹ ψ⁻¹ A B hAB 1
  have hprod :
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ₁ *
          DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) ψ₁) *
        (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ₂ *
          DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) ψ₂) =
      DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) (χ₁ * χ₂) *
        DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) (ψ₁ * ψ₂) := by
    simp only [map_mul]
    ac_rfl
  have hc := cChi_crt_shift443 hcop (χ₁ * χ₂) (ψ₁ * ψ₂) A B hAB N
  have hnum :
      (cChi χ₁⁻¹ B * cChi ψ₁⁻¹ A) * (cChi χ₂⁻¹ B * cChi ψ₂⁻¹ A) *
        (cChi (χ₁ * χ₂) (B * N) * cChi (ψ₁ * ψ₂) (A * N)) =
        (tauConj χ₁ * tauConj χ₂ * cChi (χ₁ * χ₂) N) *
          (tauConj ψ₁ * tauConj ψ₂ * cChi (ψ₁ * ψ₂) N) := by
    calc
      _ = (cChi χ₁⁻¹ B * cChi χ₂⁻¹ B * cChi (χ₁ * χ₂) (B * N)) *
          (cChi ψ₁⁻¹ A * cChi ψ₂⁻¹ A * cChi (ψ₁ * ψ₂) (A * N)) := by ring
      _ = _ := by rw [coefficient_phase_cancel443 χ₁ χ₂ B N hB,
        coefficient_phase_cancel443 ψ₁ ψ₂ A N hA]
  simp only [Aq, dif_pos (show m * n ∣ m * n ∧ m * n ∣ m * n from ⟨dvd_refl _, dvd_refl _⟩),
    dif_pos (show m ∣ m ∧ m ∣ m from ⟨dvd_refl _, dvd_refl _⟩),
    dif_pos (show n ∣ n ∧ n ∣ n from ⟨dvd_refl _, dvd_refl _⟩),
    DirichletCharacter.changeLevel_self]
  rw [ht, ht, hprod, hc, hnum, Nat.totient_mul hcop, Nat.cast_mul, mul_pow]
  exact mul_div_mul_comm _ _ _ _

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.Aq_crt443
