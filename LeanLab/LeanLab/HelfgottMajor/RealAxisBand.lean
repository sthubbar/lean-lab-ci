import LeanLab.HelfgottMajor.RealAxisSmall
import LeanLab.HelfgottMajor.RealAxisSix
import LeanLab.HelfgottMajor.RealAxisFifteenSixteen
import LeanLab.HelfgottMajor.RealAxisEleven
import LeanLab.HelfgottMajor.RealAxisThirteen
import LeanLab.HelfgottMajor.RealAxisSeventeenOdd
import LeanLab.HelfgottMajor.RealAxisSeventeenEven

/-!
# No zero of `L(σ, χ)` on the positive real axis for moduli at most seventeen

Assembly of the per modulus theorems. For every non principal Dirichlet character `χ` of
modulus `q ≤ 17` and every real `σ > 0`, `L(σ, χ) ≠ 0`. Each modulus is settled in its own file
by the kernel criterion of `RealAxisKernel`: the generating polynomial `∑_{a < q} χ(a) x^a`
stays in a half plane for `0 < x < 1`. This is standard mathematics, the Mellin transform
representation of `Γ(s) L(s, χ)`, see Davenport, Multiplicative Number Theory, chapter 9; the
finite verification for these moduli agrees with the numerical verifications of the
generalized Riemann hypothesis at low height for small conductors.

Also: the band `1 ≤ T`, `q * T ≤ 2πe` forces `q ≤ 17`, and a primitive character of modulus
other than one is not principal.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.RealAxisKernel

/-- Modulus seventeen: a non principal character sends the generator `3` to a sixteenth root
of unity, whose eighth power is `1` or `-1`; the two cases are the even and the odd
characters. -/
theorem LFunction_ofReal_ne_zero_mod_17 (χ : DirichletCharacter ℂ 17) (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 0 < σ) : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have h16 : χ (3 : ZMod 17) ^ 16 = 1 := by
    rw [← map_pow, show (3 : ZMod 17) ^ 16 = 1 by decide, map_one]
  have hsq : (χ (3 : ZMod 17) ^ 8 - 1) * (χ (3 : ZMod 17) ^ 8 + 1) = 0 := by
    linear_combination h16
  rcases mul_eq_zero.mp hsq with h | h
  · exact LFunction_ofReal_ne_zero_mod_17_even χ hχ (by linear_combination h) hσ
  · exact LFunction_ofReal_ne_zero_mod_17_odd χ (by linear_combination h) hσ

/-- For every non principal character of modulus at most seventeen, `L(σ, χ) ≠ 0` for every
real `σ > 0`. -/
theorem LFunction_ofReal_ne_zero_of_le_seventeen {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : q ≤ 17) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hcases : q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨
      q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 15 ∨ q = 16 ∨ q = 17 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact absurd (DirichletCharacter.level_one χ) hχ
  · exact LFunction_ofReal_ne_zero_mod_2 χ hχ hσ
  · exact LFunction_ofReal_ne_zero_mod_3 χ hχ hσ
  · exact LFunction_ofReal_ne_zero_mod_4 χ hχ hσ
  · exact LFunction_ofReal_ne_zero_mod_5 χ hχ hσ
  · exact LFunction_ofReal_ne_zero_mod_6 χ hχ hσ
  · exact LFunction_ofReal_ne_zero_mod_7 χ hχ hσ
  · exact LFunction_ofReal_ne_zero_mod_8 χ hχ hσ
  · exact LFunction_ofReal_ne_zero_mod_9 χ hχ hσ
  · exact LFunction_ofReal_ne_zero_mod_10 χ hχ hσ
  · exact LFunction_ofReal_ne_zero_mod_11 χ hχ hσ
  · exact LFunction_ofReal_ne_zero_mod_12 χ hχ hσ
  · exact LFunction_ofReal_ne_zero_mod_13 χ hχ hσ
  · exact LFunction_ofReal_ne_zero_mod_14 χ hχ hσ
  · exact LFunction_ofReal_ne_zero_mod_15 χ hχ hσ
  · exact LFunction_ofReal_ne_zero_mod_16 χ hχ hσ
  · exact LFunction_ofReal_ne_zero_mod_17 χ hχ hσ

/-- On the band `1 ≤ T`, `q * T ≤ 2πe` the modulus is at most seventeen, since
`2πe < 18`. -/
theorem modulus_le_seventeen_of_band {q : ℕ} {T : ℝ} (hT : 1 ≤ T)
    (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) : q ≤ 17 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : (q : ℝ) ≤ (q : ℝ) * T := le_mul_of_one_le_right hq0 hT
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have he : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hpe : 2 * Real.pi * Real.exp 1 < 18 := by
    have h2 : 2 * Real.pi * Real.exp 1 ≤ 2 * 3.15 * 2.72 := by
      have := Real.pi_pos
      have := Real.exp_pos 1
      nlinarith
    linarith [show (2 : ℝ) * 3.15 * 2.72 < 18 by norm_num]
  have hlt : (q : ℝ) < 18 := by linarith
  have : q < 18 := by exact_mod_cast hlt
  omega

/-- A primitive character of modulus other than one is not principal: the principal
character has conductor one. -/
theorem ne_one_of_isPrimitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) : χ ≠ 1 := by
  rintro rfl
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hχ
  exact hq hχ.symm

/-- On the band, a primitive character of modulus other than one has no zero on the positive
real axis. -/
theorem LFunction_ofReal_ne_zero_of_band {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) (hq : q ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 :=
  LFunction_ofReal_ne_zero_of_le_seventeen χ (ne_one_of_isPrimitive χ hχ hq)
    (modulus_le_seventeen_of_band hT hband) hσ

end LeanLab.HelfgottMajor.RealAxisKernel
