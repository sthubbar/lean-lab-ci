import LeanLab.Ricci1937.TheoremsCD

/-!
Ricci 1937, pages 74 and 77: the fixed divisor in degree one.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
noncomputable section

/-- If every common divisor of the positive values is one, the fixed divisor is one. -/
lemma fixedDivisor_eq_one_of_common_divisors (P : Polynomial ℤ)
    (h : ∀ d : ℕ, (∀ n : ℕ, 1 ≤ n → (d : ℤ) ∣ P.eval (n : ℤ)) → d = 1) :
    fixedDivisor P = 1 := by
  unfold fixedDivisor
  have hset : {d : ℕ | ∀ n : ℕ, 1 ≤ n → (d : ℤ) ∣ P.eval (n : ℤ)} = {1} := by
    ext d
    constructor
    · intro hd
      simpa using h d hd
    · intro hd
      have : d = 1 := by simpa using hd
      subst d
      simp
  rw [hset, csSup_singleton]

/-- A primitive linear integer polynomial has fixed divisor one. -/
lemma fixedDivisor_eq_one_of_linear {P : Polynomial ℤ} (hprim : P.IsPrimitive)
    (hdegree : P.natDegree ≤ 1) : fixedDivisor P = 1 := by
  apply fixedDivisor_eq_one_of_common_divisors
  intro d hd
  have hlin := Polynomial.eq_X_add_C_of_natDegree_le_one hdegree
  have h1 := hd 1 (by omega)
  have h2 := hd 2 (by omega)
  rw [hlin] at h1 h2
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Nat.cast_one, Nat.cast_ofNat] at h1 h2
  have ha : (d : ℤ) ∣ P.coeff 1 := by
    have := dvd_sub h2 h1
    convert this using 1
    ring
  have hb : (d : ℤ) ∣ P.coeff 0 := by
    have := dvd_sub h1 ha
    convert this using 1
    ring
  have hu : IsUnit (d : ℤ) := hprim d (by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    by_cases hi0 : i = 0
    · subst i; exact hb
    by_cases hi1 : i = 1
    · subst i; exact ha
    have hcoeff : P.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hcoeff]
    exact dvd_zero _)
  simpa only [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] using hu

/-- In degree one the integer valued polynomial needs no division. -/
lemma Fval_of_linear {P : Polynomial ℤ} (hprim : P.IsPrimitive)
    (hdegree : P.natDegree ≤ 1) (n : ℕ) :
    Fval P n = (P.eval (n : ℤ)).toNat := by
  simp [Fval, fixedDivisor_eq_one_of_linear hprim hdegree]

example : fixedDivisor (Polynomial.X : Polynomial ℤ) = 1 :=
  fixedDivisor_eq_one_of_linear Polynomial.monic_X.isPrimitive (by simp)

example (n : ℕ) : Fval (Polynomial.X : Polynomial ℤ) n = n := by
  rw [Fval_of_linear Polynomial.monic_X.isPrimitive (by simp)]
  simp

end
end LeanLab.Ricci1937
