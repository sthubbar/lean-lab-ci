import LeanLab.Ricci1937.CLinear
import LeanLab.Ricci1937.Statements

/-!
Ricci 1937, page 74: the qualitative degree one case using Dirichlet's theorem.
The introduction cites Dirichlet. This is not Ricci's elementary sieve proof.
It does not supply the quantitative count in Theorem C.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
noncomputable section

/-- A nonnegative shifted primitive linear progression has coprime natural coefficients. -/
lemma linear_shift_coprime {P : Polynomial ℤ} (hprim : P.IsPrimitive)
    (hdegree : P.natDegree ≤ 1) (n : ℕ) (ha : 0 ≤ P.coeff 1)
    (hb : 0 ≤ P.eval (n : ℤ)) :
    Nat.Coprime (P.coeff 1).toNat (P.eval (n : ℤ)).toNat := by
  let a := (P.coeff 1).toNat
  let b := (P.eval (n : ℤ)).toNat
  let d := Nat.gcd a b
  change d = 1
  have ha_cast : (a : ℤ) = P.coeff 1 := Int.toNat_of_nonneg ha
  have hb_cast : (b : ℤ) = P.eval (n : ℤ) := Int.toNat_of_nonneg hb
  have hda : (d : ℤ) ∣ P.coeff 1 := by
    rw [← ha_cast]
    exact Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left a b)
  have hdb : (d : ℤ) ∣ P.eval (n : ℤ) := by
    rw [← hb_cast]
    exact Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right a b)
  have heval : P.eval (n : ℤ) = P.coeff 1 * n + P.coeff 0 := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdegree]
    simp
  have hdc : (d : ℤ) ∣ P.coeff 0 := by
    have h := dvd_sub hdb (dvd_mul_of_dvd_left hda (n : ℤ))
    rw [heval] at h
    simpa using h
  have hu := hprim (d : ℤ) (by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    by_cases hi0 : i = 0
    · subst i; exact hdc
    by_cases hi1 : i = 1
    · subst i; exact hda
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact dvd_zero _)
  simpa only [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] using hu

/-- Infinitely many prime values for every polynomial in the degree one case.
Dirichlet's theorem supplies the primes. No count estimate is asserted. -/
theorem linear_Fval_prime_infinite {P : Polynomial ℤ} (hP : CHyp P)
    (hdegree : P.natDegree = 1) :
    {n : ℕ | 1 ≤ n ∧ (Fval P n).Prime}.Infinite := by
  have haZ : 0 < P.coeff 1 := by
    simpa only [Polynomial.leadingCoeff, hdegree] using hP.2.2.2
  let A : ℕ := (P.coeff 1).toNat
  let M : ℕ := (P.coeff 0).natAbs + 1
  let B : ℕ := (P.eval (M : ℤ)).toNat
  have hA : 0 < A := by dsimp [A]; omega
  have hA_cast : (A : ℤ) = P.coeff 1 := Int.toNat_of_nonneg haZ.le
  have heval (n : ℕ) : P.eval (n : ℤ) = P.coeff 1 * n + P.coeff 0 := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdegree.le]
    simp
  have hMval : 1 ≤ P.eval (M : ℤ) := by
    rw [heval]
    have hbound : -((P.coeff 0).natAbs : ℤ) ≤ P.coeff 0 := by
      have h := Int.le_natAbs (a := -(P.coeff 0))
      rw [Int.natAbs_neg] at h
      omega
    have ha1 : 1 ≤ P.coeff 1 := haZ
    dsimp [M]
    nlinarith [Int.natCast_nonneg (P.coeff 0).natAbs]
  have hB_cast : (B : ℤ) = P.eval (M : ℤ) := Int.toNat_of_nonneg (by omega)
  have hab : Nat.Coprime A B := linear_shift_coprime hP.2.1 hdegree.le M haZ.le (by omega)
  apply Set.infinite_of_forall_exists_gt
  intro T
  obtain ⟨p, hpT, hp, x, hx, hpx⟩ := primes_in_ap_terms A B hA hab (A * T + B)
  have hxT : T < x := by
    by_contra hh
    have hmono := Nat.mul_le_mul_left A (show x ≤ T by omega)
    omega
  have hv : P.eval ((M + x : ℕ) : ℤ) = (p : ℤ) := by
    rw [heval]
    have hpZ : (p : ℤ) = A * x + B := by exact_mod_cast hpx
    rw [hA_cast, hB_cast, heval] at hpZ
    push_cast
    nlinarith
  refine ⟨M + x, ⟨by omega, ?_⟩, by omega⟩
  rw [Fval_of_linear hP.2.1 hdegree.le, hv, Int.toNat_natCast]
  exact hp

/-- A prime large enough compared with its index satisfies the C1 factor condition. -/
lemma almostGT_two_of_prime_index {p n : ℕ} (hp : p.Prime) (hn : n ≤ 2 * p) :
    AlmostGT 2 ((n : ℝ) ^ ((1 : ℝ) / 3)) p := by
  refine ⟨hp.one_le, ?_, ?_⟩
  · rw [Nat.primeFactorsList_prime hp]
    simp
  · intro q hq
    rw [Nat.primeFactorsList_prime hp, List.mem_singleton] at hq
    subst q
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hnR : (n : ℝ) ≤ 2 * p := by exact_mod_cast hn
    have hsq : (2 : ℝ) * p ≤ (p : ℝ) ^ (2 : ℕ) := by nlinarith
    have hcube : (n : ℝ) < (p : ℝ) ^ (3 : ℕ) := by
      have hmul := mul_le_mul_of_nonneg_right hsq (show (0 : ℝ) ≤ p by positivity)
      nlinarith
    have h := Real.rpow_lt_rpow (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hcube
      (by norm_num : (0 : ℝ) < 1 / 3)
    have hroot : ((p : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) = p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
      norm_num
    rwa [hroot] at h

/-- The qualitative C1 assertion for every degree one polynomial, from Dirichlet.
The quantitative two sided count is still not asserted here. -/
theorem linear_c1_indices_infinite {P : Polynomial ℤ} (hP : CHyp P)
    (hdegree : P.natDegree = 1) :
    {n : ℕ | 1 ≤ n ∧ AlmostGT 2 ((n : ℝ) ^ ((1 : ℝ) / 3)) (Fval P n)}.Infinite := by
  have hInf := linear_Fval_prime_infinite hP hdegree
  have haZ : 1 ≤ P.coeff 1 := by
    have : 0 < P.coeff 1 := by
      simpa only [Polynomial.leadingCoeff, hdegree] using hP.2.2.2
    omega
  apply Set.infinite_of_forall_exists_gt
  intro T
  obtain ⟨n, ⟨hn1, hp⟩, hnlarge⟩ := Set.infinite_iff_exists_gt.mp hInf
    (max T (2 * (P.coeff 0).natAbs + 1))
  refine ⟨n, ⟨hn1, almostGT_two_of_prime_index hp ?_⟩, by omega⟩
  have hbound : -((P.coeff 0).natAbs : ℤ) ≤ P.coeff 0 := by
    have h := Int.le_natAbs (a := -(P.coeff 0))
    rw [Int.natAbs_neg] at h
    omega
  have htoNat : P.eval (n : ℤ) ≤ (Fval P n : ℤ) := by
    rw [Fval_of_linear hP.2.1 hdegree.le]
    exact Int.self_le_toNat _
  have heval : P.eval (n : ℤ) = P.coeff 1 * n + P.coeff 0 := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdegree.le]
    simp
  rw [heval] at htoNat
  have hnZ : (2 : ℤ) * (P.coeff 0).natAbs + 1 < n := by
    exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hnlarge)
  have hnp : (n : ℤ) ≤ 2 * (Fval P n : ℤ) := by
    nlinarith [Int.natCast_nonneg n]
  exact_mod_cast hnp

example : {n : ℕ | 1 ≤ n ∧ AlmostGT 2 ((n : ℝ) ^ ((1 : ℝ) / 3))
    (Fval (Polynomial.X : Polynomial ℤ) n)}.Infinite := by
  apply linear_c1_indices_infinite
  · exact ⟨by simp, Polynomial.monic_X.isPrimitive, Polynomial.irreducible_X, by simp⟩
  · simp

end
end LeanLab.Ricci1937
