/-
P0093 pages 156 and 159 through 161. The three character terms of equation 3.4.
The principal integral is extended to a full period as in equations 6.2 and 6.3.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp491a

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- P0093 page 155 equation 2.3. Conjugate Gauss coefficient in natural residues. -/
noncomputable def conjugateGauss491 (q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  star (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    χ a * Complex.exp (((2 * Real.pi * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I))

/-- P0093 page 156 equation 3.4. The signed reduced residue phase. -/
noncomputable def signedRamanujan491 (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)

/-- P0093 page 156 equation 3.4. One ordered character pair contribution. -/
noncomputable def characterPair491 (N q : ℕ) (n : ℤ)
    (χ ψ : DirichletCharacter ℂ q) : ℂ :=
  (1 / (q.totient : ℂ) ^ 2) * conjugateGauss491 q χ * conjugateGauss491 q ψ *
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      χ a * ψ a * Complex.exp
        (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) *
    (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      characterPrime280 χ N z * characterPrime280 ψ N z *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))

/-- P0093 page 160 equation 6.1. The principal square integral alone. -/
noncomputable def principalIntegral491 (N q : ℕ) (n : ℤ) : ℂ :=
  ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
      (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
    characterPrime280 (1 : DirichletCharacter ℂ q) N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)

/-- P0093 page 156 equation 3.4. The term I zero. -/
noncomputable def principalTerm491 (N q : ℕ) (n : ℤ) : ℂ :=
  ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
    signedRamanujan491 q n) * principalIntegral491 N q n

/-- P0093 page 156 equation 3.4. The mixed term I one, with both ordered pairs. -/
noncomputable def mixedTerm491 (N q : ℕ) [NeZero q] (n : ℤ) : ℂ :=
  ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
    (characterPair491 N q n 1 χ + characterPair491 N q n χ 1)

/-- P0093 page 156 equation 3.4. The term I two with both characters nonprincipal. -/
noncomputable def nonprincipalTerm491 (N q : ℕ) [NeZero q] (n : ℤ) : ℂ :=
  ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
    ∑ ψ ∈ univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1),
      characterPair491 N q n χ ψ

/-- LEAF. P0093 page 156 equation 3.4. Separate the three character terms.
Only the omitted prime divisors of q contribute to this remainder.
The frequency has no effect on its norm estimate. No GRH is used. -/
theorem character_decomposition491 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        letI : NeZero q := ⟨by omega⟩
        ∀ n : ℤ, ‖localArc1622 N q n -
          (principalTerm491 N q n + mixedTerm491 N q n + nonprincipalTerm491 N q n)‖ ≤
          C * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := by
  sorry

/-- LEAF. P0093 page 160 equation 5.4. The term with two nonprincipal
characters is bounded using the character square estimate. It contains no
principal integral and no reciprocal logarithm convolution. -/
theorem nonprincipal_bound491 (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        letI : NeZero q := ⟨by omega⟩
        ∀ n : ℤ, ‖nonprincipalTerm491 N q n‖ ≤
          C * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 := by
  sorry

/-- LEAF. P0093 page 160 equation 5.5. The mixed character term has
logarithmic exponent six and denominator square root of q tau.
It has no principal square integral and no convolution main term. -/
theorem mixed_bound491 (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        letI : NeZero q := ⟨by omega⟩
        ∀ n : ℤ, ‖mixedTerm491 N q n‖ ≤
          C * (N : ℝ) * Real.log N ^ 6 /
            Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- LEAF. P0093 pages 160 and 161 equations 6.1 through 6.3.
The principal square integral is replaced by the exact damped logarithmic
convolution through a full period, retaining both displayed errors.
The damping is exp of minus n over N before multiplication by tuple weights. -/
theorem principal_convolution491 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
        ‖principalIntegral491 N q n -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. P0093 page 156 equation 3.4. The principal arithmetic coefficient
has norm at most one for every positive modulus and every signed frequency. -/
theorem principal_coefficient_norm491 (q : ℕ) (hq : 1 ≤ q) (n : ℤ) :
    ‖(((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
      signedRamanujan491 q n‖ ≤ 1 := by
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hμ : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  have hμ2 : (ArithmeticFunction.moebius q : ℝ) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) hμ 2
  have hr : ‖signedRamanujan491 q n‖ ≤ (q.totient : ℝ) := by
    unfold signedRamanujan491
    calc
      _ ≤ ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ‖Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)‖ :=
        norm_sum_le _ _
      _ = (q.totient : ℝ) := by
        simp only [Complex.norm_exp_ofReal_mul_I, sum_const, nsmul_eq_mul, mul_one]
        congr 1
        rw [Nat.totient_eq_card_coprime]
        congr 1
        ext a
        simp [Nat.coprime_comm]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) * q.totient := by
      gcongr
    _ ≤ 1 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (show (0 : ℝ) < (q.totient : ℝ) ^ 2 by positivity)).mpr
      have hsq : (q.totient : ℝ) ≤ (q.totient : ℝ) ^ 2 := by nlinarith
      exact (mul_le_mul_of_nonneg_right hμ2 (by positivity)).trans (by simpa using hsq)

/-- LEAF. P0093 page 161 equation 6.4. For nonnegative residuals the signed
reduced residue phase is the existing natural Ramanujan sum. -/
theorem signedRamanujan_toNat491 (q : ℕ) (n : ℤ) (hn : 0 ≤ n) :
    signedRamanujan491 q n = LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat := by
  have hc : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
  unfold signedRamanujan491 LeanLab.Perelli1996.Ramanujan103.ramanujanSum
    LeanLab.Perelli1996.Kernel.e
  apply sum_congr rfl
  intro a ha
  rw [hc]
  congr 1
  push_cast
  ring

/-- LEAF. P0093 page 161 equation 6.4. The coefficient times the exact
convolution agrees with the sealed main term, also at negative residuals. -/
theorem principal_main_eq491 (N q : ℕ) (n : ℤ) :
    ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
      signedRamanujan491 q n) *
        ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ) =
      localMain491 N q n := by
  by_cases hn : 0 ≤ n
  · rw [signedRamanujan_toNat491 q n hn]
    rfl
  · have hz : n.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    simp [localMain491, hz, logConvolution_vanish491 0 (by omega)]

/-- LEAF. P0093 page 156 equation 3.4. At modulus one every character is
principal, so the mixed term is exactly zero. -/
theorem mixed_unit491 (N : ℕ) (n : ℤ) : mixedTerm491 N 1 n = 0 := by
  have hχ : ∀ χ : DirichletCharacter ℂ 1, χ = 1 := fun χ => Subsingleton.elim _ _
  simp [mixedTerm491, hχ]

/-- LEAF. P0093 page 156 equation 3.4. At modulus one the term with two
nonprincipal characters is exactly zero. -/
theorem nonprincipal_unit491 (N : ℕ) (n : ℤ) : nonprincipalTerm491 N 1 n = 0 := by
  have hχ : ∀ χ : DirichletCharacter ℂ 1, χ = 1 := fun χ => Subsingleton.elim _ _
  simp [nonprincipalTerm491, hχ]

/-- LEAF. P0093 page 155 equation 2.3. At modulus one the principal character
prime series is the full prime Fourier series. -/
theorem principal_unit_series491 (N : ℕ) (z : ℝ) :
    characterPrime280 (1 : DirichletCharacter ℂ 1) N z = primeFourier111 N z := by
  unfold characterPrime280 primeFourier111
  apply tsum_congr
  intro p
  have hp : (1 : DirichletCharacter ℂ 1) (p : ℕ) = 1 :=
    MulChar.one_apply (by rw [Subsingleton.elim ((p : ℕ) : ZMod 1) 1]; exact isUnit_one)
  simp only [hp, one_mul]

/-- LEAF. P0093 page 156 equation 3.4. At modulus one the character
decomposition is exact with no omitted prime divisor error. -/
theorem character_decomposition_unit491 (N : ℕ) (n : ℤ) :
    localArc1622 N 1 n =
      principalTerm491 N 1 n + mixedTerm491 N 1 n + nonprincipalTerm491 N 1 n := by
  rw [mixed_unit491, nonprincipal_unit491, add_zero, add_zero]
  simp [localArc1622, principalTerm491, signedRamanujan491, principalIntegral491,
    principal_unit_series491]

/-- LEAF. P0093 page 161 equation 6.4. Elementary assembly of the four written
estimates. CONDITIONAL on character_decomposition491, nonprincipal_bound491,
mixed_bound491 and principal_convolution491. -/
theorem local_expansion_assembled491 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, LocalExpansion1622 B N0 := by
  obtain ⟨C0, hC0, N0, h0⟩ := character_decomposition491
  obtain ⟨C1, hC1, N1, h1⟩ := mixed_bound491 hM
  obtain ⟨C2, hC2, N2, h2⟩ := nonprincipal_bound491 hM
  obtain ⟨C3, hC3, N3, h3⟩ := principal_convolution491 hG hM
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨C0 + C1 + C2 + C3, by positivity,
    max 2 (max L (max N0 (max N1 (max N2 N3)))), ?_⟩
  intro N hN q hq hqQ n hn
  have hN2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNL : L < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNs : max N0 (max N1 (max N2 N3)) < N :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_left _ _) hNs
  have hN1 : N1 < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hNs
  have hN2' : N2 < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hNs
  have hN3 : N3 < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hNs
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 1 ≤ Real.log N := by
    have hreal : (L : ℝ) < (N : ℝ) := by exact_mod_cast hNL
    have hh := Real.log_le_log (Real.exp_pos 1) (hL.trans hreal).le
    simpa using hh
  have hqN : (q : ℝ) ≤ N := hqQ.trans (by
    convert Real.rpow_le_rpow_of_exponent_le hNr (show (1 / 10 : ℝ) ≤ 1 by norm_num) using 1
    rw [Real.rpow_one])
  have hlogq : Real.log q ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (show 0 < q by omega)) hqN
  have hlog13 : Real.log N ≤ Real.log N ^ 13 := by
    simpa using pow_le_pow_right₀ hlog (show 1 ≤ 13 by omega)
  have hlog6 : Real.log N ^ 6 ≤ Real.log N ^ 13 :=
    pow_le_pow_right₀ hlog (by omega)
  let τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ)
  let X : ℝ := (N : ℝ) * Real.log N ^ 13
  let E : ℝ := X * (1 / τ + 1 / Real.sqrt ((q : ℝ) * τ))
  have hτ : 0 < τ := Real.rpow_pos_of_pos (by positivity) _
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hfirst : X / τ ≤ E := by
    dsimp [E]
    simpa only [div_eq_mul_inv, one_div, mul_add, one_mul] using
      (le_add_of_nonneg_right (show 0 ≤ X / Real.sqrt ((q : ℝ) * τ) by positivity) :
        X / τ ≤ X / τ + X / Real.sqrt ((q : ℝ) * τ))
  have hsecond : X / Real.sqrt ((q : ℝ) * τ) ≤ E := by
    dsimp [E]
    simpa only [div_eq_mul_inv, one_div, mul_add, one_mul] using
      (le_add_of_nonneg_left (show 0 ≤ X / τ by positivity) :
        X / Real.sqrt ((q : ℝ) * τ) ≤ X / τ + X / Real.sqrt ((q : ℝ) * τ))
  letI : NeZero q := ⟨by omega⟩
  have ha : ‖localArc1622 N q n -
      (principalTerm491 N q n + mixedTerm491 N q n + nonprincipalTerm491 N q n)‖ ≤ C0 * E := by
    calc
      _ ≤ C0 * N * Real.log q / τ := h0 N hN0 q hq hqQ n
      _ ≤ C0 * N * Real.log N ^ 13 / τ := by gcongr; exact hlogq.trans hlog13
      _ = C0 * X / τ := by dsimp [X]; ring
      _ = C0 * (X / τ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfirst hC0.le
  have hb : ‖mixedTerm491 N q n‖ ≤ C1 * E := by
    calc
      _ ≤ C1 * N * Real.log N ^ 6 / Real.sqrt ((q : ℝ) * τ) := h1 N hN1 q hq hqQ n
      _ ≤ C1 * N * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * τ) := by gcongr
      _ = C1 * X / Real.sqrt ((q : ℝ) * τ) := by dsimp [X]; ring
      _ = C1 * (X / Real.sqrt ((q : ℝ) * τ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsecond hC1.le
  have hc : ‖nonprincipalTerm491 N q n‖ ≤ C2 * E := by
    calc
      _ ≤ C2 * N / τ * Real.log N ^ 13 := h2 N hN2' q hq hqQ n
      _ = C2 * (X / τ) := by dsimp [X]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfirst hC2.le
  have hd : ‖principalTerm491 N q n - localMain491 N q n‖ ≤ C3 * E := by
    rw [← principal_main_eq491]
    unfold principalTerm491
    rw [← mul_sub, norm_mul]
    have hp := h3 N hN3 q hq hqQ n hn
    have hcoef := principal_coefficient_norm491 q hq n
    have hrec : 1 / ((q : ℝ) * τ) ≤ 1 / τ := by
      apply one_div_le_one_div_of_le hτ
      have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith
    calc
      _ ≤ 1 * ‖principalIntegral491 N q n -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ ≤ C3 * X * (1 / ((q : ℝ) * τ) + 1 / Real.sqrt ((q : ℝ) * τ)) := by
        simpa [X, τ, mul_assoc] using hp
      _ ≤ C3 * X * (1 / τ + 1 / Real.sqrt ((q : ℝ) * τ)) := by gcongr
      _ = _ := by dsimp [E]; ring
  change ‖localArc1622 N q n - localMain491 N q n‖ ≤ _
  have htri : ‖localArc1622 N q n - localMain491 N q n‖ ≤
      ‖localArc1622 N q n - (principalTerm491 N q n + mixedTerm491 N q n + nonprincipalTerm491 N q n)‖ +
      ‖principalTerm491 N q n - localMain491 N q n‖ +
      ‖mixedTerm491 N q n‖ + ‖nonprincipalTerm491 N q n‖ := by
    have heq : localArc1622 N q n - localMain491 N q n =
        (localArc1622 N q n - (principalTerm491 N q n + mixedTerm491 N q n + nonprincipalTerm491 N q n)) +
        (principalTerm491 N q n - localMain491 N q n) + mixedTerm491 N q n + nonprincipalTerm491 N q n := by ring
    rw [heq]
    let e := localArc1622 N q n -
      (principalTerm491 N q n + mixedTerm491 N q n + nonprincipalTerm491 N q n)
    let p := principalTerm491 N q n - localMain491 N q n
    change ‖e + p + mixedTerm491 N q n + nonprincipalTerm491 N q n‖ ≤
      ‖e‖ + ‖p‖ + ‖mixedTerm491 N q n‖ + ‖nonprincipalTerm491 N q n‖
    calc
      _ ≤ ‖e + p + mixedTerm491 N q n‖ + ‖nonprincipalTerm491 N q n‖ := norm_add_le _ _
      _ ≤ (‖e + p‖ + ‖mixedTerm491 N q n‖) + ‖nonprincipalTerm491 N q n‖ := by
        linarith [norm_add_le (e + p) (mixedTerm491 N q n)]
      _ ≤ _ := by linarith [norm_add_le e p]
  have hsum := htri.trans (add_le_add (add_le_add (add_le_add ha hd) hb) hc)
  calc
    _ ≤ C0 * E + C3 * E + C1 * E + C2 * E := hsum
    _ = _ := by dsimp [E, X, τ]; ring

end LeanLab.Linnik1951
