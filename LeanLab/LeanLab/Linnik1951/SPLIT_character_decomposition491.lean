/-
The three character term decomposition of the local major arc integral at an
integer residual, cut into two steps: the finite character square expansion of
the local arc at each fixed residual, and the exact separation of that square
into the principal, the mixed and the nonprincipal character blocks.

The square is the double sum of the ordered character pair contribution over all
pairs of characters of the modulus. Expanding the square of the prime Fourier
series against the characters of the modulus is exact for the primes coprime to
the modulus, so the expansion differs from the local arc only through the primes
dividing the modulus and through the finite integral rearrangement. The residual
is carried separately for nonnegative and for negative residuals, since the two
regions use conjugate reduced residue phases. The separation of the square into
the three named blocks is a finite rearrangement with no error term.
-/
import LeanLab.Linnik1951.Decomp491b

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- LEAF. The conjugate Gauss coefficient of the principal character is the
Moebius value at the modulus. -/
private lemma conjGauss_one491 (q : ℕ) (hq : 1 ≤ q) :
    conjugateGauss491 q (1 : DirichletCharacter ℂ q) = (ArithmeticFunction.moebius q : ℂ) := by
  have hone : conjugateGauss491 q (1 : DirichletCharacter ℂ q) =
      star (signedRamanujan491 q 1) := by
    unfold conjugateGauss491 signedRamanujan491
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
    have hunit : IsUnit ((a : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr hcop
    rw [MulChar.one_apply hunit, one_mul]
    congr 1
    push_cast
    ring
  rw [hone, signedRamanujan_toNat491 q 1 (by norm_num)]
  have hto : (Int.toNat 1 : ℕ) = 1 := rfl
  rw [hto, LeanLab.Perelli1996.Ramanujan103.ramanujanSum_coprime q 1 (by omega)
      (Nat.coprime_one_right q)]
  simp

/-- LEAF. The ordered pair of two principal characters is the principal term. -/
private lemma pair_one_one491 (N q : ℕ) (hq : 1 ≤ q) (n : ℤ) :
    characterPair491 N q n 1 1 = principalTerm491 N q n := by
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hτ : conjugateGauss491 q (1 : DirichletCharacter ℂ q) =
      (ArithmeticFunction.moebius q : ℂ) := conjGauss_one491 q hq
  have hone (a : ℕ) (ha : a ∈ (range q).filter (fun a => Nat.Coprime a q)) :
      (1 : DirichletCharacter ℂ q) a = 1 := by
    have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime a q).mpr hcop)
  unfold characterPair491 principalTerm491 principalIntegral491 signedRamanujan491
  rw [hτ]
  have hsum : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      (1 : DirichletCharacter ℂ q) a * (1 : DirichletCharacter ℂ q) a *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hone a ha]
    ring
  rw [hsum]
  have hcoef : (1 / ((q.totient : ℂ)) ^ 2) * ((ArithmeticFunction.moebius q : ℂ)) *
      ((ArithmeticFunction.moebius q : ℂ)) =
      (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) := by
    have hne : ((q.totient : ℂ)) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr hφpos.ne')
    push_cast
    field_simp
  rw [hcoef]
  simp only [sq]

/-- LEAF. Finite character square expansion at a nonnegative residual. For a
modulus inside the admissible range, the local arc at a residual that is at
least zero differs from the double sum of the ordered character pair
contribution by no more than the stated logarithm of the modulus, the residual
coming only from the primes dividing the modulus and the finite integral
rearrangement. -/
theorem character_square_expansion_nonneg491 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        ∀ n : ℤ, 0 ≤ n →
          ‖localArc1622 N q n -
              (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
                characterPair491 N q n χ ψ)‖ ≤
            C * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := by
  sorry

/-- LEAF. Finite character square expansion at a negative residual. The same
expansion as at a nonnegative residual, with the reduced residue phase replaced
by its conjugate, which changes no norm; the primes dividing the modulus and the
finite integral rearrangement are again the whole residual. -/
theorem character_square_expansion_neg491 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        ∀ n : ℤ, n < 0 →
          ‖localArc1622 N q n -
              (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
                characterPair491 N q n χ ψ)‖ ≤
            C * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := by
  sorry

/-- LEAF. Exact separation of the finite character square. The double sum over
all ordered character pairs is the principal pair, that is the reduced residue
phase against the square of the principal prime series, plus the two mixed
blocks with exactly one principal character plus the block with both characters
nonprincipal. This is a finite rearrangement of the same sum with no error. -/
theorem character_square_matching491 (N q : ℕ) [NeZero q] (n : ℤ) :
    (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
        characterPair491 N q n χ ψ) =
      principalTerm491 N q n + mixedTerm491 N q n + nonprincipalTerm491 N q n := by
  classical
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set S := univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1) with hS
  have hsingle : (univ.filter (fun χ : DirichletCharacter ℂ q => χ = 1)) = {1} := by
    ext x
    simp
  have hsplit (f : DirichletCharacter ℂ q → ℂ) :
      (∑ χ : DirichletCharacter ℂ q, f χ) = f 1 + ∑ χ ∈ S, f χ := by
    have h := Finset.sum_filter_add_sum_filter_not
      (s := (univ : Finset (DirichletCharacter ℂ q)))
      (p := fun χ : DirichletCharacter ℂ q => χ = 1) (f := f)
    rw [hsingle, Finset.sum_singleton] at h
    rw [← h]
  rw [hsplit (fun χ => ∑ ψ : DirichletCharacter ℂ q, characterPair491 N q n χ ψ)]
  rw [hsplit (fun ψ => characterPair491 N q n 1 ψ)]
  rw [Finset.sum_congr rfl (fun χ (_ : χ ∈ S) => hsplit (fun ψ => characterPair491 N q n χ ψ))]
  rw [pair_one_one491 N q hq n]
  unfold mixedTerm491 nonprincipalTerm491
  simp only [hS, Finset.sum_add_distrib]
  abel

/-- The three character term decomposition, assembled from the finite character
square expansion at each residual sign and from the exact separation of that
square. -/
theorem character_decomposition491_split :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        letI : NeZero q := ⟨by omega⟩
        ∀ n : ℤ, ‖localArc1622 N q n -
          (principalTerm491 N q n + mixedTerm491 N q n + nonprincipalTerm491 N q n)‖ ≤
          C * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := by
  obtain ⟨C1, hC1, N1, h1⟩ := character_square_expansion_nonneg491
  obtain ⟨C2, hC2, N2, h2⟩ := character_square_expansion_neg491
  refine ⟨max C1 C2, lt_of_lt_of_le hC1 (le_max_left _ _), max N1 N2, ?_⟩
  intro N hN q hq hqQ
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) hN
    exact_mod_cast h
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hx : 0 ≤ (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) :=
    div_nonneg (mul_nonneg (by positivity) hlogq) (Real.rpow_pos_of_pos hNpos _).le
  letI : NeZero q := ⟨by omega⟩
  intro n
  rcases lt_or_ge n 0 with hn | hn
  · have h := h2 N hN2 q hq hqQ n hn
    calc ‖localArc1622 N q n -
          (principalTerm491 N q n + mixedTerm491 N q n + nonprincipalTerm491 N q n)‖
        = ‖localArc1622 N q n -
            (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
              characterPair491 N q n χ ψ)‖ := by
          rw [character_square_matching491 N q n]
      _ ≤ C2 * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := h
      _ = C2 * ((N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ)) := by ring
      _ ≤ max C1 C2 * ((N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hx
      _ = max C1 C2 * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := by ring
  · have h := h1 N hN1 q hq hqQ n hn
    calc ‖localArc1622 N q n -
          (principalTerm491 N q n + mixedTerm491 N q n + nonprincipalTerm491 N q n)‖
        = ‖localArc1622 N q n -
            (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
              characterPair491 N q n χ ψ)‖ := by
          rw [character_square_matching491 N q n]
      _ ≤ C1 * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := h
      _ = C1 * ((N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ)) := by ring
      _ ≤ max C1 C2 * ((N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hx
      _ = max C1 C2 * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := by ring

end LeanLab.Linnik1951
