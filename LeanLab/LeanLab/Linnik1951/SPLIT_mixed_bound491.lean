/-
Split of mixed_bound491 into four leaves. The mixed character term of equation
3.4 is cut into the count of nonprincipal characters at one modulus, the
principal conjugate Gauss coefficient, the mixed character mass over the local
window at the sixth power of the logarithm, and the estimate for one ordered
character pair. The assembly at the end has no sorry and does not use the split
statement.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp491b

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- LEAF. Counting step of equation 5.5. The number of nonprincipal characters
at a positive modulus is at most the totient of that modulus. At modulus one the
filtered set is empty, so the bound reads zero at most one. No estimate on the
characters themselves and no integral occurs here. -/
theorem mixed_card491 (q : ℕ) [NeZero q] :
    (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card ≤ q.totient := by
  classical
  have hle : (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card ≤
      (univ : Finset (DirichletCharacter ℂ q)).card := Finset.card_filter_le _ _
  rw [Finset.card_univ] at hle
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  omega

/-- LEAF. Modulus step of equation 5.5. The conjugate Gauss coefficient of the
principal character at a positive modulus is the Moebius value at the modulus in
absolute value, hence has norm at most one. It carries no frequency, no size of
N, and no character other than the principal one. -/
theorem mixed_principal_gauss491 (q : ℕ) (hq : 1 ≤ q) :
    ‖conjugateGauss491 q (1 : DirichletCharacter ℂ q)‖ ≤ 1 := by
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
  rw [hone, norm_star, signedRamanujan_toNat491 q 1 (by norm_num)]
  have hto : (Int.toNat 1 : ℕ) = 1 := rfl
  rw [hto,
    LeanLab.Perelli1996.Ramanujan103.ramanujanSum_coprime q 1 (by omega)
      (Nat.coprime_one_right q)]
  have hmu : ((|ArithmeticFunction.moebius q| : ℤ) : ℝ) ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
  calc ‖((ArithmeticFunction.moebius q : ℤ) : ℂ)‖
      = |((ArithmeticFunction.moebius q : ℤ) : ℝ)| := Complex.norm_intCast _
    _ = ((|ArithmeticFunction.moebius q| : ℤ) : ℝ) := by rw [Int.cast_abs]
    _ ≤ 1 := hmu

/-- LEAF. Mass step of equation 5.5. The mixed character mass of one
nonprincipal character: the integral of the principal character prime series
against the nonprincipal one over the local window is at most the scale N times
the sixth power of the logarithm of N over the square root of q times tau. This
is the sixth power form of the mixed mass and it carries no conjugate Gauss
coefficient, no residue sum and no outer character sum. -/
theorem mixed_mass491 (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖characterPrime280 (1 : DirichletCharacter ℂ q) N α‖ *
              ‖characterPrime280 χ N α‖) ≤
            C * (N : ℝ) * Real.log N ^ 6 /
              Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- LEAF. Pair step of equation 5.5. One nonprincipal character contributes, in
its two orders with the principal character, at most the scale N times the sixth
power of the logarithm of N divided by the totient of q and by the square root of
q times tau. This is the per character form of the displayed mixed bound; it
carries the two conjugate Gauss coefficients, the residue sum and the two
integrals. -/
theorem mixed_pair_bound491 (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        ∀ n : ℤ, ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖ ≤
            C * (N : ℝ) * Real.log N ^ 6 /
              ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- The four leaves together give the mixed character estimate of equation 5.5:
the term is a sum over the nonprincipal characters of pairs of ordered character
pairs, so the triangle inequality, the count of those characters and the per
character estimate give the displayed bound. -/
theorem mixed_bound491_split (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        letI : NeZero q := ⟨by omega⟩
        ∀ n : ℤ, ‖mixedTerm491 N q n‖ ≤
          C * (N : ℝ) * Real.log N ^ 6 /
            Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  obtain ⟨C, hC, N0, hle⟩ := mixed_pair_bound491 hM
  refine ⟨2 * C, by positivity, N0, ?_⟩
  intro N hN q hq hqQ
  classical
  letI : NeZero q := ⟨by omega⟩
  intro n
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hτpos : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hRpos : (0 : ℝ) < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hstep : ∀ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
      ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖ ≤
        C * (N : ℝ) * Real.log N ^ 6 /
          ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    intro χ hχ
    exact hle N hN q hq hqQ n χ (by simpa using hχ)
  have hcard : (((univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℕ) : ℝ) ≤
      (q.totient : ℝ) := by
    exact_mod_cast mixed_card491 q
  have hBnn : (0 : ℝ) ≤ C * (N : ℝ) * Real.log N ^ 6 /
      ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    apply div_nonneg
    · positivity
    · positivity
  have hnorm : ‖mixedTerm491 N q n‖ ≤
      ∑ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
        ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖ := by
    simp only [mixedTerm491]
    exact norm_sum_le _ _
  have hfirst : ∑ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
        ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖ ≤
      ((univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) *
        (C * (N : ℝ) * Real.log N ^ 6 /
          ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have harith : (q.totient : ℝ) * (C * (N : ℝ) * Real.log N ^ 6 /
      ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) =
      C * (N : ℝ) * Real.log N ^ 6 /
        Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    have hs : Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≠ 0 :=
      (Real.sqrt_pos.mpr hRpos).ne'
    field_simp [hφpos.ne', hs]
  have hright : (0 : ℝ) ≤ C * (N : ℝ) * Real.log N ^ 6 /
      Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    apply div_nonneg
    · positivity
    · exact (Real.sqrt_pos.mpr hRpos).le
  calc ‖mixedTerm491 N q n‖
      ≤ ∑ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
          ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖ := hnorm
    _ ≤ ((univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) *
          (C * (N : ℝ) * Real.log N ^ 6 /
            ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := hfirst
    _ ≤ (q.totient : ℝ) * (C * (N : ℝ) * Real.log N ^ 6 /
          ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) :=
        mul_le_mul_of_nonneg_right hcard hBnn
    _ = C * (N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := harith
    _ ≤ 2 * C * (N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
        have heq : 2 * C * (N : ℝ) * Real.log N ^ 6 /
              Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) =
            2 * (C * (N : ℝ) * Real.log N ^ 6 /
              Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring
        rw [heq]
        linarith

end LeanLab.Linnik1951
