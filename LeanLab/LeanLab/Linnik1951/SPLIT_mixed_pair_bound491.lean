/-
Split of mixed_pair_bound491 into four leaves. The ordered pair estimate of
equation 5.5 is cut into the reduction of the character pair to its coefficient
times the unsigned mixed mass, the pointwise size of the Gauss coefficient
against the totient, the pointwise size of the residue phase against the
totient, and the single per character mixed mass estimate at the totient scale.
The assembly at the end has no sorry and does not use the split statement.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_mixed_bound491

namespace LeanLab.Linnik1951

open Finset MeasureTheory
open Filter
open scoped Topology

/-- LEAF. Reduction step of equation 5.5. The two ordered pairs of one
nonprincipal character with the principal character are equal, so the ordered
pair under the norm is at most twice the single ordered pair, and that single
order is at most its coefficient, the conjugate Gauss coefficient of the
character times its residue phase divided by the square of the totient, times
the unsigned mixed mass over the local window. No size of the mass, no power of
`N` and no logarithm is asserted here. -/
theorem mixed_pair_reduction491 (N q : ℕ) (n : ℤ) (χ : DirichletCharacter ℂ q)
    (hq : 1 ≤ q) (hN : 1 ≤ N) :
    ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖ ≤
      2 * (‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ /
          (q.totient : ℝ) ^ 2) *
        (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ *
            ‖characterPrime280 χ N z‖) := by
  have hsum : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      (1 : DirichletCharacter ℂ q) a * χ a * Complex.exp
        (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) =
      residuePhase555 q n χ := by
    unfold residuePhase555
    apply Finset.sum_congr rfl
    intro a ha
    have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
    have hunit : IsUnit ((a : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr hcop
    rw [MulChar.one_apply hunit, one_mul]
  have hsum' : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      χ a * (1 : DirichletCharacter ℂ q) a * Complex.exp
        (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) =
      residuePhase555 q n χ := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hint : (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      characterPrime280 χ N z * characterPrime280 (1 : DirichletCharacter ℂ q) N z *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      characterPrime280 (1 : DirichletCharacter ℂ q) N z * characterPrime280 χ N z *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro z _
    simp only
    ring
  have hsymm : characterPair491 N q n χ 1 = characterPair491 N q n 1 χ := by
    unfold characterPair491
    rw [hsum, hsum', hint]
    ring
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hw : (0 : ℝ) < 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
  have hab : -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
      1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by linarith
  have hI : ‖∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      characterPrime280 (1 : DirichletCharacter ℂ q) N z * characterPrime280 χ N z *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
      ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ *
        ‖characterPrime280 χ N z‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans_eq ?_
    apply intervalIntegral.integral_congr
    intro z _
    simp only
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hG1 := mixed_principal_gauss491 q hq
  have hφ : ‖(1 : ℂ) / (q.totient : ℂ) ^ 2‖ = 1 / (q.totient : ℝ) ^ 2 := by
    rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
  rw [hsymm, ← two_mul, norm_mul]
  unfold characterPair491
  rw [hsum, norm_mul, norm_mul, norm_mul, norm_mul, hφ]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  set J : ℝ := ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
      (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ *
        ‖characterPrime280 χ N z‖ with hJ
  set I0 : ℂ := ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
      (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      characterPrime280 (1 : DirichletCharacter ℂ q) N z * characterPrime280 χ N z *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) with hI0
  have hK : (0 : ℝ) ≤ ‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ /
      (q.totient : ℝ) ^ 2 := by positivity
  have hprod : ‖conjugateGauss491 q (1 : DirichletCharacter ℂ q)‖ * ‖I0‖ ≤ 1 * J :=
    mul_le_mul hG1 hI (norm_nonneg _) zero_le_one
  calc 2 * (1 / (q.totient : ℝ) ^ 2 *
          ‖conjugateGauss491 q (1 : DirichletCharacter ℂ q)‖ *
          ‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ * ‖I0‖)
      = 2 * (‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ /
          (q.totient : ℝ) ^ 2) *
          (‖conjugateGauss491 q (1 : DirichletCharacter ℂ q)‖ * ‖I0‖) := by ring
    _ ≤ 2 * (‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ /
          (q.totient : ℝ) ^ 2) * (1 * J) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by ring

/-- LEAF. Coefficient step of equation 5.5, Gauss half. The conjugate Gauss
coefficient of any character at a modulus is at most four times the totient of
that modulus: the Gauss sum has square at most the modulus, and the totient of a
positive modulus is at least a quarter of the square root of the modulus. This
is a bound in the modulus alone, with no frequency, no `N` and no logarithm. -/
theorem gauss_coeff_le_totient491 (q : ℕ) (χ : DirichletCharacter ℂ q) :
    ‖conjugateGauss491 q χ‖ ≤ 4 * (q.totient : ℝ) := by
  have hcard : ((range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    exact congrArg Finset.card (Finset.filter_congr fun a _ => Nat.coprime_comm)
  have h : ‖conjugateGauss491 q χ‖ ≤ (q.totient : ℝ) := by
    unfold conjugateGauss491
    rw [norm_star]
    refine (norm_sum_le _ _).trans ?_
    have hle := Finset.sum_le_card_nsmul ((range q).filter (fun a => Nat.Coprime a q))
      (fun a : ℕ => ‖χ a * Complex.exp
        (((2 * Real.pi * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)‖) (1 : ℝ)
      (fun a _ => by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
        exact DirichletCharacter.norm_le_one χ _)
    rw [hcard, nsmul_eq_mul, mul_one] at hle
    exact hle
  have h0 : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  linarith

/-- LEAF. Coefficient step of equation 5.5, phase half. The residue phase of any
character at a positive modulus is at most the totient of that modulus, since it
is a sum of totient many terms of modulus at most one. This is the trivial size
bound of the phase; it carries no frequency dependence beyond the fixed
frequency and no `N`. -/
theorem residue_phase_le_totient491 (q : ℕ) (n : ℤ) (χ : DirichletCharacter ℂ q) :
    ‖residuePhase555 q n χ‖ ≤ (q.totient : ℝ) := by
  have hcard : ((range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    exact congrArg Finset.card (Finset.filter_congr fun a _ => Nat.coprime_comm)
  unfold residuePhase555
  refine (norm_sum_le _ _).trans ?_
  have hle := Finset.sum_le_card_nsmul ((range q).filter (fun a => Nat.Coprime a q))
    (fun a : ℕ => ‖χ a * Complex.exp
      (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)‖) (1 : ℝ)
    (fun a _ => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact DirichletCharacter.norm_le_one χ _)
  rw [hcard, nsmul_eq_mul, mul_one] at hle
  exact hle

/-- LEAF. Mass step of equation 5.5 at the totient scale. For every nonprincipal
character the unsigned mixed mass of the principal character series against that
character series over the local window is at most the scale `N` times the sixth
power of the logarithm of `N`, divided by the totient of `q` and by the square
root of `q` times `N` to the one seventh. This is the single mass estimate: it
carries neither the conjugate Gauss coefficients nor the residue phase. -/
theorem mixed_mass_totient491 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ *
              ‖characterPrime280 χ N z‖) ≤
            C * (N : ℝ) * Real.log N ^ 6 /
              ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- The four leaves together give the per character ordered pair estimate of
equation 5.5: the reduction removes the phases, the two pointwise coefficient
leaves bound the Gauss coefficient and the residue phase by the totient, and the
mass leaf supplies the totient scale, so the pair is at most eight times that
mass. -/
theorem mixed_pair_bound491_split (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        ∀ n : ℤ, ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖ ≤
            C * (N : ℝ) * Real.log N ^ 6 /
              ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C, hC, N0, hmass⟩ := mixed_mass_totient491
  refine ⟨8 * C, by positivity, max N0 1, ?_⟩
  intro N hN q hq hqQ n χ hχ
  have hN0 : N0 < N := by
    have h : N0 ≤ max N0 1 := le_max_left _ _
    omega
  have hN1 : 1 ≤ N := by
    have h : 1 ≤ max N0 1 := le_max_right _ _
    omega
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    have hq0 : 0 < q := by omega
    exact_mod_cast Nat.totient_pos.mpr hq0
  set I : ℝ := ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
      (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ *
        ‖characterPrime280 χ N z‖ with hIdef
  have hI0 : 0 ≤ I := by
    rw [hIdef]
    exact intervalIntegral.integral_nonneg (by
      have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
      have hpos : (0 : ℝ) < 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
      linarith) (fun z _ => by positivity)
  have hred := mixed_pair_reduction491 N q n χ hq hN1
  rw [← hIdef] at hred
  have hI := hmass N hN0 q hq hqQ χ hχ
  rw [← hIdef] at hI
  have hG := gauss_coeff_le_totient491 q χ
  have hph := residue_phase_le_totient491 q n χ
  have hcoef : ‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ /
      (q.totient : ℝ) ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : ‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ ≤
        (4 * (q.totient : ℝ)) * (q.totient : ℝ) :=
      mul_le_mul hG hph (norm_nonneg _) (by positivity)
    calc ‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖
        ≤ (4 * (q.totient : ℝ)) * (q.totient : ℝ) := h1
      _ = 4 * (q.totient : ℝ) ^ 2 := by ring
  have hstep : 2 * (‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ /
      (q.totient : ℝ) ^ 2) * I ≤ 8 * I := by
    have h2 : (‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ /
        (q.totient : ℝ) ^ 2) * I ≤ 4 * I := mul_le_mul_of_nonneg_right hcoef hI0
    nlinarith [h2]
  refine hred.trans (hstep.trans ?_)
  have h8 : 8 * I ≤ 8 * (C * (N : ℝ) * Real.log N ^ 6 /
      ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by
    linarith
  exact h8.trans_eq (by ring)

end LeanLab.Linnik1951
