/-
Repaired split of mixed_pair_bound491 of Linnik1951/SPLIT_mixed_bound491, P0093 page 160
equation 5.5, with the q over phi of q factor of audit P1122-0033 absorbed.

The split on main, SPLIT_mixed_pair_bound491, bounds the conjugate Gauss coefficient and
the residue phase each by a multiple of the totient and pushes the whole saving of one
over the totient into the mixed mass leaf mixed_mass_totient491. That leaf has no
hypothesis and asks more than Cauchy Schwarz with MellinBound280 gives; see the audit
note of burst 20261122 feed1122.

This file keeps the proved reduction mixed_pair_reduction491 and cuts the rest along the
printed argument of 5.5:
* the product of the conjugate Gauss coefficient and the residue phase is at most q, the
  Gauss sum bound for a character with its primitive part, HARD;
* the mean square of the principal series over the arc is at most a constant times N over
  log squared N, the Gallagher inequality with the Brun Titchmarsh bound, HARD;
* the mixed mass is at most the geometric mean of the two mean squares, Cauchy Schwarz on
  the arc, PROVED here;
* q over the totient of q is at most a constant times the square root of log N for q up to
  N to the 1/10, an elementary bound since q over phi of q grows like log log q, MEDIUM.
MellinBound280, the hypothesis of the target, supplies the mean square of the
nonprincipal series. The half power of log N saved by the true principal mass absorbs the
factor q over phi of q, which is how the printed ln^6 display survives.

The assembly mixed_pair_bound491_repair has exactly the statement of mixed_pair_bound491
and is free of admitted steps. No statement on main is changed.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_mixed_pair_bound491
import LeanLab.Linnik1951.SPLIT_gauss_phase491
import LeanLab.Linnik1951.TotientRatioS128

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- LEAF: P0093 page 160, the Gauss sum factor of equation 5.5. HARD. For every
character mod a positive q and every integer n, the conjugate Gauss coefficient times
the residue phase at n has modulus at most q. Through the primitive character inducing
the character, the Gauss coefficient is at most the square root of the conductor and the
residue phase is at most the square root of the conductor times the Ramanujan factor of
the cofactor, whose size is at most the cofactor. -/
theorem gauss_phase_product_le491 (q : ℕ) (hq : 1 ≤ q) (n : ℤ) (χ : DirichletCharacter ℂ q) :
    ‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ ≤ (q : ℝ) := by
  have hg := gauss_coefficient_le_sqrt_conductor491 q hq χ
  have hr := residue_phase_mul_sqrt_conductor_le491 q hq n χ
  calc ‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖
      ≤ Real.sqrt (χ.conductor : ℝ) * ‖residuePhase555 q n χ‖ :=
        mul_le_mul_of_nonneg_right hg (norm_nonneg _)
    _ = ‖residuePhase555 q n χ‖ * Real.sqrt (χ.conductor : ℝ) := mul_comm _ _
    _ ≤ (q : ℝ) := hr

/-- LEAF: P0093 page 160, the principal mass in equation 5.5. HARD. The mean square of
the principal character prime series over the arc of radius one over q times N to the
one seventh is at most a constant times N over log squared N, uniformly in q up to N to
the one tenth. By the Gallagher inequality the mean square is at most the arc radius squared
times the integral of the squared prime counts in intervals of length about q times N to
the one seventh with the exponential damping, and Brun Titchmarsh bounds each count by
that length over its logarithm. -/
theorem principal_arc_mass491 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) ≤
          C * (N : ℝ) / Real.log N ^ 2 := by
  sorry

/-- Cauchy Schwarz for interval integrals of continuous real functions, by the
nonnegativity of the integral of the square of f minus t g for every real t. -/
theorem interval_cauchy_schwarz491 (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, f x * g x) ^ 2 ≤ (∫ x in a..b, f x ^ 2) * (∫ x in a..b, g x ^ 2) := by
  set A := ∫ x in a..b, f x ^ 2
  set B := ∫ x in a..b, f x * g x
  set C := ∫ x in a..b, g x ^ 2
  have key : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C := by
    intro t
    have h0 : 0 ≤ ∫ x in a..b, (f x - t * g x) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
    have hexp : (∫ x in a..b, (f x - t * g x) ^ 2) = A - 2 * t * B + t ^ 2 * C := by
      have e : (fun x => (f x - t * g x) ^ 2) =
          fun x => (f x ^ 2 - (2 * t) * (f x * g x)) + t ^ 2 * g x ^ 2 := by
        funext x; ring
      rw [e, intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      · exact (hf.pow 2).intervalIntegrable _ _
      · exact (continuous_const.mul (hf.mul hg)).intervalIntegrable _ _
      · exact ((hf.pow 2).sub (continuous_const.mul (hf.mul hg))).intervalIntegrable _ _
      · exact (continuous_const.mul (hg.pow 2)).intervalIntegrable _ _
    linarith
  have hC0 : 0 ≤ C := intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
  rcases hC0.lt_or_eq with hC | hC
  · have h := key (B / C)
    have : A - 2 * (B / C) * B + (B / C) ^ 2 * C = A - B ^ 2 / C := by field_simp; ring
    rw [this] at h
    have : B ^ 2 / C ≤ A := by linarith
    rw [div_le_iff₀ hC] at this
    linarith
  · rw [← hC] at key ⊢
    have hB : B = 0 := by
      by_contra hB
      have h := key ((A + 1) / (2 * B))
      have : A - 2 * ((A + 1) / (2 * B)) * B + ((A + 1) / (2 * B)) ^ 2 * 0 = -1 := by
        field_simp; ring
      linarith
    rw [hB]; simp

/-- P0093 page 160, the Cauchy Schwarz step of equation 5.5, PROVED here, formerly a MEDIUM
leaf of this file. On the arc
the mixed mass of the principal series against a character series is at most the
square root of the product of the two mean squares. Both series are continuous for N at
least one, by continuous_character_prime357. -/
theorem mixed_mass_cauchy_schwarz491 (N q : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q)
    (χ : DirichletCharacter ℂ q) :
    (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ *
        ‖characterPrime280 χ N z‖) ^ 2 ≤
      (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) *
      (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        ‖characterPrime280 χ N z‖ ^ 2) := by
  have hle : -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    have hq' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have : 0 < 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
    linarith
  exact interval_cauchy_schwarz491 _ _
    (continuous_character_prime357 (1 : DirichletCharacter ℂ q) N hN).norm
    (continuous_character_prime357 χ N hN).norm _ _ hle

/-- LEAF: audit P1122-0033 of the factor q over phi of q in equation 5.5. MEDIUM. For q
up to N to the one tenth, q is at most a constant times the totient of q times the square
root of log N. The ratio q over phi of q is the product of p over p minus one over the
primes dividing q, which is at most a constant times log log q, and log log q is far
below the square root of log N. -/
theorem modulus_over_totient491 :
    ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        (q : ℝ) ≤ D * (q.totient : ℝ) * Real.sqrt (Real.log N) :=
  TotientRatioS128.modulus_over_totient_S128

set_option maxHeartbeats 1000000 in
/-- Assembly: the exact statement of mixed_pair_bound491 from the reduction
mixed_pair_reduction491, the four leaves above and MellinBound280. -/
theorem mixed_pair_bound491_repair (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        ∀ n : ℤ, ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖ ≤
            C * (N : ℝ) * Real.log N ^ 6 /
              ((q.totient : ℝ) * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨B, hB, NB, hMB⟩ := hM
  obtain ⟨C1, hC1, N1, hP⟩ := principal_arc_mass491
  obtain ⟨D, hD, N2, hQ⟩ := modulus_over_totient491
  refine ⟨2 * D * Real.sqrt (C1 * B), by positivity, max (max NB N1) (max N2 3), ?_⟩
  intro N hN q hq hqQ n χ hχ
  have hNB : NB < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : N1 < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : 3 < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNr : (3 : ℝ) < (N : ℝ) := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog : (1 : ℝ) < Real.log N := by
    rw [Real.lt_log_iff_exp_lt hNpos]
    have := Real.exp_one_lt_d9
    linarith
  have hqr : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hφ : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hτ : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hR : (0 : ℝ) < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hq7 : (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
    le_trans hqQ (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  set I : ℝ := ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
      (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ *
        ‖characterPrime280 χ N z‖ with hIdef
  set P : ℝ := ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
      (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 with hPdef
  set X : ℝ := ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
      (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      ‖characterPrime280 χ N z‖ ^ 2 with hXdef
  have hle : -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    have : 0 < 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
    linarith
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hle (fun z _ => by positivity)
  have hP0 : 0 ≤ P := intervalIntegral.integral_nonneg hle (fun z _ => by positivity)
  have hX0 : 0 ≤ X := intervalIntegral.integral_nonneg hle (fun z _ => by positivity)
  have hred := mixed_pair_reduction491 N q n χ hq (by omega)
  rw [← hIdef] at hred
  have hGP := gauss_phase_product_le491 q hq n χ
  have hCS : I ^ 2 ≤ P * X := mixed_mass_cauchy_schwarz491 N q (by omega) hq χ
  have hPb : P ≤ C1 * (N : ℝ) / Real.log N ^ 2 := hP N hN1 q hq hqQ
  have hXb : X ≤ B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 :=
    hMB N hNB q hq hq7 χ hχ
  have hqD : (q : ℝ) ≤ D * (q.totient : ℝ) * Real.sqrt (Real.log N) := hQ N hN2 q hq hqQ
  -- notation for the scale
  set L : ℝ := Real.log N with hL
  set R : ℝ := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) with hRdef
  set φ : ℝ := (q.totient : ℝ) with hφdef
  have hL0 : 0 < L := by linarith
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hsL : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hsR2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hsCB : Real.sqrt (C1 * B) ^ 2 = C1 * B := Real.sq_sqrt (by positivity)
  -- bound I squared
  have hPX : P * X ≤ (C1 * (N : ℝ) / L ^ 2) * (B * (N : ℝ) / R * L ^ 13) :=
    mul_le_mul hPb hXb hX0 (by positivity)
  have hI2 : I ^ 2 ≤ C1 * B * (N : ℝ) ^ 2 * L ^ 11 / R := by
    have e : (C1 * (N : ℝ) / L ^ 2) * (B * (N : ℝ) / R * L ^ 13) =
        C1 * B * (N : ℝ) ^ 2 * L ^ 11 / R := by
      field_simp
    linarith [hCS, hPX, e.le, e.ge]
  -- the target scale
  set T : ℝ := 2 * D * Real.sqrt (C1 * B) * (N : ℝ) * L ^ 6 / (φ * Real.sqrt R) with hT
  have hT0 : 0 ≤ T := by positivity
  have hcoef0 : 0 ≤ ‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ / φ ^ 2 := by positivity
  have hstep1 : 2 * (‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ / φ ^ 2) * I ≤
      2 * ((q : ℝ) / φ ^ 2) * I := by
    have : ‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ / φ ^ 2 ≤ (q : ℝ) / φ ^ 2 :=
      div_le_div_of_nonneg_right hGP (by positivity)
    nlinarith
  have hstep2 : 2 * ((q : ℝ) / φ ^ 2) * I ≤ T := by
    have hlhs0 : 0 ≤ 2 * ((q : ℝ) / φ ^ 2) * I := by positivity
    rw [← abs_of_nonneg hlhs0, ← abs_of_nonneg hT0]
    apply sq_le_sq.mp
    have hq2 : (q : ℝ) ^ 2 ≤ D ^ 2 * φ ^ 2 * L := by
      have h0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
      have := mul_self_le_mul_self h0 hqD
      nlinarith [hsL]
    have eT : T ^ 2 = 4 * D ^ 2 * (C1 * B) * (N : ℝ) ^ 2 * L ^ 12 / (φ ^ 2 * R) := by
      rw [hT, div_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, hsCB, hsR2]
      ring
    have eL : (2 * ((q : ℝ) / φ ^ 2) * I) ^ 2 = 4 * (q : ℝ) ^ 2 * I ^ 2 / φ ^ 4 := by
      rw [mul_pow, mul_pow, div_pow]; ring
    rw [eL, eT]
    have hφ4 : 0 < φ ^ 4 := by positivity
    rw [div_le_div_iff₀ hφ4 (by positivity)]
    have hA : 4 * (q : ℝ) ^ 2 * I ^ 2 ≤ 4 * (D ^ 2 * φ ^ 2 * L) * (C1 * B * (N : ℝ) ^ 2 * L ^ 11 / R) :=
      mul_le_mul (by linarith [hq2]) hI2 (sq_nonneg _) (by positivity)
    have e2 : 4 * (D ^ 2 * φ ^ 2 * L) * (C1 * B * (N : ℝ) ^ 2 * L ^ 11 / R) * (φ ^ 2 * R) =
        4 * D ^ 2 * (C1 * B) * (N : ℝ) ^ 2 * L ^ 12 * φ ^ 4 := by
      field_simp
    have hB2 : 0 ≤ φ ^ 2 * R := by positivity
    have hA' := mul_le_mul_of_nonneg_right hA hB2
    rw [e2] at hA'
    linarith
  calc ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖
      ≤ 2 * (‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ / φ ^ 2) * I := hred
    _ ≤ 2 * ((q : ℝ) / φ ^ 2) * I := hstep1
    _ ≤ T := hstep2

end LeanLab.Linnik1951

#print axioms LeanLab.Linnik1951.mixed_pair_bound491_repair
#print axioms LeanLab.Linnik1951.interval_cauchy_schwarz491
#print axioms LeanLab.Linnik1951.mixed_mass_cauchy_schwarz491
