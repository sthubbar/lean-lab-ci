/-
P0093 pages 155, 159 and 160 equations 2.3, 5.2 and 5.5.
Reuse the exact character coefficient energy of Decomp555a.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Base520a
import LeanLab.Linnik1951.ResidueData696
import LeanLab.Linnik1951.SquareSupply696
import LeanLab.Linnik1951.Burst1122GrhTransfer519
import LeanLab.Linnik1951.SPLIT_mixed_bound491
import LeanLab.Linnik1951.SPLIT_character_decomposition491
import Batteries.Tactic.OpenPrivate

namespace LeanLab.Linnik1951
open Finset MeasureTheory

open private Gunit_eq_mul sum_Gunit_mul_char from LeanLab.Linnik1951.Decomp519a
open private summable_prime_damp491 norm_twist_le491 summable_twist491
  tsum_prime_damp_le491 from LeanLab.Linnik1951.SPLIT_character_decomposition491

/-- P0093 page 159 equation 5.2. The proved GRH transfer supplies the
existing local character square hypothesis, at radius one over q tau. -/
theorem mellin_bound696 (hG : LeanLab.DERZ1997.GRH) : MellinBound280 := by
  obtain ⟨C, hC, N0, hm⟩ := Task519.nonprincipal_mass519_b1122 hG
    (Task519.grh_mellin_transfer519_b1122 hG)
  refine ⟨C, hC, max N0 1, ?_⟩
  intro N hN q hq hqN χ hχ
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hτ1 : 1 ≤ (N : ℝ) ^ (1 / 7 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hR1 : 1 ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by nlinarith
  have hR2 : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 7 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  convert hm N (by omega) q hq hqN χ hχ _ hR1 hR2 using 1 <;> first | rfl | ring

/-- P0093 page 155 equation 2.3. The principal character series is the
prime series with the prime divisors of its modulus removed. -/
theorem principal_character696 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (z : ℝ) :
    principalPrime520 N q z = characterPrime280 (1 : DirichletCharacter ℂ q) N z := by
  rw [← class_principal1121 N q hN z]
  have hG : ∀ b : ZMod q, ¬ IsUnit b → classSeries1121 N q z b = 0 := by
    intro b hb
    simp [classSeries1121, hb]
  rw [← principal_character_sum552 q _ hG, class_character1121 N q hN z]
  rfl

/-- P0093 page 155 equation 2.3. The unit Gauss coefficient in the
finite character inversion is the conjugate reduced residue Gauss sum. -/
theorem unit_gauss_coefficient696 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∑ b ∈ (univ : Finset (ZMod q)).filter IsUnit,
      ZMod.stdAddChar (-((1 : ZMod q) * b)) * (starRingEnd ℂ) (χ b)) =
        conjugateGauss491 q χ := by
  classical
  rw [sum_filter, LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range]
  unfold conjugateGauss491
  rw [star_sum]
  simp only [ZMod.isUnit_iff_coprime]
  rw [← sum_filter]
  apply sum_congr rfl
  intro b hb
  have hp := negative_unit_phase470 q 1 b
  simp only [Nat.cast_one, one_mul, mul_one] at hp
  simp only [one_mul]
  rw [hp]
  change _ = (starRingEnd ℂ) (χ (b : ZMod q) *
    Complex.exp (((2 * Real.pi * ((b : ℝ) / q) : ℝ) : ℂ) * Complex.I))
  rw [map_mul, ← Complex.exp_conj]
  simp only [Nat.cast_one, one_div, one_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

/-- P0093 pages 155 and 156 equations 2.3 and 3.4. The residue error is
the nonprincipal character expansion plus its exact prime divisor remainder. -/
theorem residue_character_linear696 (N q : ℕ) [NeZero q] (hN : 1 ≤ N)
    (a : ℕ) (ha : Nat.Coprime a q) (z : ℝ) :
    residueError520 N q a z =
      (1 / (q.totient : ℂ)) *
        (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          χ a * conjugateGauss491 q χ * characterPrime280 χ N z) +
        divisorPart1121 N q a z := by
  classical
  let G : ZMod q → ℂ := classSeries1121 N q z
  let H := fun χ : DirichletCharacter ℂ q =>
    ∑ b ∈ (univ : Finset (ZMod q)).filter IsUnit,
      ZMod.stdAddChar (-((a : ZMod q) * b)) * (starRingEnd ℂ) (χ b)
  have hG (b : ZMod q) (hb : ¬ IsUnit b) : G b = 0 := by
    simp [G, classSeries1121, hb]
  have hinv :
      (∑ χ : DirichletCharacter ℂ q, H χ * ∑ b : ZMod q, χ b * G b) =
        (q.totient : ℂ) * ∑ b : ZMod q, ZMod.stdAddChar (-((a : ZMod q) * b)) * G b := by
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro b _
    simp_rw [← mul_assoc, ← sum_mul]
    by_cases hb : IsUnit b
    · rw [show (∑ χ : DirichletCharacter ℂ q, H χ * χ b) =
        (q.totient : ℂ) * ZMod.stdAddChar (-((a : ZMod q) * b)) from
          sum_Gunit_mul_char _ _ hb]
    · simp [hG b hb]
  have hH (χ : DirichletCharacter ℂ q) : H χ = χ a * conjugateGauss491 q χ := by
    dsimp [H]
    rw [Gunit_eq_mul χ ((ZMod.isUnit_iff_coprime a q).mpr ha),
      unit_gauss_coefficient696]
  simp_rw [hH, show ∀ χ : DirichletCharacter ℂ q,
    (∑ b : ZMod q, χ b * G b) = characterPrime280 χ N z from
      fun χ => class_character1121 N q hN z χ] at hinv
  have hphase : (∑ b : ZMod q, ZMod.stdAddChar (-((a : ZMod q) * b)) * G b) =
      primeFourier111_up111 N ((a : ℝ) / q + z) - divisorPart1121 N q a z := by
    simp_rw [mul_comm (a : ZMod q)]
    exact class_transform1121 N q hN z a ha
  rw [hphase] at hinv
  have hsplit := add_sum_erase (univ : Finset (DirichletCharacter ℂ q))
    (fun χ => χ a * conjugateGauss491 q χ * characterPrime280 χ N z)
    (mem_univ (1 : DirichletCharacter ℂ q))
  have herase : (univ : Finset (DirichletCharacter ℂ q)).erase 1 =
      univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1) := by ext χ; simp
  rw [herase, MulChar.one_apply ((ZMod.isUnit_iff_coprime a q).mpr ha), one_mul,
    ← principal_character696 N q hN z] at hsplit
  have hgauss : conjugateGauss491 q (1 : DirichletCharacter ℂ q) =
      (ArithmeticFunction.moebius q : ℂ) := by
    unfold conjugateGauss491
    rw [residue_gauss_eq470, LeanLab.Grimmelt2019.MainTerm.gaussSum_principal]
    simp
  rw [hgauss] at hsplit
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  unfold residueError520 principalCoefficient520
  rw [← hsplit] at hinv
  push_cast
  field_simp
  linear_combination -hinv

/-- P0093 page 160 equation 5.5. Summing the residue phases before taking
norms preserves the exact Gauss and frequency coefficients. -/
theorem residue_phase_sum696 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (n : ℤ) (z : ℝ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      residueError520 N q a z * Complex.exp
        (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) =
      (1 / (q.totient : ℂ)) *
        (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          conjugateGauss491 q χ * residuePhase555 q n χ * characterPrime280 χ N z) +
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        divisorPart1121 N q a z * Complex.exp
          (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) := by
  classical
  calc
    _ = ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        (((1 / (q.totient : ℂ)) *
          ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            χ a * conjugateGauss491 q χ * characterPrime280 χ N z) +
          divisorPart1121 N q a z) * Complex.exp
            (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) := by
      apply sum_congr rfl
      intro a ha
      rw [residue_character_linear696 N q hN a (mem_filter.mp ha).2 z]
    _ = _ := by
      simp only [add_mul, sum_add_distrib]
      congr 1
      simp only [mul_sum, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro χ _
      unfold residuePhase555
      simp only [mul_sum, sum_mul]
      apply sum_congr rfl
      intro a _
      ring

/-- P0093 page 160 equation 5.5 with page 155 equation 2.3. The exact
mixed integral consists of its character part and its prime divisor part. -/
theorem mixed_integral_character696 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (n : ℤ) :
    mixedIntegral520 N q n =
      (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        (2 * principalCoefficient520 q / (q.totient : ℂ) *
          conjugateGauss491 q χ * residuePhase555 q n χ) *
          (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            principalPrime520 N q z * characterPrime280 χ N z *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))) +
      (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        2 * principalCoefficient520 q * principalPrime520 N q z *
          (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            divisorPart1121 N q a z * Complex.exp
              (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) := by
  classical
  let r : ℝ := 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))
  have hA := continuous_principal520 N q hN
  have hE (a : ℕ) := continuous_residue520 N q a hN
  have hχ (χ : DirichletCharacter ℂ q) : Continuous (characterPrime280 χ N) :=
    Task519.continuous_character_prime519 χ N hN
  have hD (a : ℕ) : Continuous (divisorPart1121 N q a) := by
    unfold divisorPart1121
    fun_prop
  have hIi : ∀ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      IntervalIntegrable (fun z : ℝ => 2 * principalCoefficient520 q *
        principalPrime520 N q z * residueError520 N q a z * Complex.exp
          (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))
          volume (-r) r := by
    intro a _
    exact (by fun_prop : Continuous _).intervalIntegrable _ _
  have hCi : ∀ χ : DirichletCharacter ℂ q,
      IntervalIntegrable (fun z : ℝ =>
        (2 * principalCoefficient520 q / (q.totient : ℂ) *
          conjugateGauss491 q χ * residuePhase555 q n χ) *
          (principalPrime520 N q z * characterPrime280 χ N z *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)))
          volume (-r) r := by
    intro χ
    exact (by fun_prop : Continuous _).intervalIntegrable _ _
  have hDi : IntervalIntegrable (fun z : ℝ =>
      2 * principalCoefficient520 q * principalPrime520 N q z *
        (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          divisorPart1121 N q a z * Complex.exp
            (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) volume (-r) r :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  unfold mixedIntegral520
  rw [← intervalIntegral.integral_finsetSum hIi]
  simp_rw [← intervalIntegral.integral_const_mul]
  have hSi : IntervalIntegrable (fun z : ℝ =>
      ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        (2 * principalCoefficient520 q / (q.totient : ℂ) *
          conjugateGauss491 q χ * residuePhase555 q n χ) *
          (principalPrime520 N q z * characterPrime280 χ N z *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)))
        volume (-r) r := (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [← intervalIntegral.integral_finsetSum (fun χ _ => hCi χ),
    ← intervalIntegral.integral_add hSi hDi]
  apply intervalIntegral.integral_congr
  intro z _
  dsimp only
  have hs := residue_phase_sum696 N q hN n z
  calc
    _ = 2 * principalCoefficient520 q * principalPrime520 N q z *
        (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          residueError520 N q a z * Complex.exp
            (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) := by
      simp only [mul_sum, sum_mul, centred_phase520]
      apply sum_congr rfl
      intro a _
      ring
    _ = _ := by
      rw [hs]
      simp only [mul_add, add_mul, mul_sum, sum_mul]
      congr 1
      apply sum_congr rfl
      intro χ _
      ring

/-- P0093 page 155 exponential damping. The principal series has norm
at most twice N, uniformly in the modulus and the phase. -/
theorem principal_pointwise696 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (z : ℝ) :
    ‖principalPrime520 N q z‖ ≤ 2 * (N : ℝ) := by
  rw [principal_character696 N q hN z]
  let c := fun p : Nat.Primes => (1 : DirichletCharacter ℂ q) (p : ℕ)
  have hc (p : Nat.Primes) : ‖c p‖ ≤ 1 := (1 : DirichletCharacter ℂ q).norm_le_one _
  have hs := summable_twist491 N hN c hc z
  have hb := norm_tsum_le_tsum_norm hs
  have ht := Summable.tsum_le_tsum (fun p => norm_twist_le491 N c hc p z)
    hs (summable_prime_damp491 N hN)
  calc
    _ ≤ ∑' p : Nat.Primes, Real.exp (-((p : ℕ) : ℝ) / N) := by
      simpa only [characterPrime280, c, mul_assoc] using hb.trans ht
    _ ≤ _ := tsum_prime_damp_le491 N hN

/-- P0093 page 160 equation 5.5. The character part of the residue
mixed integral is the existing mixed ordered character term. -/
theorem mixed_character_part696 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (n : ℤ) :
    (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      (2 * principalCoefficient520 q / (q.totient : ℂ) *
        conjugateGauss491 q χ * residuePhase555 q n χ) *
        (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          principalPrime520 N q z * characterPrime280 χ N z *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))) =
      mixedTerm491 N q n := by
  classical
  unfold mixedTerm491
  apply sum_congr rfl
  intro χ _
  rw [characterPair_comm555 N q n χ 1]
  have hS :
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        (1 : DirichletCharacter ℂ q) a * χ a * Complex.exp
          (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) =
      residuePhase555 q n χ := by
    apply sum_congr rfl
    intro a ha
    rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime a q).mpr (mem_filter.mp ha).2),
      one_mul]
  have hgauss : conjugateGauss491 q (1 : DirichletCharacter ℂ q) =
      (ArithmeticFunction.moebius q : ℂ) := by
    unfold conjugateGauss491
    rw [residue_gauss_eq470, LeanLab.Grimmelt2019.MainTerm.gaussSum_principal]
    simp
  unfold characterPair491
  rw [hS, hgauss]
  simp_rw [principal_character696 N q hN]
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  unfold principalCoefficient520
  push_cast
  field_simp
  ring_nf
  congr 2
  apply intervalIntegral.integral_congr
  intro z _
  congr 1
  congr 1
  ring

/-- P0093 pages 155 and 160 equations 2.3 and 5.5. The prime divisor
part of the residue mixed integral is at most eight N over tau. -/
theorem mixed_divisor_bound696 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) :
    ∀ n : ℤ,
      ‖∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        2 * principalCoefficient520 q * principalPrime520 N q z *
          (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            divisorPart1121 N q a z * Complex.exp
              (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
        8 * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) := by
  classical
  intro n
  have hq : 1 ≤ q := NeZero.pos q
  have hqp : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hτp : 0 < (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hφp : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hcard : (((range q).filter (fun a => Nat.Coprime a q)).card : ℝ) =
      (q.totient : ℝ) := by
    congr 1
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext a
    simp [Nat.coprime_comm]
  have hD (z : ℝ) :
      ‖∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        divisorPart1121 N q a z * Complex.exp
          (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)‖ ≤
        (q.totient : ℝ) * q := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _a ∈ (range q).filter (fun a => Nat.Coprime a q), (q : ℝ) := by
        apply sum_le_sum
        intro a _
        simpa only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
          divisor_part_norm1121 N q a z
      _ = _ := by rw [sum_const, nsmul_eq_mul, hcard]
  have hb (z : ℝ) :
      ‖2 * principalCoefficient520 q * principalPrime520 N q z *
        (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          divisorPart1121 N q a z * Complex.exp
            (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
        4 * (N : ℝ) * q := by
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    rw [htwo]
    calc
      _ ≤ 2 * (1 / (q.totient : ℝ)) * (2 * (N : ℝ)) * ((q.totient : ℝ) * q) := by
        gcongr
        · exact coefficient_le_inv_totient_prep1121 q hq
        · exact principal_pointwise696 N q hN z
        · exact hD z
      _ = _ := by field_simp [ne_of_gt hφp]; ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))))
    (b := 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) (fun z _ => hb z)
  have hr : 0 < 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
  rw [abs_of_pos (by linarith :
    0 < 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) -
      -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))))] at hi
  convert hi using 1 <;> field_simp [ne_of_gt hqp, ne_of_gt hτp] <;> ring

end LeanLab.Linnik1951
