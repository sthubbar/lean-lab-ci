/-
P0093 pages 155, 156, 159 and 160, equations 2.3, 3.4, 5.2 and 5.4.
Closure of residue_square_mean520 along the paper's character expansion:
the residue error is the nonprincipal part of the character expansion plus the
prime divisor term of 2.3, character orthogonality and the Gauss bound of
Lemma 1 turn its residue square mean into the nonprincipal character square
means, and Lemma 2 in the form nonprincipal_mass519 bounds each of those.
CONDITIONAL ON GRH and on the open leaves of nonprincipal_mass519.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp520a
import LeanLab.Linnik1951.ResidueData696
import LeanLab.Linnik1951.Decomp519a
import LeanLab.Linnik1951.Decomp552g

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- P0093 pages 159 and 160 equations 5.2 and 5.4, the exact statement of
residue_square_mean520. CONDITIONAL ON GRH, the leaves of this file and the
open leaves of nonprincipal_mass519. -/
theorem residue_square_mean1121 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))), ‖residueError520 N q a z‖ ^ 2) ≤
        C * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 := by
  classical
  obtain ⟨C, hC, N0, hm⟩ := Task519.nonprincipal_mass519 hG
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨2 * C + 4, by positivity, max 1 (max L N0), ?_⟩
  intro N hN q hq hqN
  have : NeZero q := ⟨by omega⟩
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hLN : (L : ℝ) < N := by exact_mod_cast (show L < N by omega)
  have hlog : 1 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hL.trans hLN).le
  have hlog13 : 1 ≤ Real.log N ^ 13 := one_le_pow₀ hlog
  set τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ) with hτdef
  have hτp : 0 < τ := by positivity
  have hτ1 : 1 ≤ τ := Real.one_le_rpow hN1R (by norm_num)
  have h10 : (N : ℝ) ^ (1 / 10 : ℝ) ≤ τ :=
    Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
  have hq7 : (q : ℝ) ≤ τ := hqN.trans h10
  set R : ℝ := (q : ℝ) * τ with hRdef
  have hRp : 0 < R := by positivity
  have hR1 : 1 ≤ R := by nlinarith
  have hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by
    have : (N : ℝ) ^ (2 / 7 : ℝ) = τ * τ := by
      rw [hτdef, ← Real.rpow_add hNp]; norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_right hq7 hτp.le
  have hr0 : 0 ≤ 1 / R := by positivity
  have hab : -(1 / R) ≤ 1 / R := by linarith
  -- integrability of every integrand
  have hEi : ∀ a, IntervalIntegrable (fun z => ‖residueError520 N q a z‖ ^ 2)
      volume (-(1 / R)) (1 / R) := fun a =>
    ((continuous_residue520 N q a hN1).norm.pow 2).intervalIntegrable _ _
  have hAi : ∀ χ : DirichletCharacter ℂ q,
      IntervalIntegrable (fun z => ‖Task519.characterPrime519 χ N z‖ ^ 2)
        volume (-(1 / R)) (1 / R) := fun χ =>
    ((Task519.continuous_character_prime519 χ N hN1).norm.pow 2).intervalIntegrable _ _
  have hcardχ := nonprincipal_card1121 q
  have hφp : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hAc : Continuous (fun z => ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      ‖Task519.characterPrime519 χ N z‖ ^ 2) :=
    continuous_finsetSum _ fun χ _ =>
      (Task519.continuous_character_prime519 χ N hN1).norm.pow 2
  -- integrate the pointwise energy
  have hint :
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / R)..(1 / R), ‖residueError520 N q a z‖ ^ 2) ≤
      2 * ((q : ℝ) / q.totient *
        ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ∫ z in -(1 / R)..(1 / R), ‖Task519.characterPrime519 χ N z‖ ^ 2) +
        2 * (q : ℝ) ^ 3 * (2 / R) := by
    rw [← intervalIntegral.integral_finsetSum (fun a _ => hEi a)]
    have hrhs : (∫ z in -(1 / R)..(1 / R), (2 * ((q : ℝ) / q.totient *
          ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖Task519.characterPrime519 χ N z‖ ^ 2) + 2 * (q : ℝ) ^ 3)) =
        2 * ((q : ℝ) / q.totient *
        ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ∫ z in -(1 / R)..(1 / R), ‖Task519.characterPrime519 χ N z‖ ^ 2) +
        2 * (q : ℝ) ^ 3 * (2 / R) := by
      have h1 : IntervalIntegrable (fun z => 2 * ((q : ℝ) / q.totient *
          ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖Task519.characterPrime519 χ N z‖ ^ 2)) volume (-(1 / R)) (1 / R) :=
        ((continuous_const.mul (continuous_const.mul hAc))).intervalIntegrable _ _
      rw [intervalIntegral.integral_add h1 intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum (fun χ _ => hAi χ),
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← hrhs]
    apply intervalIntegral.integral_mono_on hab
    · exact (continuous_finsetSum _ fun a _ =>
        (continuous_residue520 N q a hN1).norm.pow 2).intervalIntegrable _ _
    · exact ((continuous_const.mul (continuous_const.mul hAc)).add
        continuous_const).intervalIntegrable _ _
    · intro z _
      exact pointwise_energy1121 N q hN1 z
  -- the character square means
  have hmass : ∀ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      (∫ z in -(1 / R)..(1 / R), ‖Task519.characterPrime519 χ N z‖ ^ 2) ≤
        C * ((N : ℝ) / R * Real.log N ^ 13) := by
    intro χ hχ
    exact hm N (by omega) q hq hq7 χ (mem_filter.mp hχ).2 R hR1 hR2
  have hsumχ : (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      ∫ z in -(1 / R)..(1 / R), ‖Task519.characterPrime519 χ N z‖ ^ 2) ≤
      (q.totient : ℝ) * (C * ((N : ℝ) / R * Real.log N ^ 13)) := by
    calc _ ≤ ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          C * ((N : ℝ) / R * Real.log N ^ 13) := sum_le_sum hmass
      _ = _ := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcardχ (by positivity)
  have hq2 : (q : ℝ) ^ 2 ≤ N := by
    have h1 : (q : ℝ) ^ 2 ≤ ((N : ℝ) ^ (1 / 10 : ℝ)) ^ 2 := pow_le_pow_left₀ hqp.le hqN 2
    have h2 : ((N : ℝ) ^ (1 / 10 : ℝ)) ^ 2 ≤ N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
      calc (N : ℝ) ^ ((1 / 10 : ℝ) * ((2 : ℕ) : ℝ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
        _ = N := Real.rpow_one _
    linarith
  have hfin1 : 2 * ((q : ℝ) / q.totient *
      ((q.totient : ℝ) * (C * ((N : ℝ) / R * Real.log N ^ 13)))) =
      2 * C * (N : ℝ) / τ * Real.log N ^ 13 := by
    rw [hRdef]; field_simp
  have hfin2 : 2 * (q : ℝ) ^ 3 * (2 / R) ≤ 4 * (N : ℝ) / τ * Real.log N ^ 13 := by
    have he : 2 * (q : ℝ) ^ 3 * (2 / R) = 4 * (q : ℝ) ^ 2 / τ := by
      rw [hRdef]; field_simp; ring
    rw [he]
    have h4 : 4 * (q : ℝ) ^ 2 / τ ≤ 4 * (N : ℝ) / τ :=
      div_le_div_of_nonneg_right (by linarith) hτp.le
    have h5 : 4 * (N : ℝ) / τ ≤ 4 * (N : ℝ) / τ * Real.log N ^ 13 :=
      le_mul_of_one_le_right (by positivity) hlog13
    linarith
  have hfin0 : 2 * ((q : ℝ) / q.totient *
        ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ∫ z in -(1 / R)..(1 / R), ‖Task519.characterPrime519 χ N z‖ ^ 2) ≤
      2 * ((q : ℝ) / q.totient *
        ((q.totient : ℝ) * (C * ((N : ℝ) / R * Real.log N ^ 13)))) := by
    gcongr
  calc _ ≤ _ := hint
    _ ≤ 2 * C * (N : ℝ) / τ * Real.log N ^ 13 + 4 * (N : ℝ) / τ * Real.log N ^ 13 := by
      rw [← hfin1]; exact add_le_add hfin0 hfin2
    _ = _ := by ring

end LeanLab.Linnik1951
