/-
Copyright (c) 2026 Lean Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI
-/
import Mathlib
import LeanLab.SparseTernary.Arc613FromSW
import LeanLab.SparseTernary.SWPartialSum
import LeanLab.SparseTernary.LocalFactors
import LeanLab.SparseTernary.RepAssembly
import LeanLab.SparseTernary.Section4
import LeanLab.SparseTernary.MajorArcs
import LeanLab.SparseTernary.Major618FromSW
import LeanLab.SparseTernary.Gluing

open Finset Filter Real MeasureTheory
open scoped Classical

noncomputable section
namespace LeanLab.SparseTernary.DecompJ269

open LeanLab.SparseTernary LeanLab.SparseTernary.Section4 LeanLab.SparseTernary.MajorArcs
open LeanLab.SparseTernary.LocalFactors LeanLab.SparseTernary.Tail72Proof
open LeanLab.SparseTernary.SWInput
open LeanLab.SparseTernary.SWPartial LeanLab.SparseTernary.Arc613Proof
open LeanLab.SparseTernary.Major618SW

def Iu (u : ℝ) : Finset ℕ := Icc ⌈u⌉₊ ⌊2 * u⌋₊
def Stil_alias (u β : ℝ) : ℂ := ∑ k ∈ Iu u, (ArithmeticFunction.vonMangoldt k : ℂ) * ee (k * β)

/-- The principal Gauss sum in Section 6, page 9, at every coprime residue. -/
theorem ramanujan_at_unit (q a : ℕ) (hq : 0 < q) (ha : a.Coprime q) :
    ram q a = (ArithmeticFunction.moebius q : ℂ) := by
  have hsums : ∀ n > 0, n ∣ q →
      ∑ d ∈ n.divisors, ram d a = if n = 1 then 1 else 0 := by
    intro n hn hnd
    have h := LeanLab.SparseTernary.Lemma82Proof.farey n hn (fun _ => 1) (-(a : ℤ))
    simp only [one_mul] at h
    rw [LeanLab.SparseTernary.Lemma82Proof.sum_range_ee n hn] at h
    have hdiv : ((n : ℤ) ∣ -(a : ℤ)) ↔ n = 1 := by
      rw [dvd_neg, Int.natCast_dvd_natCast]
      exact ⟨fun hna => Nat.eq_one_of_dvd_coprimes ha hna hnd,
        by rintro rfl; exact one_dvd _⟩
    simp only [hdiv] at h
    by_cases h1 : n = 1
    · subst n
      simpa only [ram, Int.cast_neg, Int.cast_natCast, mul_neg, neg_div,
        ite_eq_left rfl, Nat.cast_one] using h
    · simpa only [ram, Int.cast_neg, Int.cast_natCast, mul_neg, neg_div,
        ite_eq_right h1] using h
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
    (R := ℂ) {n | n ∣ q} (by intro m n hmn hn; exact hmn.trans hn)).mp hsums
    q hq (dvd_refl q)
  rw [Nat.sum_divisorsAntidiagonal' (fun x y =>
    (ArithmeticFunction.moebius x : ℂ) * (if y = 1 then 1 else 0))] at hi
  simpa [mul_ite, Nat.mem_divisors, hq.ne'] using hi.symm

/-- Residue class form of display 6.3 on page 8, when q is below u. -/
theorem prime_residue_expansion (u β : ℝ) (q a : ℕ) (hq : 0 < q) (hqu : (q : ℝ) < u) :
    (∑ p ∈ (Iw u).filter Nat.Prime,
      (Real.log p : ℂ) * ee (p * ((a : ℝ) / q + β))) =
    ∑ b ∈ U q, ee ((a : ℝ) * b / q) * thetaE u β q b := by
  simp only [thetaE, sum_filter, mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  refine sum_congr rfl fun p hp => ?_
  by_cases hprime : p.Prime
  · have hup : u ≤ p := (Nat.le_ceil u).trans (by exact_mod_cast (mem_Icc.mp hp).1)
    have hpq : q < p := by exact_mod_cast hqu.trans_le hup
    have hcop : p.Coprime q := hprime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt hq hpq)
    let b := (p + q - 1) % q + 1
    have hbI : b ∈ Icc 1 q := by
      have := Nat.mod_lt (p + q - 1) hq
      simp only [b, mem_Icc]; omega
    have hmod : b ≡ p [MOD q] := by
      have h1 := (Nat.mod_modEq (p + q - 1) q).add_right 1
      have h2 : p + q - 1 + 1 = p + q := by omega
      rw [h2] at h1
      exact h1.trans (by show (p + q) % q = p % q; exact Nat.add_mod_right _ _)
    have hbU : b ∈ U q := by
      refine mem_filter.mpr ⟨hbI, ?_⟩
      rw [Nat.coprime_iff_gcd_eq_one, hmod.gcd_eq]
      exact hcop.gcd_eq_one
    have hphase : ee (p * ((a : ℝ) / q + β)) =
        ee ((a : ℝ) * b / q) * ee (p * β) := by
      obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd).mp hmod
      have htR : (p : ℝ) - b = q * (t : ℝ) := by exact_mod_cast ht
      have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      rw [← ee_add]
      have heq : (p : ℝ) * (a / q + β) =
          a * b / q + p * β + (((a : ℤ) * t : ℤ) : ℝ) := by
        push_cast
        field_simp
        nlinarith [htR]
      rw [heq, LeanLab.SparseTernary.RepAssembly.ee_shift]
    rw [sum_eq_single b]
    · simp only [hprime, hmod.symm, and_self, ite_eq_left]
      rw [hphase]; ring
    · intro c hc hcb
      have hnc : ¬ p ≡ c [MOD q] := by
        intro hpc
        exact hcb (U_eq_of_modEq hc hbU (hpc.symm.trans hmod.symm))
      simp [hnc]
    · exact fun h => (h hbU).elim
  · simp [hprime]

/-- The positive phase form of the principal Gauss sum on page 9. -/
theorem reduced_phase_sum (q a : ℕ) (hq : 0 < q) (ha : a.Coprime q) :
    ∑ b ∈ U q, ee ((a : ℝ) * b / q) = (ArithmeticFunction.moebius q : ℂ) := by
  have he (x : ℝ) : (starRingEnd ℂ) (ee (-x)) = ee x := by
    unfold ee
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  have h := congrArg (starRingEnd ℂ) (ramanujan_at_unit q a hq ha)
  simp only [ram, map_sum, map_intCast] at h
  have ht (b : ℕ) : (starRingEnd ℂ) (ee (-((b : ℝ) * a / q))) =
      ee ((a : ℝ) * b / q) := by rw [he]; congr 1; ring
  simpa only [ht] using h

/-- The prime part of display 6.10, conditional on Siegel-Walfisz. -/
theorem prime_fraction_approx (N : ℕ) (hSW : SW (N + 1)) (K : ℝ) (hK : 0 ≤ K) :
    ∃ D u0 : ℝ, ∀ u : ℝ, u0 ≤ u → ∀ q a : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log u ^ N → a.Coprime q → ∀ β : ℝ,
      ‖(∑ p ∈ (Iw u).filter Nat.Prime,
        (Real.log p : ℂ) * ee (p * ((a : ℝ) / q + β))) -
        ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * Tsum u β‖ ≤
        D * (1 + |β| * u) * u / Real.log u ^ K := by
  obtain ⟨D, u0, hD⟩ := swExp N hSW (K + N) (by positivity)
  have hsmall : ∀ᶠ u : ℝ in atTop, Real.log u ^ N < u := by
    filter_upwards [(isLittleO_pow_log_id_atTop (n := N)).bound
      (by norm_num : (0 : ℝ) < 1 / 2), eventually_ge_atTop (2 : ℝ)] with u hu hu2
    simp only [Real.norm_eq_abs, id_eq, abs_of_pos (by linarith : 0 < u)] at hu
    have := le_abs_self (Real.log u ^ N)
    linarith
  obtain ⟨v0, hv0⟩ := hsmall.exists_forall_of_atTop
  refine ⟨|D|, max u0 (max v0 (Real.exp 1)), ?_⟩
  intro u hu q a hq hqu ha β
  have huu0 : u0 ≤ u := (le_max_left _ _).trans hu
  have huv0 : v0 ≤ u := (le_max_left _ _).trans ((le_max_right _ _).trans hu)
  have hue : Real.exp 1 ≤ u := (le_max_right _ _).trans ((le_max_right _ _).trans hu)
  have hu0 : 0 < u := (Real.exp_pos 1).trans_le hue
  have hL : 0 < Real.log u := by
    have := Real.log_le_log (Real.exp_pos 1) hue
    rw [Real.log_exp] at this
    linarith
  have hmodel : ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * Tsum u β =
      ∑ b ∈ U q, ee ((a : ℝ) * b / q) * ((1 / (q.totient : ℂ)) * Tsum u β) := by
    rw [← sum_mul, reduced_phase_sum q a (by omega) ha]
    ring
  rw [prime_residue_expansion u β q a (by omega) (hqu.trans_lt (hv0 u huv0)), hmodel,
    ← sum_sub_distrib]
  simp only [← mul_sub]
  have hc : (#(U q) : ℝ) ≤ Real.log u ^ N := by
    calc (#(U q) : ℝ) = q.totient := by rw [card_U]
      _ ≤ q := by exact_mod_cast Nat.totient_le q
      _ ≤ Real.log u ^ N := hqu
  calc
    ‖∑ b ∈ U q, ee ((a : ℝ) * b / q) *
        (thetaE u β q b - (1 / (q.totient : ℂ)) * Tsum u β)‖
        ≤ ∑ b ∈ U q, ‖ee ((a : ℝ) * b / q) *
          (thetaE u β q b - (1 / (q.totient : ℂ)) * Tsum u β)‖ := norm_sum_le _ _
    _ = ∑ b ∈ U q, ‖thetaE u β q b - (1 / (q.totient : ℂ)) * Tsum u β‖ := by
      simp only [norm_mul, norm_ee, one_mul]
    _ ≤ ∑ b ∈ U q, |D| * (1 + |β| * u) * u / Real.log u ^ (K + N) := by
      refine sum_le_sum fun b hb => (hD u huu0 q b hq hqu (mem_filter.mp hb).2 β).trans ?_
      gcongr
      exact le_abs_self D
    _ = (#(U q) : ℝ) * (|D| * (1 + |β| * u) * u / Real.log u ^ (K + N)) := by
      simp [sum_const, nsmul_eq_mul]
    _ ≤ Real.log u ^ N * (|D| * (1 + |β| * u) * u / Real.log u ^ (K + N)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = |D| * (1 + |β| * u) * u / Real.log u ^ K := by
      rw [Real.rpow_add hL, Real.rpow_natCast]
      field_simp

/-- The proper prime power contribution removed before displays 6.5 to 6.10. -/
theorem prime_power_difference_bound (u β : ℝ) (q a : ℕ) (hu : 1 ≤ u) :
    ‖LambdaSum u β q a - (∑ p ∈ (Iw u).filter Nat.Prime,
      (Real.log p : ℂ) * ee (p * ((a : ℝ) / q + β)))‖ ≤
      (#(LeanLab.SparseTernary.RepAssembly.NP ⌊2 * u⌋₊) : ℝ) * Real.log (2 * u) := by
  let S := (Iw u).filter (fun k => IsPrimePow k ∧ ¬ k.Prime)
  have hsum : LambdaSum u β q a - (∑ p ∈ (Iw u).filter Nat.Prime,
      (Real.log p : ℂ) * ee (p * ((a : ℝ) / q + β))) =
      ∑ k ∈ S, (ArithmeticFunction.vonMangoldt k : ℂ) *
        ee (k * ((a : ℝ) / q + β)) := by
    simp only [LambdaSum, S, sum_filter, ← sum_sub_distrib]
    refine sum_congr rfl fun k hk => ?_
    by_cases hp : k.Prime
    · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · by_cases hpp : IsPrimePow k
      · simp [hp, hpp]
      · simp [hp, hpp, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
  have hsub : S ⊆ LeanLab.SparseTernary.RepAssembly.NP ⌊2 * u⌋₊ := by
    intro k hk
    obtain ⟨hk, hpp, hnp⟩ := mem_filter.mp hk
    have hlow : 1 ≤ k := by
      have : u ≤ k := (Nat.le_ceil u).trans (by exact_mod_cast (mem_Icc.mp hk).1)
      exact_mod_cast hu.trans this
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hlow, (mem_Icc.mp hk).2⟩, hpp, hnp⟩
  rw [hsum]
  calc
    ‖∑ k ∈ S, (ArithmeticFunction.vonMangoldt k : ℂ) *
        ee (k * ((a : ℝ) / q + β))‖ ≤ ∑ k ∈ S, ArithmeticFunction.vonMangoldt k := by
      refine norm_sum_le_of_le _ fun k hk => ?_
      rw [norm_mul, norm_ee, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ ≤ ∑ k ∈ LeanLab.SparseTernary.RepAssembly.NP ⌊2 * u⌋₊, ArithmeticFunction.vonMangoldt k :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ ≤ ∑ k ∈ LeanLab.SparseTernary.RepAssembly.NP ⌊2 * u⌋₊, Real.log (2 * u) := by
      refine sum_le_sum fun k hk => ArithmeticFunction.vonMangoldt_le_log.trans ?_
      have hkI := mem_Icc.mp (mem_filter.mp hk).1
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hkI.1
      have hku : (k : ℝ) ≤ 2 * u := (by exact_mod_cast hkI.2 : (k : ℝ) ≤ (⌊2 * u⌋₊ : ℕ)).trans
        (Nat.floor_le (by linarith))
      exact Real.log_le_log hkpos hku
    _ = (#(LeanLab.SparseTernary.RepAssembly.NP ⌊2 * u⌋₊) : ℝ) * Real.log (2 * u) := by simp

/-- Proper prime powers have every fixed logarithmic saving in the single sum. -/
theorem prime_power_error_small (K : ℝ) : ∀ᶠ u : ℝ in atTop,
    (#(LeanLab.SparseTernary.RepAssembly.NP ⌊2 * u⌋₊) : ℝ) * Real.log (2 * u) ≤ u / Real.log u ^ K := by
  filter_upwards [LeanLab.SparseTernary.RepAssembly.pp_small K, eventually_ge_atTop (Real.exp 1)] with u hu hue
  have hu0 : 0 < u := (Real.exp_pos 1).trans_le hue
  have hu1 : 1 ≤ u := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hue
  have hL : 0 < Real.log u := by
    have := Real.log_le_log (Real.exp_pos 1) hue
    rw [Real.log_exp] at this
    linarith
  have hLu : 1 ≤ Real.log (2 * u) := by
    have h2 : Real.exp 1 ≤ 2 * u := by linarith
    have := Real.log_le_log (Real.exp_pos 1) h2
    simpa only [Real.log_exp] using this
  have hn : u ≤ (⌊2 * u⌋₊ : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (2 * u)
    linarith
  have hcard : 0 ≤ (#(LeanLab.SparseTernary.RepAssembly.NP ⌊2 * u⌋₊) : ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (2 * u) := by linarith
  have hden : 0 < Real.log u ^ K := Real.rpow_pos_of_pos hL _
  push_cast at hu
  have hbase : ((#(LeanLab.SparseTernary.RepAssembly.NP ⌊2 * u⌋₊) : ℝ) * Real.log (2 * u)) * u ≤
      Real.log (2 * u) ^ 3 * (3 * ((#(LeanLab.SparseTernary.RepAssembly.NP ⌊2 * u⌋₊) : ℝ) * ((⌊2 * u⌋₊ : ℝ) + 1))) := by
    have hlog3 : Real.log (2 * u) ≤ Real.log (2 * u) ^ 3 := by nlinarith [sq_nonneg (Real.log (2 * u) - 1)]
    calc
      ((#(LeanLab.SparseTernary.RepAssembly.NP ⌊2 * u⌋₊) : ℝ) * Real.log (2 * u)) * u ≤
          ((#(LeanLab.SparseTernary.RepAssembly.NP ⌊2 * u⌋₊) : ℝ) * Real.log (2 * u) ^ 3) * ((⌊2 * u⌋₊ : ℝ) + 1) := by gcongr
      _ ≤ Real.log (2 * u) ^ 3 * (3 * ((#(LeanLab.SparseTernary.RepAssembly.NP ⌊2 * u⌋₊) : ℝ) * ((⌊2 * u⌋₊ : ℝ) + 1))) := by
        have hnonneg : 0 ≤ Real.log (2 * u) ^ 3 *
            ((#(LeanLab.SparseTernary.RepAssembly.NP ⌊2 * u⌋₊) : ℝ) * ((⌊2 * u⌋₊ : ℝ) + 1)) := by positivity
        nlinarith
  apply (mul_le_mul_iff_left₀ hu0).mp
  have hh : u ^ 2 / (2 * Real.log u ^ K) ≤ u * (u / Real.log u ^ K) := by
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [sq_nonneg u]
  calc
    ((#(LeanLab.SparseTernary.RepAssembly.NP ⌊2 * u⌋₊) : ℝ) * Real.log (2 * u)) * u =
        ((#(LeanLab.SparseTernary.RepAssembly.NP ⌊2 * u⌋₊) : ℝ) * Real.log (2 * u)) * u := rfl
    _ ≤ _ := hbase
    _ ≤ _ := hu.le
    _ ≤ _ := hh
    _ = (u / Real.log u ^ K) * u := by ring

/-- Display 6.10 with an arbitrary nonnegative logarithmic saving, conditional on SW. -/
theorem per_fraction_of_sw (N : ℕ) (hSW : SW (N + 1)) (K : ℝ) (hK : 0 ≤ K) :
    PerFractionApprox N K := by
  obtain ⟨D, u0, hD⟩ := prime_fraction_approx N hSW K hK
  obtain ⟨v0, hv⟩ := (prime_power_error_small K).exists_forall_of_atTop
  refine ⟨D + 1, max u0 (max v0 (Real.exp 1)), ?_⟩
  intro u hu q a hq hqu ha β
  have huu0 : u0 ≤ u := (le_max_left _ _).trans hu
  have huv0 : v0 ≤ u := (le_max_left _ _).trans ((le_max_right _ _).trans hu)
  have hue : Real.exp 1 ≤ u := (le_max_right _ _).trans ((le_max_right _ _).trans hu)
  have hu1 : 1 ≤ u := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hue
  have hu0 : 0 < u := by linarith
  have hL : 0 < Real.log u := by
    have := Real.log_le_log (Real.exp_pos 1) hue
    rw [Real.log_exp] at this
    linarith
  let P : ℂ := ∑ p ∈ (Iw u).filter Nat.Prime,
    (Real.log p : ℂ) * ee (p * ((a : ℝ) / q + β))
  have herr : ‖LambdaSum u β q a - P‖ ≤ u / Real.log u ^ K :=
    (prime_power_difference_bound u β q a hu1).trans (hv u huv0)
  have hp := hD u huu0 q a hq hqu ha β
  have hscale : u / Real.log u ^ K ≤ (1 + |β| * u) * u / Real.log u ^ K := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg (abs_nonneg β) (sq_nonneg u)]
  calc
    ‖LambdaSum u β q a - ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * Tsum u β‖
        ≤ ‖LambdaSum u β q a - P‖ +
          ‖P - ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * Tsum u β‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ u / Real.log u ^ K + D * (1 + |β| * u) * u / Real.log u ^ K :=
      add_le_add herr hp
    _ ≤ (D + 1) * (1 + |β| * u) * u / Real.log u ^ K := by
      calc
        _ ≤ (1 + |β| * u) * u / Real.log u ^ K +
            D * (1 + |β| * u) * u / Real.log u ^ K := add_le_add hscale le_rfl
        _ = _ := by ring

/-- The reduced shifted fraction used in display 6.2 on page 8. -/
theorem shifted_fraction_data (Z q a ℓ : ℕ) (hq : 0 < q) :
    0 < qell Z q a ℓ ∧ qell Z q a ℓ ≤ q * q0 Z ∧
      ((a * q0 Z + ℓ * q) / Nat.gcd (a * q0 Z + ℓ * q) (q * q0 Z)).Coprime
        (qell Z q a ℓ) ∧
      (a : ℝ) / q + (ℓ : ℝ) / q0 Z =
        (((a * q0 Z + ℓ * q) / Nat.gcd (a * q0 Z + ℓ * q) (q * q0 Z) : ℕ) : ℝ) /
          qell Z q a ℓ := by
  have hq0 := q0_pos Z
  have hn : 0 < q * q0 Z := Nat.mul_pos hq hq0
  have hg : 0 < Nat.gcd (a * q0 Z + ℓ * q) (q * q0 Z) := Nat.gcd_pos_of_pos_right _ hn
  have hden : qell Z q a ℓ = (q * q0 Z) / Nat.gcd (a * q0 Z + ℓ * q) (q * q0 Z) := by
    unfold qell
    rw [Nat.gcd_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hden]
    exact Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_right _ _)) hg
  · unfold qell
    exact Nat.div_le_self _ _
  · rw [hden]
    exact Nat.coprime_div_gcd_div_gcd hg
  · rw [hden, Nat.cast_div_div_div_cancel_right
      (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)]
    push_cast
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hq0R : (q0 Z : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    field_simp

/-- LEAF: the per-fraction approximation of display 6.10. -/
theorem per_fraction_approx (A B : ℕ) (hSW : SW (B + 5 * A + 1)) :
    PerFractionApprox (B + 5 * A) (12 * A) := by
  exact per_fraction_of_sw (B + 5 * A) hSW (12 * A) (by positivity)

/-- LEAF: the expansion 5.3 of S over l and r. -/
theorem s_expansion (Z : ℕ) (u α : ℝ) :
    Sexp Z u α = (1 / (q0 Z : ℂ)) * ∑ ℓ ∈ range (q0 Z), ∑ r ∈ R0 Z,
      ee (-((ℓ : ℝ) * r / q0 Z)) * Stil_alias u (α + ℓ / q0 Z) := by
  have hunique : ∀ {Z r r' : ℕ} (hr : r ∈ R0 Z) (hr' : r' ∈ R0 Z)
      (h : (q0 Z : ℤ) ∣ (r : ℤ) - r') , r = r' := by
    intro Z r r' hr hr' h
    have h1 := (mem_Icc.mp (mem_filter.mp hr).1)
    have h2 := (mem_Icc.mp (mem_filter.mp hr').1)
    have hlt : |(r : ℤ) - r'| < (q0 Z : ℤ) := by
      rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd h hlt
    omega
  have hcount : ∀ (Z k : ℕ),
      ∑ r ∈ R0 Z, (if (q0 Z : ℤ) ∣ (k : ℤ) - r then (1 : ℂ) else 0) =
        if (∃ r ∈ R0 Z, k ≡ r [MOD q0 Z]) then 1 else 0 := by
    intro Z k
    split_ifs with hex
    · obtain ⟨r0, hr0, hk⟩ := hex
      have hk' : (q0 Z : ℤ) ∣ (k : ℤ) - r0 := by
        rw [dvd_sub_comm]; exact (Nat.modEq_iff_dvd).mp hk
      have hiff : ∀ r ∈ R0 Z, ((q0 Z : ℤ) ∣ (k : ℤ) - r ↔ r0 = r) := by
        intro r hr; constructor
        · intro h
          have : (q0 Z : ℤ) ∣ (r0 : ℤ) - r := by
            have := dvd_sub h hk'; rw [show (k : ℤ) - r - (k - r0) = r0 - r by ring] at this
            exact this
          exact hunique hr0 hr this
        · rintro rfl; exact hk'
      rw [sum_congr rfl (fun r hr => if_congr (hiff r hr) rfl rfl), sum_ite_eq]
      simp [hr0]
    · refine sum_eq_zero fun r hr => ?_
      rw [if_neg]
      intro h
      exact hex ⟨r, hr, (Nat.modEq_iff_dvd).mpr (by rw [dvd_sub_comm]; exact h)⟩
  have hkey : ∀ (Z k : ℕ) (α : ℝ),
      (1 / (q0 Z : ℂ)) * ∑ ℓ ∈ range (q0 Z), ∑ r ∈ R0 Z,
          ee (-((ℓ : ℝ) * r / q0 Z)) * ee (k * (α + ℓ / q0 Z)) =
        if (∃ r ∈ R0 Z, k ≡ r [MOD q0 Z]) then ee (k * α) else 0 := by
    intro Z k α
    have hq := q0_pos Z
    have hq0 : (q0 Z : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hqr : (q0 Z : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hterm : ∀ ℓ r : ℕ, ee (-((ℓ : ℝ) * r / q0 Z)) * ee (k * (α + ℓ / q0 Z)) =
        ee (k * α) * ee ((ℓ : ℝ) * (((k : ℤ) - r : ℤ) : ℝ) / q0 Z) := by
      intro ℓ r
      rw [← ee_add, ← ee_add]; congr 1; push_cast; field_simp; ring
    simp_rw [hterm]
    rw [sum_comm]
    simp_rw [← mul_sum, LeanLab.SparseTernary.Lemma82Proof.sum_range_ee (q0 Z) hq]
    have : ee (k * α) * ∑ r ∈ R0 Z, (if (q0 Z : ℤ) ∣ ((k : ℤ) - r) then (q0 Z : ℂ) else 0) =
        ee (k * α) * (q0 Z : ℂ) *
          ∑ r ∈ R0 Z, (if (q0 Z : ℤ) ∣ (k : ℤ) - r then (1 : ℂ) else 0) := by
      rw [mul_assoc, mul_sum (a := (q0 Z : ℂ))]; congr 1; refine sum_congr rfl fun r _ => ?_
      split_ifs <;> ring
    rw [this, hcount]
    split_ifs
    · field_simp
    · simp
  symm
  have h1 : ∀ ℓ r : ℕ, ee (-((ℓ : ℝ) * r / q0 Z)) * Stil_alias u (α + ℓ / q0 Z) =
      ∑ k ∈ Iu u, (ArithmeticFunction.vonMangoldt k : ℂ) *
        (ee (-((ℓ : ℝ) * r / q0 Z)) * ee (k * (α + ℓ / q0 Z))) := by
    intro ℓ r; unfold Stil_alias; rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
  simp_rw [h1]
  rw [sum_congr rfl (fun ℓ _ => sum_comm), sum_comm, mul_sum]
  have h2 : ∀ k ∈ Iu u, (1 / (q0 Z : ℂ)) * ∑ ℓ ∈ range (q0 Z), ∑ r ∈ R0 Z,
      (ArithmeticFunction.vonMangoldt k : ℂ) *
        (ee (-((ℓ : ℝ) * r / q0 Z)) * ee (k * (α + ℓ / q0 Z))) =
      (ArithmeticFunction.vonMangoldt k : ℂ) * ((1 / (q0 Z : ℂ)) * ∑ ℓ ∈ range (q0 Z),
        ∑ r ∈ R0 Z, ee (-((ℓ : ℝ) * r / q0 Z)) * ee (k * (α + ℓ / q0 Z))) := by
    intro k _; simp_rw [← mul_sum]; ring
  rw [sum_congr rfl h2]
  simp_rw [hkey]
  unfold Sexp Aset
  rw [sum_filter]
  refine sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-- LEAF: the cube expansion 6.11 to 6.12. -/
theorem s_cube_expansion (Z : ℕ) (u α : ℝ) :
    Sexp Z u α ^ 3 = (1 / (q0 Z : ℂ) ^ 3) * ∑ ℓ₁ ∈ range (q0 Z), ∑ r₁ ∈ R0 Z,
      ∑ ℓ₂ ∈ range (q0 Z), ∑ r₂ ∈ R0 Z, ∑ ℓ₃ ∈ range (q0 Z), ∑ r₃ ∈ R0 Z,
      ee (-((ℓ₁ * r₁ + ℓ₂ * r₂ + ℓ₃ * r₃ : ℝ) / q0 Z)) *
      Stil_alias u (α + ℓ₁ / q0 Z) * Stil_alias u (α + ℓ₂ / q0 Z) * Stil_alias u (α + ℓ₃ / q0 Z) := by
  rw [s_expansion Z u α, mul_pow, one_div_pow]
  congr 1
  rw [pow_three]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine sum_congr rfl fun ℓ₁ _ => sum_congr rfl fun r₁ _ =>
    sum_congr rfl fun ℓ₂ _ => sum_congr rfl fun r₂ _ =>
    sum_congr rfl fun ℓ₃ _ => sum_congr rfl fun r₃ _ => ?_
  rw [show -((ℓ₁ * r₁ + ℓ₂ * r₂ + ℓ₃ * r₃ : ℝ) / q0 Z) =
    -((ℓ₁ : ℝ) * r₁ / q0 Z) + -((ℓ₂ : ℝ) * r₂ / q0 Z) +
      -((ℓ₃ : ℝ) * r₃ / q0 Z) by ring, ee_add, ee_add]
  ring

/-- LEAF: disjointness of the major arcs. -/
theorem major_arcs_disjoint (Q : ℝ) :
    ∀ q₁ a₁ q₂ a₂ : ℕ, a₁ < q₁ → a₂ < q₂ → a₁.Coprime q₁ → a₂.Coprime q₂ →
      (q₁ : ℝ) ≤ Real.sqrt (Q / 2) → (q₂ : ℝ) ≤ Real.sqrt (Q / 2) →
      (q₁ ≠ q₂ ∨ a₁ ≠ a₂) →
      Disjoint (Set.Ioo ((a₁ : ℝ) / q₁ - 1 / Q) ((a₁ : ℝ) / q₁ + 1 / Q))
               (Set.Ioo ((a₂ : ℝ) / q₂ - 1 / Q) ((a₂ : ℝ) / q₂ + 1 / Q)) := by
  intro q1 a1 q2 a2 h_a1 h_a2 h_cop1 h_cop2 h_q1 h_q2 h_neq
  rw [Set.disjoint_iff_forall_ne]
  intro x hx y hy h_eq
  subst h_eq
  have hq1_pos : 0 < q1 := by linarith
  have hq2_pos : 0 < q2 := by linarith
  have hq1_pos' : (0 : ℝ) < q1 := by exact Nat.cast_pos.mpr hq1_pos
  have hq2_pos' : (0 : ℝ) < q2 := by exact Nat.cast_pos.mpr hq2_pos

  have h_dist : |(a1 : ℝ) / q1 - (a2 : ℝ) / q2| < 2 / Q := by
    have h1 : |x - (a1 : ℝ) / q1| < 1 / Q := by
      rw [abs_lt]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h2 : |x - (a2 : ℝ) / q2| < 1 / Q := by
      rw [abs_lt]
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    calc
      |(a1 : ℝ) / q1 - (a2 : ℝ) / q2| ≤ |(a1 : ℝ) / q1 - x| + |x - (a2 : ℝ) / q2| := abs_sub_le _ _ _
      _ = |x - (a1 : ℝ) / q1| + |x - (a2 : ℝ) / q2| := by rw [abs_sub_comm _ _]
      _ < 1 / Q + 1 / Q := add_lt_add h1 h2
      _ = 2 / Q := by ring

  have h_neq_rat : (a1 : ℝ) / q1 ≠ (a2 : ℝ) / q2 := by
    intro h
    have h1 : (a1 : ℝ) * q2 = (a2 : ℝ) * q1 := by
      calc
        (a1 : ℝ) * q2 = ((a1 : ℝ) / q1) * (q1 * q2) := by
          have : ((a1 : ℝ) / q1) * (q1 * q2) = ((a1 : ℝ) * q2) * (q1 / q1) := by ring
          rw [this, div_self hq1_pos'.ne', mul_one]
        _ = ((a2 : ℝ) / q2) * (q1 * q2) := by rw [h]
        _ = (a2 : ℝ) * q1 := by
          have : ((a2 : ℝ) / q2) * (q1 * q2) = ((a2 : ℝ) * q1) * (q2 / q2) := by ring
          rw [this, div_self hq2_pos'.ne', mul_one]
    have h2 : a1 * q2 = a2 * q1 := by exact_mod_cast h1
    have h3 : q1 ∣ q2 := by
      have : q1 ∣ a2 * q1 := dvd_mul_left _ _
      rw [←h2] at this
      exact h_cop1.symm.dvd_of_dvd_mul_left this
    have h4 : q2 ∣ q1 := by
      have : q2 ∣ a1 * q2 := dvd_mul_left _ _
      rw [h2] at this
      exact h_cop2.symm.dvd_of_dvd_mul_left this
    have hq_eq : q1 = q2 := Nat.dvd_antisymm h3 h4
    have ha_eq : a1 = a2 := by
      subst hq_eq
      have : a1 * q1 = a2 * q1 := h2
      exact (Nat.mul_right_cancel hq1_pos) this
    tauto

  have h_diff_ge : 1 / (q1 * q2 : ℝ) ≤ |(a1 : ℝ) / q1 - (a2 : ℝ) / q2| := by
    have h_diff : (a1 : ℝ) / q1 - (a2 : ℝ) / q2 = (a1 * q2 - a2 * q1 : ℝ) / (q1 * q2 : ℝ) := by
      rw [div_sub_div _ _ hq1_pos'.ne' hq2_pos'.ne']
      ring_nf
    have h_abs_div : |(a1 * q2 - a2 * q1 : ℝ) / (q1 * q2 : ℝ)| = |(a1 * q2 - a2 * q1 : ℝ)| / |(q1 * q2 : ℝ)| := by
      rw [abs_div]
    have h_pos_prod : (0 : ℝ) < (q1 * q2 : ℝ) := by positivity
    have h_abs_denom : |(q1 * q2 : ℝ)| = (q1 * q2 : ℝ) := abs_of_pos h_pos_prod
    rw [h_diff, h_abs_div, h_abs_denom]
    have h_int_diff : (a1 * q2 : ℝ) - (a2 * q1 : ℝ) = ((a1 * q2 : ℤ) - (a2 * q1 : ℤ) : ℝ) := by push_cast; rfl
    rw [h_int_diff]
    have h_int_neq : (a1 * q2 : ℤ) - (a2 * q1 : ℤ) ≠ 0 := by
      intro h
      have h1 : (a1 * q2 : ℤ) = (a2 * q1 : ℤ) := sub_eq_zero.mp h
      have h2 : (a1 : ℝ) / q1 = (a2 : ℝ) / q2 := by
        rw [← sub_eq_zero]
        rw [h_diff]
        have h3 : (a1 * q2 : ℝ) - (a2 * q1 : ℝ) = 0 := by exact_mod_cast sub_eq_zero.mpr h1
        rw [h3, zero_div]
      exact h_neq_rat h2
    have h_int_ge : 1 ≤ |(a1 * q2 : ℤ) - (a2 * q1 : ℤ)| := by
      exact Int.one_le_abs h_int_neq
    have h_real_ge : (1 : ℝ) ≤ |((a1 * q2 : ℤ) - (a2 * q1 : ℤ) : ℝ)| := by exact_mod_cast h_int_ge
    have h_div_ge : 1 / (q1 * q2 : ℝ) ≤ |((a1 * q2 : ℤ) - (a2 * q1 : ℤ) : ℝ)| / (q1 * q2 : ℝ) := by
      exact div_le_div_of_nonneg_right h_real_ge h_pos_prod.le
    exact h_div_ge

  have hQ_pos2 : 0 ≤ Q / 2 := by
    by_cases h : 0 ≤ Q / 2
    · exact h
    · push Not at h
      have h_sqrt_zero : Real.sqrt (Q / 2) = 0 := Real.sqrt_eq_zero_of_nonpos h.le
      have h_prod_le_Q2 : (q1 : ℝ) * (q2 : ℝ) ≤ Real.sqrt (Q / 2) * Real.sqrt (Q / 2) :=
        mul_le_mul h_q1 h_q2 hq2_pos'.le (Real.sqrt_nonneg _)
      rw [h_sqrt_zero, mul_zero] at h_prod_le_Q2
      have : (0 : ℝ) < 0 := by linarith
      exact False.elim (lt_irrefl 0 this)

  have h_prod_le : (q1 * q2 : ℝ) ≤ Q / 2 := by
    calc
      (q1 * q2 : ℝ) = (q1 : ℝ) * (q2 : ℝ) := by ring_nf
      _ ≤ Real.sqrt (Q / 2) * Real.sqrt (Q / 2) := mul_le_mul h_q1 h_q2 hq2_pos'.le (Real.sqrt_nonneg _)
      _ = (Real.sqrt (Q / 2)) ^ 2 := by ring
      _ = Q / 2 := Real.sq_sqrt hQ_pos2

  have h_diff_ge_2 : 2 / Q ≤ |(a1 : ℝ) / q1 - (a2 : ℝ) / q2| := by
    calc
      2 / Q = 1 / (Q / 2) := by ring
      _ ≤ 1 / (q1 * q2 : ℝ) := by
        have ht : 0 < (q1 * q2 : ℝ) := by positivity
        exact one_div_le_one_div_of_le ht h_prod_le
      _ ≤ |(a1 : ℝ) / q1 - (a2 : ℝ) / q2| := h_diff_ge

  linarith

/-- The averaged pointwise model from displays 5.3 and 6.10, conditional on PerFractionApprox. -/
theorem sexp_major_approx (N : ℕ) (K : ℝ) (hpa : PerFractionApprox N K) :
    ∃ D u0 : ℝ, ∀ u : ℝ, u0 ≤ u → ∀ Z q a : ℕ, 0 < q →
      (q * q0 Z : ℝ) ≤ Real.log u ^ N → ∀ β : ℝ,
      ‖Sexp Z u ((a : ℝ) / q + β) -
        (1 / (q0 Z : ℂ)) * MajorArcs.inner Z q a * Tsum u β‖ ≤
        (#(R0 Z) : ℝ) * D * (1 + |β| * u) * u / Real.log u ^ K := by
  obtain ⟨D, u0, hD⟩ := hpa
  refine ⟨D, u0, ?_⟩
  intro u hu Z q a hq hqu β
  let E := D * (1 + |β| * u) * u / Real.log u ^ K
  have hq0 := q0_pos Z
  have hq0R : (0 : ℝ) < q0 Z := by exact_mod_cast hq0
  have herr : ∀ ℓ ∈ range (q0 Z),
      ‖Stil_alias u ((a : ℝ) / q + β + ℓ / q0 Z) -
        (muphi (qell Z q a ℓ) : ℂ) * Tsum u β‖ ≤ E := by
    intro ℓ hℓ
    obtain ⟨hdpos, hdle, hcop, hfrac⟩ := shifted_fraction_data Z q a ℓ hq
    let c := (a * q0 Z + ℓ * q) / Nat.gcd (a * q0 Z + ℓ * q) (q * q0 Z)
    have hdL : (qell Z q a ℓ : ℝ) ≤ Real.log u ^ N := by
      exact (by exact_mod_cast hdle : (qell Z q a ℓ : ℝ) ≤ (q : ℝ) * q0 Z).trans hqu
    have h := hD u hu (qell Z q a ℓ) c (by omega) hdL hcop β
    have hp : (a : ℝ) / q + β + ℓ / q0 Z = (c : ℝ) / qell Z q a ℓ + β := by
      dsimp [c]
      linarith [hfrac]
    have hm : (muphi (qell Z q a ℓ) : ℂ) =
        (ArithmeticFunction.moebius (qell Z q a ℓ) : ℂ) /
          ((qell Z q a ℓ).totient : ℂ) := by simp [muphi]
    simpa only [E, hp, hm, Stil_alias, LambdaSum, Iu, Iw] using h
  have hmodel : (1 / (q0 Z : ℂ)) * MajorArcs.inner Z q a * Tsum u β =
      (1 / (q0 Z : ℂ)) * ∑ ℓ ∈ range (q0 Z), ∑ r ∈ R0 Z,
        ee (-((ℓ : ℝ) * r / q0 Z)) * ((muphi (qell Z q a ℓ) : ℂ) * Tsum u β) := by
    unfold MajorArcs.inner
    simp only [sum_mul, mul_sum]
    refine sum_congr rfl fun ℓ _ => sum_congr rfl fun r _ => ?_
    ring
  rw [s_expansion Z u ((a : ℝ) / q + β), hmodel, ← mul_sub, ← sum_sub_distrib]
  simp only [← sum_sub_distrib, ← mul_sub]
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hsum : ‖∑ ℓ ∈ range (q0 Z), ∑ r ∈ R0 Z,
      ee (-((ℓ : ℝ) * r / q0 Z)) *
        (Stil_alias u ((a : ℝ) / q + β + ℓ / q0 Z) -
          (muphi (qell Z q a ℓ) : ℂ) * Tsum u β)‖ ≤
        (q0 Z : ℝ) * (#(R0 Z) : ℝ) * E := by
    calc
      _ ≤ ∑ ℓ ∈ range (q0 Z), ∑ r ∈ R0 Z, E := by
        refine norm_sum_le_of_le _ fun ℓ hℓ => norm_sum_le_of_le _ fun r hr => ?_
        rw [norm_mul, norm_ee, one_mul]
        exact herr ℓ hℓ
      _ = _ := by simp [sum_const, nsmul_eq_mul, mul_assoc]
  calc
    _ ≤ (1 / (q0 Z : ℝ)) * ((q0 Z : ℝ) * (#(R0 Z) : ℝ) * E) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp [E]; field_simp

/-- Translation of the cubic model on one arc, in the calculation before display 6.13. -/
theorem arc_model_integral (u Q t : ℝ) (m : ℕ) (c : ℂ) :
    (∫ α in (t - 1 / Q)..(t + 1 / Q),
      (c * Tsum u (α - t)) ^ 3 * ee (-(m * α))) =
      c ^ 3 * ee (-(m * t)) * SingInt u Q m := by
  have heq : (fun α : ℝ => (c * Tsum u (α - t)) ^ 3 * ee (-(m * α))) =
      fun α : ℝ => (c ^ 3 * ee (-(m * t))) * gInt u m (α - t) := by
    funext α
    unfold gInt
    rw [mul_pow]
    have he : ee (-(m * α)) = ee (-(m * t)) * ee (-(m * (α - t))) := by
      rw [← ee_add]
      congr 1
      ring
    rw [he]
    ring
  rw [heq, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right]
  rw [show t - 1 / Q - t = -(1 / Q) by ring,
    show t + 1 / Q - t = 1 / Q by ring]
  rfl

/-- The rational separation inequality used on page 6 after display 4.13. -/
theorem reduced_fraction_separation (q₁ a₁ q₂ a₂ : ℕ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hc₁ : a₁.Coprime q₁) (hc₂ : a₂.Coprime q₂)
    (hne : (q₁, a₁) ≠ (q₂, a₂)) :
    1 / (q₁ * q₂ : ℝ) ≤ |(a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂| := by
  have hrat : (a₁ : ℚ) / q₁ ≠ (a₂ : ℚ) / q₂ := by
    intro he
    have hi : ((a₁ : ℤ) : ℚ) / (q₁ : ℤ) = ((a₂ : ℤ) : ℚ) / (q₂ : ℤ) := by
      simpa only [Int.cast_natCast] using he
    have h := Rat.div_int_inj (by exact_mod_cast hq₁) (by exact_mod_cast hq₂)
      (by simpa using hc₁) (by simpa using hc₂) hi
    apply hne
    have ha : a₁ = a₂ := by exact_mod_cast h.1
    have hq : q₁ = q₂ := by exact_mod_cast h.2
    exact Prod.ext hq ha
  have hq₁R : (0 : ℝ) < q₁ := by exact_mod_cast hq₁
  have hq₂R : (0 : ℝ) < q₂ := by exact_mod_cast hq₂
  have hnum : (a₁ : ℤ) * q₂ - (a₂ : ℤ) * q₁ ≠ 0 := by
    intro hn
    apply hrat
    apply (div_eq_div_iff (by exact_mod_cast hq₁.ne') (by exact_mod_cast hq₂.ne')).mpr
    exact_mod_cast sub_eq_zero.mp hn
  have hnum1 : (1 : ℝ) ≤ |(((a₁ : ℤ) * q₂ - (a₂ : ℤ) * q₁ : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hnum
  rw [div_sub_div _ _ hq₁R.ne' hq₂R.ne', abs_div,
    abs_of_pos (mul_pos hq₁R hq₂R)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, mul_comm] using hnum1

/-- Closed major arcs are disjoint under the strict separation condition on page 6. -/
theorem closed_major_arc_disjoint (P Q : ℝ) (hPQ : 2 * P ^ 2 < Q)
    (q₁ a₁ q₂ a₂ : ℕ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hc₁ : a₁.Coprime q₁) (hc₂ : a₂.Coprime q₂)
    (hp₁ : (q₁ : ℝ) ≤ P) (hp₂ : (q₂ : ℝ) ≤ P)
    (hne : (q₁, a₁) ≠ (q₂, a₂)) :
    Disjoint (Set.Icc ((a₁ : ℝ) / q₁ - 1 / Q) ((a₁ : ℝ) / q₁ + 1 / Q))
      (Set.Icc ((a₂ : ℝ) / q₂ - 1 / Q) ((a₂ : ℝ) / q₂ + 1 / Q)) := by
  have hq₁R : (0 : ℝ) < q₁ := by exact_mod_cast hq₁
  have hq₂R : (0 : ℝ) < q₂ := by exact_mod_cast hq₂
  have hP : 0 < P := hq₁R.trans_le hp₁
  have hQ : 0 < Q := lt_of_le_of_lt (by positivity) hPQ
  have hprod : (q₁ * q₂ : ℝ) ≤ P ^ 2 := by
    simpa only [pow_two] using mul_le_mul hp₁ hp₂ hq₂R.le hP.le
  have hstrict : 2 / Q < 1 / (q₁ * q₂ : ℝ) := by
    rw [div_lt_div_iff₀ hQ (mul_pos hq₁R hq₂R)]
    nlinarith
  apply Set.disjoint_left.mpr
  intro x hx₁ hx₂
  have h₁ : |(a₁ : ℝ) / q₁ - x| ≤ 1 / Q := by
    rw [abs_le]
    constructor <;> linarith [hx₁.1, hx₁.2]
  have h₂ : |x - (a₂ : ℝ) / q₂| ≤ 1 / Q := by
    rw [abs_le]
    constructor <;> linarith [hx₂.1, hx₂.2]
  have hdist : |(a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂| ≤ 2 / Q := by
    calc
      _ ≤ |(a₁ : ℝ) / q₁ - x| + |x - (a₂ : ℝ) / q₂| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add h₁ h₂
      _ = _ := by ring
  have hsep := reduced_fraction_separation q₁ a₁ q₂ a₂ hq₁ hq₂ hc₁ hc₂ hne
  linarith

/-- The elementary cubic error bound used in display 6.12 on page 9. -/
theorem cube_error_bound (x y : ℂ) (E M : ℝ) (he : ‖x - y‖ ≤ E) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ‖x ^ 3 - y ^ 3‖ ≤ 3 * E * M ^ 2 := by
  have hM : 0 ≤ M := (norm_nonneg x).trans hx
  have hE : 0 ≤ E := (norm_nonneg (x - y)).trans he
  have hs : ‖x ^ 2 + x * y + y ^ 2‖ ≤ 3 * M ^ 2 := by
    calc
      _ ≤ ‖x ^ 2 + x * y‖ + ‖y ^ 2‖ := norm_add_le _ _
      _ ≤ (‖x ^ 2‖ + ‖x * y‖) + ‖y ^ 2‖ := add_le_add (norm_add_le _ _) le_rfl
      _ = ‖x‖ ^ 2 + ‖x‖ * ‖y‖ + ‖y‖ ^ 2 := by rw [norm_pow, norm_pow, norm_mul]
      _ ≤ M ^ 2 + M * M + M ^ 2 := by gcongr
      _ = _ := by ring
  rw [show x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) by ring, norm_mul]
  calc
    _ ≤ E * (3 * M ^ 2) := mul_le_mul he hs (norm_nonneg _) hE
    _ = _ := by ring

/-- The finite disjoint arc integral decomposition of display 6.1 on page 8. -/
theorem integral_majorArcs_eq_sum (f : ℝ → ℂ) (hf : Continuous f) (P Q : ℝ) (hP : 0 ≤ P)
    (hPQ : 2 * P ^ 2 < Q) :
    (∫ α in majorArcs P Q, f α) = ∑ q ∈ Icc 1 ⌊P⌋₊, ∑ a ∈ U q,
      ∫ α in ((a : ℝ) / q - 1 / Q)..((a : ℝ) / q + 1 / Q), f α := by
  let t := (Icc 1 ⌊P⌋₊).sigma U
  let s : (Σ _ : ℕ, ℕ) → Set ℝ := fun i =>
    Set.Icc ((i.2 : ℝ) / i.1 - 1 / Q) ((i.2 : ℝ) / i.1 + 1 / Q)
  have hunion : majorArcs P Q = ⋃ i ∈ t, s i := by
    dsimp [t, s]
    ext α
    simp only [majorArcs, Set.mem_ofPred_eq, Set.mem_iUnion, mem_sigma,
      U, mem_filter, mem_Icc, Set.mem_Icc]
    constructor
    · rintro ⟨q, hq, hqP, a, ha1, haq, hcop, hα⟩
      refine ⟨⟨q, a⟩, ⟨⟨hq, (Nat.le_floor_iff hP).mpr hqP⟩, ⟨ha1, haq⟩, hcop⟩, ?_⟩
      rw [abs_le] at hα
      constructor <;> linarith [hα.1, hα.2]
    · rintro ⟨⟨q, a⟩, ⟨⟨hq, hqP⟩, ⟨ha1, haq⟩, hcop⟩, hα1, hα2⟩
      refine ⟨q, hq, (Nat.le_floor_iff hP).mp hqP, a, ha1, haq, hcop, ?_⟩
      rw [abs_le]
      constructor <;> linarith
  have hd : Set.Pairwise (↑t) (fun i j => Disjoint (s i) (s j)) := by
    intro i hi j hj hij
    obtain ⟨hqi, hai⟩ := mem_sigma.mp hi
    obtain ⟨hqj, haj⟩ := mem_sigma.mp hj
    have hci := (mem_filter.mp hai).2
    have hcj := (mem_filter.mp haj).2
    apply closed_major_arc_disjoint P Q hPQ i.1 i.2 j.1 j.2
      (by have := (mem_Icc.mp hqi).1; omega) (by have := (mem_Icc.mp hqj).1; omega) hci hcj
      ((Nat.le_floor_iff hP).mp (mem_Icc.mp hqi).2)
      ((Nat.le_floor_iff hP).mp (mem_Icc.mp hqj).2)
    intro he
    apply hij
    exact Sigma.ext (congrArg Prod.fst he) (heq_of_eq (congrArg Prod.snd he))
  rw [hunion, integral_biUnion_finset t (fun _ _ => measurableSet_Icc) hd
    (fun _ _ => hf.continuousOn.integrableOn_Icc)]
  dsimp [t, s]
  rw [sum_sigma]
  refine sum_congr rfl fun q hq => sum_congr rfl fun a ha => ?_
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le]
  have hQ : 0 < Q := lt_of_le_of_lt (by positivity) hPQ
  linarith [one_div_pos.mpr hQ]

/-- Summing the pointwise cubic error over the disjoint arcs, as in display 6.13. -/
theorem major_arc_integral_error (f : ℝ → ℂ) (hf : Continuous f) (Z m : ℕ) (u P Q E : ℝ)
    (hP : 0 ≤ P) (hPQ : 2 * P ^ 2 < Q) (hEn : 0 ≤ E)
    (hE : ∀ q ∈ Icc 1 ⌊P⌋₊, ∀ a ∈ U q, ∀ α ∈
      Set.Icc ((a : ℝ) / q - 1 / Q) ((a : ℝ) / q + 1 / Q),
      ‖f α - (((1 / (q0 Z : ℂ)) * MajorArcs.inner Z q a) *
          Tsum u (α - (a : ℝ) / q)) ^ 3 * ee (-(m * α))‖ ≤ E) :
    ‖(∫ α in majorArcs P Q, f α) - SingP Z m P * SingInt u Q m‖ ≤
      2 * P ^ 2 / Q * E := by
  have hQ : 0 < Q := lt_of_le_of_lt (by positivity) hPQ
  have hmain : (∑ q ∈ Icc 1 ⌊P⌋₊, ∑ a ∈ U q,
      ∫ α in ((a : ℝ) / q - 1 / Q)..((a : ℝ) / q + 1 / Q),
        (((1 / (q0 Z : ℂ)) * MajorArcs.inner Z q a) *
          Tsum u (α - (a : ℝ) / q)) ^ 3 * ee (-(m * α))) =
        SingP Z m P * SingInt u Q m := by
    simp_rw [arc_model_integral]
    unfold SingP fq
    simp only [sum_mul, mul_sum, mul_pow, one_div_pow]
    refine sum_congr rfl fun q hq => sum_congr rfl fun a ha => ?_
    ring
  have hcount : (#((Icc 1 ⌊P⌋₊).sigma U) : ℝ) ≤ P ^ 2 := by
    have hn : #((Icc 1 ⌊P⌋₊).sigma U) ≤ ⌊P⌋₊ ^ 2 := by
      rw [card_sigma]
      calc
        _ = ∑ q ∈ Icc 1 ⌊P⌋₊, q.totient := sum_congr rfl (fun q hq => card_U q)
        _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, ⌊P⌋₊ := sum_le_sum (fun q hq => (Nat.totient_le q).trans (mem_Icc.mp hq).2)
        _ = _ := by simp [pow_two]
    calc
      _ ≤ (⌊P⌋₊ : ℝ) ^ 2 := by exact_mod_cast hn
      _ ≤ P ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hP) _
  rw [integral_majorArcs_eq_sum f hf P Q hP hPQ, ← hmain, ← sum_sub_distrib]
  simp only [← sum_sub_distrib]
  calc
    _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, ∑ a ∈ U q, E * (2 / Q) := by
      refine norm_sum_le_of_le _ fun q hq => norm_sum_le_of_le _ fun a ha => ?_
      have hcont : Continuous (fun α : ℝ =>
          (((1 / (q0 Z : ℂ)) * MajorArcs.inner Z q a) *
            Tsum u (α - (a : ℝ) / q)) ^ 3 * ee (-(m * α))) := by
        unfold Tsum ee
        fun_prop
      rw [← intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
      have hle : (a : ℝ) / q - 1 / Q ≤ a / q + 1 / Q := by
        linarith [one_div_pos.mpr hQ]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (a : ℝ) / q - 1 / Q) (b := (a : ℝ) / q + 1 / Q)
        (f := fun α : ℝ => f α - (((1 / (q0 Z : ℂ)) * MajorArcs.inner Z q a) *
          Tsum u (α - (a : ℝ) / q)) ^ 3 * ee (-(m * α)))
        (C := E) (by
          intro α hα
          rw [Set.uIoc_of_le hle] at hα
          exact hE q hq a ha α ⟨hα.1.le, hα.2⟩)
      simpa only [show (a : ℝ) / q + 1 / Q - ((a : ℝ) / q - 1 / Q) = 2 / Q by ring,
        abs_of_pos (show (0 : ℝ) < 2 / Q from div_pos (by norm_num) hQ)] using hb
    _ = (#((Icc 1 ⌊P⌋₊).sigma U) : ℝ) * (2 / Q) * E := by
      rw [← sum_sigma (f := fun _ : Σ _ : ℕ, ℕ => E * (2 / Q))]
      simp only [sum_const, nsmul_eq_mul]
      ring
    _ ≤ P ^ 2 * (2 / Q) * E := by gcongr
    _ = _ := by ring

/-- Explicit common size bounds for S and its major arc model in display 6.12. -/
theorem major_model_size (Z q a : ℕ) (u α β : ℝ) (hu : 1 ≤ u) :
    ‖Sexp Z u α‖ ≤ (q0 Z : ℝ) * (⌊2 * u⌋₊ + 1) * (Real.log (2 * u) + 1) ∧
    ‖(1 / (q0 Z : ℂ)) * MajorArcs.inner Z q a * Tsum u β‖ ≤
      (q0 Z : ℝ) * (⌊2 * u⌋₊ + 1) * (Real.log (2 * u) + 1) := by
  have hq0 := q0_pos Z
  have hq0R : (0 : ℝ) < q0 Z := by exact_mod_cast hq0
  have hq01 : (1 : ℝ) ≤ q0 Z := by exact_mod_cast hq0
  have hlog : 0 ≤ Real.log (2 * u) := Real.log_nonneg (by linarith)
  have hT : ‖Tsum u β‖ ≤ (⌊2 * u⌋₊ : ℝ) + 1 := by
    have hc : #(Iw u) ≤ ⌊2 * u⌋₊ + 1 := by simp only [Iw, Nat.card_Icc]; omega
    calc
      _ ≤ ∑ k ∈ Iw u, (1 : ℝ) := norm_sum_le_of_le _ (by intro k hk; rw [norm_ee])
      _ = (#(Iw u) : ℝ) := by simp
      _ ≤ _ := by exact_mod_cast hc
  constructor
  · calc
      _ ≤ ∑ k ∈ Aset Z u, Real.log (2 * u) := by
        refine norm_sum_le_of_le _ fun k hk => ?_
        rw [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact LeanLab.SparseTernary.RepAssembly.vM_le hu hk
      _ = (#(Aset Z u) : ℝ) * Real.log (2 * u) := by simp
      _ ≤ ((⌊2 * u⌋₊ : ℝ) + 1) * Real.log (2 * u) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast LeanLab.SparseTernary.RepAssembly.card_Aset_le Z u) hlog
      _ = 1 * ((⌊2 * u⌋₊ : ℝ) + 1) * Real.log (2 * u) := by ring
      _ ≤ _ := by gcongr; linarith
  · calc
      _ = (1 / (q0 Z : ℝ)) * ‖MajorArcs.inner Z q a‖ * ‖Tsum u β‖ := by
        rw [norm_mul, norm_mul, norm_div, norm_one, Complex.norm_natCast]
      _ ≤ (1 / (q0 Z : ℝ)) * ((q0 Z : ℝ) * q0 Z) * ((⌊2 * u⌋₊ : ℝ) + 1) := by
        gcongr
        exact norm_inner_le Z q a
      _ = (q0 Z : ℝ) * ((⌊2 * u⌋₊ : ℝ) + 1) := by field_simp
      _ ≤ _ := by
        have hnonneg : (0 : ℝ) ≤ (q0 Z : ℝ) * ((⌊2 * u⌋₊ : ℝ) + 1) := by positivity
        nlinarith [mul_nonneg hnonneg hlog]

/-- An explicit integrated bound from the per-fraction input, for the route to display 6.13. -/
theorem arc_bound_from_per_fraction (N : ℕ) (K : ℝ) (hpa : PerFractionApprox N K) :
    ∃ D u0 : ℝ, 0 ≤ D ∧ ∀ u : ℝ, u0 ≤ u → ∀ Z m : ℕ, ∀ P Q : ℝ,
      0 ≤ P → 2 * P ^ 2 < Q → P * q0 Z ≤ Real.log u ^ N →
      ‖(∫ α in majorArcs P Q, Sexp Z u α ^ 3 * ee (-(m * α))) -
          SingP Z m P * SingInt u Q m‖ ≤
        6 * D * P ^ 2 / Q * (#(R0 Z) : ℝ) * (1 + u / Q) * u / Real.log u ^ K *
          ((q0 Z : ℝ) * (⌊2 * u⌋₊ + 1) * (Real.log (2 * u) + 1)) ^ 2 := by
  obtain ⟨D, u0, hD⟩ := sexp_major_approx N K hpa
  refine ⟨|D|, max u0 (Real.exp 1), abs_nonneg _, ?_⟩
  intro u hu Z m P Q hP hPQ hmod
  have huu0 : u0 ≤ u := (le_max_left _ _).trans hu
  have hue : Real.exp 1 ≤ u := (le_max_right _ _).trans hu
  have hu1 : 1 ≤ u := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hue
  have hu0 : 0 < u := by linarith
  have hL : 0 < Real.log u := by
    have := Real.log_le_log (Real.exp_pos 1) hue
    rw [Real.log_exp] at this
    linarith
  have hQ : 0 < Q := lt_of_le_of_lt (by positivity) hPQ
  let R := (q0 Z : ℝ) * (⌊2 * u⌋₊ + 1) * (Real.log (2 * u) + 1)
  let E := (#(R0 Z) : ℝ) * |D| * (1 + u / Q) * u / Real.log u ^ K
  have hEn : 0 ≤ E := by dsimp [E]; positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * u)
    positivity
  have hf : Continuous (fun α : ℝ => Sexp Z u α ^ 3 * ee (-(m * α))) :=
    LeanLab.SparseTernary.RepAssembly.continuous_F Z u m
  have hi := major_arc_integral_error _ hf Z m u P Q (3 * E * R ^ 2) hP hPQ
    (by positivity) (by
      intro q hq a ha α hα
      have hqp : (q : ℝ) ≤ P := (Nat.le_floor_iff hP).mp (mem_Icc.mp hq).2
      have hqq : (q : ℝ) * q0 Z ≤ Real.log u ^ N :=
        (mul_le_mul_of_nonneg_right hqp (Nat.cast_nonneg _)).trans hmod
      have hq0 : 0 < q := by have := (mem_Icc.mp hq).1; omega
      let β := α - (a : ℝ) / q
      have hb : |β| ≤ 1 / Q := by
        rw [abs_le]
        dsimp [β]
        constructor <;> linarith [hα.1, hα.2]
      have hs := hD u huu0 Z q a hq0 hqq β
      have hαeq : (a : ℝ) / q + β = α := by dsimp [β]; ring
      rw [hαeq] at hs
      have hse : ‖Sexp Z u α - (1 / (q0 Z : ℂ)) * MajorArcs.inner Z q a * Tsum u β‖ ≤ E := by
        calc
          _ ≤ (#(R0 Z) : ℝ) * D * (1 + |β| * u) * u / Real.log u ^ K := hs
          _ ≤ (#(R0 Z) : ℝ) * |D| * (1 + |β| * u) * u / Real.log u ^ K := by
            gcongr
            exact le_abs_self D
          _ ≤ E := by
            dsimp [E]
            gcongr
            calc |β| * u ≤ (1 / Q) * u := mul_le_mul_of_nonneg_right hb hu0.le
              _ = u / Q := by ring
      obtain ⟨hS, hM⟩ := major_model_size Z q a u α β hu1
      have hc := cube_error_bound (Sexp Z u α)
        ((1 / (q0 Z : ℂ)) * MajorArcs.inner Z q a * Tsum u β) E R hse hS hM
      change ‖Sexp Z u α ^ 3 * ee (-(m * α)) -
        ((1 / (q0 Z : ℂ)) * MajorArcs.inner Z q a * Tsum u β) ^ 3 * ee (-(m * α))‖ ≤ _
      rw [← sub_mul, norm_mul, norm_ee, mul_one]
      exact hc)
  calc
    _ ≤ 2 * P ^ 2 / Q * (3 * E * R ^ 2) := hi
    _ = _ := by dsimp [E, R]; ring

/-- A coarse logarithmic bound from the existing q0 square bound, for display 4.3. -/
theorem q0_log_pow5 (A : ℕ) (u : ℝ) (hL : 1 ≤ Real.log u) :
    (q0 (Zof A u) : ℝ) ≤ Real.log u ^ (5 * A) := by
  have hs := q0_sq_le A u hL
  rw [show (9 * (A : ℝ)) = ((9 * A : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at hs
  have hm : Real.log u ^ (9 * A) ≤ Real.log u ^ (10 * A) :=
    pow_le_pow_right₀ hL (by omega)
  have he : Real.log u ^ (10 * A) = (Real.log u ^ (5 * A)) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [he] at hm
  have hn : 0 ≤ Real.log u ^ (5 * A) := by positivity
  nlinarith

/-- Display 6.13 from any per-fraction saving at least 3A + 5B + 2. -/
theorem arc613_of_per_fraction_saving (A B K : ℕ) (hK : 3 * A + 5 * B + 2 ≤ K)
    (hpa : PerFractionApprox (B + 5 * A) (K : ℝ)) : Arc613 A B := by
  obtain ⟨D, u0, hDn, hD⟩ := arc_bound_from_per_fraction (B + 5 * A) (K : ℝ) hpa
  have hsmall : ∀ᶠ u : ℝ in atTop, 2 * Real.log u ^ (3 * B) < u := by
    filter_upwards [(isLittleO_pow_log_id_atTop (n := 3 * B)).bound
      (by norm_num : (0 : ℝ) < 1 / 4), eventually_ge_atTop (1 : ℝ)] with u hu hu1
    simp only [Real.norm_eq_abs, id_eq, abs_of_pos (by linarith : 0 < u)] at hu
    have := le_abs_self (Real.log u ^ (3 * B))
    linarith
  obtain ⟨v0, hv0⟩ := hsmall.exists_forall_of_atTop
  intro ε hε
  refine ⟨972 * D, max u0 (max v0 (Real.exp 1)), ?_⟩
  intro u hu m hm1 hm2
  have huu0 : u0 ≤ u := (le_max_left _ _).trans hu
  have huv0 : v0 ≤ u := (le_max_left _ _).trans ((le_max_right _ _).trans hu)
  have hue : Real.exp 1 ≤ u := (le_max_right _ _).trans ((le_max_right _ _).trans hu)
  have hu1 : 1 ≤ u := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hue
  have hu0 : 0 < u := by linarith
  have hL : 1 ≤ Real.log u := by
    have := Real.log_le_log (Real.exp_pos 1) hue
    simpa only [Real.log_exp] using this
  let L := Real.log u
  let Z := Zof A u
  let P := L ^ B
  let Q := u / P
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hP1 : 1 ≤ P := one_le_pow₀ hL
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  have hQ0 : 0 < Q := div_pos hu0 hP0
  have hPQ : 2 * P ^ 2 < Q := by
    apply (lt_div_iff₀ hP0).mpr
    have hv := hv0 u huv0
    have hp : P ^ 2 * P = L ^ (3 * B) := by dsimp [P]; rw [← pow_succ, ← pow_mul]; congr 1; omega
    nlinarith
  have hq0 : (q0 Z : ℝ) ≤ L ^ (5 * A) := q0_log_pow5 A u hL
  have hcard : (#(R0 Z) : ℝ) ≤ L ^ (5 * A) :=
    (by exact_mod_cast card_R0_le_q0 Z : (#(R0 Z) : ℝ) ≤ q0 Z).trans hq0
  have hmod : P * q0 Z ≤ L ^ (B + 5 * A) := by
    calc
      _ ≤ P * L ^ (5 * A) := mul_le_mul_of_nonneg_left hq0 hP0.le
      _ = _ := by dsimp [P]; rw [pow_add]
  have hf : (⌊2 * u⌋₊ : ℝ) + 1 ≤ 3 * u := by
    have := Nat.floor_le (by linarith : 0 ≤ 2 * u)
    linarith
  have hlog : Real.log (2 * u) + 1 ≤ 3 * L := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hu0.ne']
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    dsimp [L]
    linarith
  have hM : (q0 Z : ℝ) * (⌊2 * u⌋₊ + 1) * (Real.log (2 * u) + 1) ≤
      9 * u * L ^ (5 * A + 1) := by
    have hlogn : 0 ≤ Real.log (2 * u) + 1 := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * u)
      linarith
    calc
      _ ≤ L ^ (5 * A) * (3 * u) * (3 * L) := by gcongr
      _ = _ := by rw [pow_succ]; ring
  have hquot : 1 + u / Q ≤ 2 * P := by
    have he : u / Q = P := by dsimp [Q]; field_simp
    rw [he]
    linarith
  have hi := hD u huu0 Z m P Q hP0.le hPQ hmod
  rw [Real.rpow_natCast] at hi
  have hMnonneg : 0 ≤ (q0 Z : ℝ) * (⌊2 * u⌋₊ + 1) * (Real.log (2 * u) + 1) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * u)
    positivity
  have hbound : 6 * D * P ^ 2 / Q * (#(R0 Z) : ℝ) * (1 + u / Q) * u / L ^ K *
      ((q0 Z : ℝ) * (⌊2 * u⌋₊ + 1) * (Real.log (2 * u) + 1)) ^ 2 ≤
        972 * D * u ^ 2 * L ^ (15 * A + 4 * B + 2) / L ^ K := by
    calc
      _ ≤ 6 * D * P ^ 2 / Q * L ^ (5 * A) * (2 * P) * u / L ^ K *
          (9 * u * L ^ (5 * A + 1)) ^ 2 := by gcongr
      _ = _ := by
        have hp (n c : ℕ) : L ^ (c * n) = (L ^ n) ^ c := by rw [Nat.mul_comm c n, pow_mul]
        dsimp [P, Q]
        field_simp
        simp only [pow_add, hp, pow_one]
        ring
  have hratio : L ^ (15 * A + 4 * B + 2) / L ^ K ≤ L ^ (12 * A) / L ^ B := by
    rw [div_le_div_iff₀ (pow_pos hL0 _) (pow_pos hL0 _)]
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hL (by omega)
  have hrpow : L ^ (12 * A) / L ^ B = L ^ (12 * (A : ℝ) - B) := by
    rw [Real.rpow_sub hL0]
    rw [show (12 * (A : ℝ)) = ((12 * A : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, Real.rpow_natCast]
  calc
    _ ≤ 972 * D * u ^ 2 * L ^ (15 * A + 4 * B + 2) / L ^ K := hi.trans hbound
    _ ≤ 972 * D * u ^ 2 * L ^ (12 * (A : ℝ) - B) := by
      rw [mul_div_assoc, ← hrpow]
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ 972 * D * u ^ 2 * L ^ (12 * (A : ℝ) - B + ε) := by
      gcongr
      linarith

/-- Display 6.13 derived directly from SW with arbitrary per-fraction saving. -/
theorem arc613_of_sw (A B : ℕ) (hSW : SW (B + 5 * A + 1)) : Arc613 A B := by
  have hpa := per_fraction_of_sw (B + 5 * A) hSW
    ((3 * A + 5 * B + 2 : ℕ) : ℝ) (by positivity)
  exact arc613_of_per_fraction_saving A B (3 * A + 5 * B + 2) le_rfl hpa

theorem Arc613FromSWProp_assembly (A B : ℕ) : Arc613FromSWProp A B := by
  intro hSW
  exact arc613_of_sw A B hSW

/-- Display 6.18 with SW as the only analytic input on the major arc side. -/
theorem major618_from_sw (A B : ℕ) (hB : 15 * A ≤ B)
    (hSW : SW (B + 5 * A + 1)) : Major618 A B :=
  major618_of_arc613 A B hB (arc613_of_sw A B hSW)

/-- The representation conclusion with the major arc side reduced to SW. -/
theorem repProp_from_sw (A B : ℕ) (hA : 1 ≤ A)
    (hB1 : 36 * A + 3 ≤ B) (hB2 : 28 * A + 13 ≤ B)
    (hminor : LeanLab.SparseTernary.RepAssembly.Minor516W A B)
    (hSW : SW (B + 5 * A + 1)) : RepProp A :=
  repProp_of_arc613 A B hA hB1 hB2 hminor (arc613_of_sw A B hSW)

/-- The denominator comparison of display 5.9, including the equal fraction case. -/
theorem nearby_denominator_sqrt (q r : ℚ) (α γ : ℝ) (hγ : 1 ≤ γ)
    (hαq : |α - (q : ℝ)| ≤ γ / (q.den : ℝ) ^ 2)
    (hαr : |α - (r : ℝ)| ≤ 1 / (2 * (q.den : ℝ) * r.den)) :
    1 / Real.sqrt (r.den : ℝ) ≤ Real.sqrt (2 * γ) / Real.sqrt (q.den : ℝ) := by
  have hqR : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hrR : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hγ0 : 0 < γ := by linarith
  have hden : (q.den : ℝ) ≤ 2 * γ * r.den := by
    by_cases heq : q = r
    · subst r
      nlinarith
    · have hnum : q.num * r.den - r.num * q.den ≠ 0 := by
        intro hn
        apply heq
        exact Rat.eq_iff_mul_eq_mul.mpr (sub_eq_zero.mp hn)
      have hnum1 : (1 : ℝ) ≤ |((q.num * r.den - r.num * q.den : ℤ) : ℝ)| := by
        exact_mod_cast Int.one_le_abs hnum
      have hs : 1 / ((q.den : ℝ) * r.den) ≤ |(q : ℝ) - (r : ℝ)| := by
        rw [Rat.cast_def q, Rat.cast_def r,
          div_sub_div _ _ hqR.ne' hrR.ne', abs_div, abs_of_pos (mul_pos hqR hrR)]
        apply div_le_div_of_nonneg_right _ (by positivity)
        simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, mul_comm] using hnum1
      have hd : |(q : ℝ) - (r : ℝ)| ≤
          γ / (q.den : ℝ) ^ 2 + 1 / (2 * (q.den : ℝ) * r.den) := by
        calc
          _ ≤ |(q : ℝ) - α| + |α - (r : ℝ)| := abs_sub_le _ _ _
          _ = |α - (q : ℝ)| + |α - (r : ℝ)| := by rw [abs_sub_comm (q : ℝ) α]
          _ ≤ _ := add_le_add hαq hαr
      have hh : 1 / (2 * (q.den : ℝ) * r.den) ≤ γ / (q.den : ℝ) ^ 2 := by
        have he : 1 / ((q.den : ℝ) * r.den) = 2 * (1 / (2 * (q.den : ℝ) * r.den)) := by ring
        rw [he] at hs
        linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)] at hh
      apply (mul_le_mul_iff_left₀ hqR).mp
      nlinarith
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hrR) (Real.sqrt_pos.mpr hqR)]
  simp only [one_mul]
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hden

/-- Lemma 5.2, conditional on the pointwise Vinogradov bound of Lemma 5.1. -/
theorem lemma52_from_vinogradov (u α γ C : ℝ) (q : ℚ) (hu : 1 ≤ u) (hγ : 1 ≤ γ) (hC : 0 ≤ C)
    (hαq : |α - (q : ℝ)| ≤ γ / (q.den : ℝ) ^ 2)
    (hV : ∀ r : ℚ, |α - (r : ℝ)| ≤ 1 / (r.den : ℝ) ^ 2 →
      ‖∑ k ∈ Icc 1 ⌊u⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ) * ee (k * α)‖ ≤
        C * (u / Real.sqrt r.den + u ^ (4 / 5 : ℝ) + Real.sqrt u * Real.sqrt r.den) *
          Real.log u ^ 4) :
    ‖∑ k ∈ Icc 1 ⌊u⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ) * ee (k * α)‖ ≤
      (Real.sqrt 2 * C) *
        (Real.sqrt γ * u / Real.sqrt q.den + u ^ (4 / 5 : ℝ) + Real.sqrt u * Real.sqrt q.den) *
          Real.log u ^ 4 := by
  have hqp := q.pos
  obtain ⟨r, hr, hrden⟩ := Real.exists_rat_abs_sub_le_and_den_le α
    (n := 2 * q.den) (by omega)
  have hqR : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hrR : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hrdenR : (r.den : ℝ) ≤ 2 * q.den := by exact_mod_cast hrden
  have hnear : |α - (r : ℝ)| ≤ 1 / (2 * (q.den : ℝ) * r.den) := by
    refine hr.trans (one_div_le_one_div_of_le (by positivity) ?_)
    push_cast
    nlinarith
  have hnear2 : |α - (r : ℝ)| ≤ 1 / (r.den : ℝ) ^ 2 := by
    refine hnear.trans (one_div_le_one_div_of_le (by positivity) ?_)
    nlinarith
  have hs := nearby_denominator_sqrt q r α γ hγ hαq hnear
  have hu0 : 0 ≤ u := by linarith
  have hfirst : u / Real.sqrt r.den ≤ Real.sqrt (2 * γ) * u / Real.sqrt q.den := by
    convert mul_le_mul_of_nonneg_left hs hu0 using 1 <;> ring
  have hlast : Real.sqrt u * Real.sqrt r.den ≤ Real.sqrt u * Real.sqrt (2 * (q.den : ℝ)) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrdenR) (Real.sqrt_nonneg _)
  have h2 : 1 ≤ Real.sqrt (2 : ℝ) := by norm_num
  have hmiddle : u ^ (4 / 5 : ℝ) ≤ Real.sqrt 2 * u ^ (4 / 5 : ℝ) :=
    le_mul_of_one_le_left (Real.rpow_nonneg hu0 _) h2
  have hbr : Real.sqrt (2 * γ) * u / Real.sqrt q.den + u ^ (4 / 5 : ℝ) +
      Real.sqrt u * Real.sqrt (2 * (q.den : ℝ)) ≤
      Real.sqrt 2 * (Real.sqrt γ * u / Real.sqrt q.den + u ^ (4 / 5 : ℝ) +
        Real.sqrt u * Real.sqrt q.den) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    linear_combination hmiddle
  calc
    _ ≤ C * (u / Real.sqrt r.den + u ^ (4 / 5 : ℝ) + Real.sqrt u * Real.sqrt r.den) *
        Real.log u ^ 4 := hV r hnear2
    _ ≤ C * (Real.sqrt (2 * γ) * u / Real.sqrt q.den + u ^ (4 / 5 : ℝ) +
        Real.sqrt u * Real.sqrt (2 * (q.den : ℝ))) * Real.log u ^ 4 := by gcongr
    _ ≤ C * (Real.sqrt 2 * (Real.sqrt γ * u / Real.sqrt q.den + u ^ (4 / 5 : ℝ) +
        Real.sqrt u * Real.sqrt q.den)) * Real.log u ^ 4 := by gcongr
    _ = _ := by ring

/-- The coarse fixed-saving upper bound cannot be absorbed at the desired exponent in this range. -/
theorem fixed_saving_coarse_bound_insufficient (A B : ℕ) (ε : ℝ) (hgap : 9 * (A : ℝ) + ε < 5 * B + 2) :
    ¬ ∃ C : ℝ, ∀ L : ℝ, 1 ≤ L →
      L ^ (3 * (A : ℝ) + 4 * B + 2) ≤ C * L ^ (12 * (A : ℝ) - B + ε) := by
  rintro ⟨C, hC⟩
  let d := (3 * (A : ℝ) + 4 * B + 2) - (12 * (A : ℝ) - B + ε)
  have hd : 0 < d := by dsimp [d]; linarith
  have hg : ∀ᶠ L : ℝ in atTop, C < L ^ d :=
    (tendsto_rpow_atTop hd).eventually (eventually_gt_atTop C)
  obtain ⟨L, hL, hlarge⟩ := ((eventually_ge_atTop (1 : ℝ)).and hg).exists
  have hL0 : 0 < L := by linarith
  have h := hC L hL
  have hden : 0 < L ^ (12 * (A : ℝ) - B + ε) := Real.rpow_pos_of_pos hL0 _
  have hh : L ^ (3 * (A : ℝ) + 4 * B + 2) / L ^ (12 * (A : ℝ) - B + ε) ≤ C :=
    (div_le_iff₀ hden).mpr h
  rw [← Real.rpow_sub hL0] at hh
  exact (not_lt_of_ge hh) hlarge

/-- The fixed saving of the remaining leaf suffices in this explicit parameter range. -/
theorem arc613_of_fixed_saving_small_B (A B : ℕ) (hsmall : 5 * B + 2 ≤ 9 * A)
    (hpa : PerFractionApprox (B + 5 * A) (12 * A)) : Arc613 A B := by
  have hpa' : PerFractionApprox (B + 5 * A) ((12 * A : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hpa
  exact arc613_of_per_fraction_saving A B (12 * A) (by omega) hpa'

/-- LEAF: integration over major arcs reaching 6.13. -/
theorem arc_integration_613 (A B : ℕ) (h_per_frac : PerFractionApprox (B + 5 * A) (12 * A))
    (h_s_exp : ∀ Z u α, Sexp Z u α = (1 / (q0 Z : ℂ)) * ∑ ℓ ∈ range (q0 Z), ∑ r ∈ R0 Z,
      ee (-((ℓ : ℝ) * r / q0 Z)) * Stil_alias u (α + ℓ / q0 Z))
    (h_cube : ∀ Z u α, Sexp Z u α ^ 3 = (1 / (q0 Z : ℂ) ^ 3) * ∑ ℓ₁ ∈ range (q0 Z), ∑ r₁ ∈ R0 Z,
      ∑ ℓ₂ ∈ range (q0 Z), ∑ r₂ ∈ R0 Z, ∑ ℓ₃ ∈ range (q0 Z), ∑ r₃ ∈ R0 Z,
      ee (-((ℓ₁ * r₁ + ℓ₂ * r₂ + ℓ₃ * r₃ : ℝ) / q0 Z)) *
      Stil_alias u (α + ℓ₁ / q0 Z) * Stil_alias u (α + ℓ₂ / q0 Z) * Stil_alias u (α + ℓ₃ / q0 Z))
    (h_disjoint : ∀ Q : ℝ, ∀ q₁ a₁ q₂ a₂ : ℕ, a₁ < q₁ → a₂ < q₂ → a₁.Coprime q₁ → a₂.Coprime q₂ →
      (q₁ : ℝ) ≤ Real.sqrt (Q / 2) → (q₂ : ℝ) ≤ Real.sqrt (Q / 2) →
      (q₁ ≠ q₂ ∨ a₁ ≠ a₂) →
      Disjoint (Set.Ioo ((a₁ : ℝ) / q₁ - 1 / Q) ((a₁ : ℝ) / q₁ + 1 / Q))
               (Set.Ioo ((a₂ : ℝ) / q₂ - 1 / Q) ((a₂ : ℝ) / q₂ + 1 / Q))) :
    Arc613 A B := by
  by_cases hsmall : 5 * B + 2 ≤ 9 * A
  · exact arc613_of_fixed_saving_small_B A B hsmall h_per_frac
  · -- The remaining LEAF is the unrestricted parameter range.
    sorry

/-- Lemma 3.1 from the existing size theorem, the minor arc input and SW. -/
theorem lemma31_from_minor_and_sw (A B : ℕ) (hA : 1 ≤ A)
    (hB1 : 36 * A + 3 ≤ B) (hB2 : 28 * A + 13 ≤ B)
    (hminor : LeanLab.SparseTernary.RepAssembly.Minor516W A B)
    (hSW : SW (B + 5 * A + 1)) : Lemma31 A :=
  lemma31_of_props A (LeanLab.SparseTernary.SizeProof.sizeProp A hA)
    (repProp_from_sw A B hA hB1 hB2 hminor hSW)

/-- Theorem 1.1 from the remaining minor arc, SW and ternary Goldbach inputs. -/
theorem theorem11_from_minor_and_sw
    (hminor : ∀ A : ℕ, 0 < A → LeanLab.SparseTernary.RepAssembly.Minor516W A (41 * A))
    (hSW : ∀ A : ℕ, 0 < A → SW (46 * A + 1))
    (hT : TernaryGoldbach) : Theorem11 := by
  apply LeanLab.SparseTernary.Gluing.theorem11_of_lemma31 ?_ hT
  intro A hA
  apply lemma31_from_minor_and_sw A (41 * A) (by omega) (by omega) (by omega) (hminor A hA)
  simpa only [show 41 * A + 5 * A + 1 = 46 * A + 1 by omega] using hSW A hA

end LeanLab.SparseTernary.DecompJ269

#print axioms LeanLab.SparseTernary.DecompJ269.s_expansion

#print axioms LeanLab.SparseTernary.DecompJ269.s_cube_expansion

#print axioms LeanLab.SparseTernary.DecompJ269.ramanujan_at_unit

#print axioms LeanLab.SparseTernary.DecompJ269.prime_residue_expansion

#print axioms LeanLab.SparseTernary.DecompJ269.reduced_phase_sum

#print axioms LeanLab.SparseTernary.DecompJ269.prime_fraction_approx

#print axioms LeanLab.SparseTernary.DecompJ269.prime_power_difference_bound

#print axioms LeanLab.SparseTernary.DecompJ269.prime_power_error_small

#print axioms LeanLab.SparseTernary.DecompJ269.per_fraction_of_sw

#print axioms LeanLab.SparseTernary.DecompJ269.per_fraction_approx

#print axioms LeanLab.SparseTernary.DecompJ269.shifted_fraction_data

#print axioms LeanLab.SparseTernary.DecompJ269.sexp_major_approx

#print axioms LeanLab.SparseTernary.DecompJ269.arc_model_integral

#print axioms LeanLab.SparseTernary.DecompJ269.reduced_fraction_separation

#print axioms LeanLab.SparseTernary.DecompJ269.closed_major_arc_disjoint

#print axioms LeanLab.SparseTernary.DecompJ269.cube_error_bound

#print axioms LeanLab.SparseTernary.DecompJ269.integral_majorArcs_eq_sum

#print axioms LeanLab.SparseTernary.DecompJ269.major_arc_integral_error

#print axioms LeanLab.SparseTernary.DecompJ269.major_model_size

#print axioms LeanLab.SparseTernary.DecompJ269.arc_bound_from_per_fraction

#print axioms LeanLab.SparseTernary.DecompJ269.q0_log_pow5

#print axioms LeanLab.SparseTernary.DecompJ269.arc613_of_sw

#print axioms LeanLab.SparseTernary.DecompJ269.Arc613FromSWProp_assembly

#print axioms LeanLab.SparseTernary.DecompJ269.major618_from_sw

#print axioms LeanLab.SparseTernary.DecompJ269.repProp_from_sw

#print axioms LeanLab.SparseTernary.DecompJ269.nearby_denominator_sqrt

#print axioms LeanLab.SparseTernary.DecompJ269.lemma52_from_vinogradov

#print axioms LeanLab.SparseTernary.DecompJ269.fixed_saving_coarse_bound_insufficient

#print axioms LeanLab.SparseTernary.DecompJ269.arc613_of_per_fraction_saving

#print axioms LeanLab.SparseTernary.DecompJ269.arc613_of_fixed_saving_small_B

#print axioms LeanLab.SparseTernary.DecompJ269.lemma31_from_minor_and_sw

#print axioms LeanLab.SparseTernary.DecompJ269.theorem11_from_minor_and_sw
