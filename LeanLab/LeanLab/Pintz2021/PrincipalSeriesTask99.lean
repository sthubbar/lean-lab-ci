import LeanLab.Pintz2021.CharacterSumsTask53
import LeanLab.Pintz2021.Applications
import LeanLab.PerelliPintz1992.Decomp1519

/-!
P0054 page 6, the paragraph after display 2.9.
The principal-character specialization recovers the classical singular series.
The general conductor-dependent estimate remains a separate analytic problem.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.PrincipalSeriesTask99

open Finset CharacterSumsTask53
open LeanLab.PNTPort.LargeSieve

attribute [local instance] Classical.propDecidable

/-- The principal finite character sum is the existing Ramanujan sum. -/
theorem principal_eq_ram (q : ℕ) (m : ℤ) :
    characterSum (principalValue q) q m =
      LeanLab.PerelliPintz1992.Decomp1519.ram q m := by
  unfold characterSum principalValue LeanLab.PerelliPintz1992.Decomp1519.ram
    LeanLab.PerelliPintz1992.Decomp1519.As
  rw [sum_filter]
  apply sum_congr rfl
  intro a _
  split_ifs with h
  · simp only [one_mul]
    unfold e LeanLab.PerelliPintz1992.e
    congr 1
    push_cast
    ring
  · simp

/-- The principal Gauss sum is the Mobius function, at every natural modulus. -/
theorem gauss_principal (q : ℕ) :
    CharacterSumsTask53.gaussSum (principalValue q) q = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  by_cases hq0 : q = 0
  · subst q
    simp [CharacterSumsTask53.gaussSum, characterSum]
  by_cases hq1 : q = 1
  · subst q
    have he1 : e (1 : ℝ) = 1 := by simpa using e_int (1 : ℤ)
    simp [CharacterSumsTask53.gaussSum, characterSum, principalValue, he1]
  have hsets : (Icc 1 q).filter (fun b => Nat.Coprime b q) =
      (range q).filter (fun b => Nat.Coprime b q) := by
    ext b
    simp only [mem_filter, mem_Icc, mem_range]
    by_cases hb0 : b = 0
    · subst b
      simp [Nat.coprime_zero_left, hq1]
    · by_cases hbq : b = q
      · subst b
        simp [Nat.coprime_self, hq1]
      · omega
  unfold CharacterSumsTask53.gaussSum characterSum principalValue
  simp only [ite_mul, one_mul, zero_mul]
  rw [← sum_filter, hsets]
  calc
    _ = ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
        LeanLab.PerelliPintz1992.e ((1 : ℝ) * b / q) := by
      apply sum_congr rfl
      intro b _
      unfold e LeanLab.PerelliPintz1992.e
      congr 1
      push_cast
      ring
    _ = _ := by
      simpa using (LeanLab.PerelliPintz1992.Decomp1519.ramanujan_coprime
        (by omega : 1 ≤ q) (by simp : Nat.Coprime 1 q))

/-- Both principal coefficient templates are the classical Ramanujan coefficient. -/
theorem principal_coefficient (q : ℕ) (m : ℤ) (difference : Bool) :
    generalizedCoeff (fun _ => 1) (fun _ => 1) q m difference =
      ((LeanLab.PerelliPintz1992.Decomp1519.muφ q ^ 2 : ℝ) : ℂ) *
        LeanLab.PerelliPintz1992.Decomp1519.ram q (-m) := by
  cases difference <;>
    simp only [generalizedCoeff, map_one, mul_one, one_mul, Bool.false_eq_true,
      ite_false, ite_true, gauss_principal, map_intCast]
  all_goals
    rw [principal_eq_ram]
    unfold LeanLab.PerelliPintz1992.Decomp1519.muφ
    push_cast
    ring

/-- The principal coefficient is the existing classical Euler product coefficient. -/
theorem principal_coefficient_eq_gm (m q : ℕ) (hm : 1 ≤ m) (difference : Bool) :
    generalizedCoeff (fun _ => 1) (fun _ => 1) q (m : ℤ) difference =
      (LeanLab.HeathBrown1985.gm m q : ℂ) := by
  have hpconj : (fun h => (starRingEnd ℂ) (principalValue q h)) = principalValue q := by
    funext h
    unfold principalValue
    split_ifs <;> simp
  have hr := characterSum_conj (principalValue q) q (m : ℤ)
  rw [hpconj, principal_eq_ram, principal_eq_ram] at hr
  rw [principal_coefficient, hr]
  calc
    _ = (starRingEnd ℂ)
        (((LeanLab.PerelliPintz1992.Decomp1519.muφ q ^ 2 : ℝ) : ℂ) *
          LeanLab.PerelliPintz1992.Decomp1519.ram q (m : ℤ)) := by
      rw [map_mul, Complex.conj_ofReal]
    _ = _ := by
      rw [LeanLab.PerelliPintz1992.Decomp1519.ram_term_eq_gm m q hm,
        Complex.conj_ofReal]

/-- The principal coefficient series has the classical value at positive even m. -/
theorem principal_hasSum (m : ℕ) (hm : 1 ≤ m) (he : Even m) (difference : Bool) :
    HasSum (fun q : ℕ => generalizedCoeff (fun _ => 1) (fun _ => 1) q (m : ℤ) difference)
      (Sing m : ℂ) := by
  have hsing : LeanLab.HeathBrown1985.singular m = Sing m := by
    rw [LeanLab.HeathBrown1985.singular, ite_eq_left he, Sing, Applications.C0_eq_twinC]
    congr 1
    apply prod_congr rfl
    intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    have hne : (p : ℝ) - 2 ≠ 0 := by linarith
    field_simp
    ring
  have hsum := Complex.hasSum_ofReal.mpr (LeanLab.HeathBrown1985.hasSum_gm m hm)
  rw [hsing] at hsum
  convert hsum using 1
  funext q
  exact principal_coefficient_eq_gm m q hm difference

/-- The principal coefficient series is absolutely convergent at positive m. -/
theorem principal_summable_norm (m : ℕ) (hm : 1 ≤ m) (difference : Bool) :
    Summable (fun q : ℕ =>
      ‖generalizedCoeff (fun _ => 1) (fun _ => 1) q (m : ℤ) difference‖) := by
  simpa only [principal_coefficient_eq_gm m _ hm difference, Complex.norm_real] using
    LeanLab.HeathBrown1985.summable_abs_gm m hm

/-- The exact generalizedSeries definition recovers Sing at positive even m. -/
theorem principal_series (m : ℕ) (hm : 1 ≤ m) (he : Even m) (difference : Bool) :
    generalizedSeries 1 1 (fun _ => 1) (fun _ => 1) (m : ℤ) difference = (Sing m : ℂ) := by
  unfold generalizedSeries
  have hterm : (fun q : ℕ => if 0 < q ∧ Nat.lcm 1 1 ∣ q then
      generalizedCoeff (fun _ => 1) (fun _ => 1) q (m : ℤ) difference else 0) =
      (fun q : ℕ => generalizedCoeff (fun _ => 1) (fun _ => 1) q (m : ℤ) difference) := by
    funext q
    by_cases hq : 0 < q
    · simp [hq]
    · have hq0 : q = 0 := by omega
      subst q
      simp [principal_coefficient_eq_gm m 0 hm difference, LeanLab.HeathBrown1985.gm_zero]
  rw [hterm]
  exact (principal_hasSum m hm he difference).tsum_eq

end LeanLab.Pintz2021.PrincipalSeriesTask99

#print axioms LeanLab.Pintz2021.PrincipalSeriesTask99.principal_eq_ram

#print axioms LeanLab.Pintz2021.PrincipalSeriesTask99.gauss_principal

#print axioms LeanLab.Pintz2021.PrincipalSeriesTask99.principal_coefficient

#print axioms LeanLab.Pintz2021.PrincipalSeriesTask99.principal_coefficient_eq_gm

#print axioms LeanLab.Pintz2021.PrincipalSeriesTask99.principal_hasSum

#print axioms LeanLab.Pintz2021.PrincipalSeriesTask99.principal_summable_norm

#print axioms LeanLab.Pintz2021.PrincipalSeriesTask99.principal_series
