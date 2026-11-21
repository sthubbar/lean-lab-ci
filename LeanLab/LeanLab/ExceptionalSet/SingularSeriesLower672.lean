/-
P0082 page 358 display 11 and page 362 case i.
The even singular series dominates the totient ratio with the existing positive twin constant.
The proof uses the proved Euler product and totient product of HeathBrown1985.
No new definition or analytic hypothesis is introduced.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelectedDecisions
import LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelectedDecisions
import LeanLab.HeathBrown1985.SingularSeries

namespace LeanLab.ExceptionalSet.Task672

open Finset

/-- P0082 page 358 display 11, equality of the two existing singular series formulas. -/
theorem singularSeries_eq_hb672 (m : ℕ) (hm : 1 ≤ m) :
    UpJ200.DQLeafAbsentSelected.singularSeries m = LeanLab.HeathBrown1985.singular m := by
  have hE := EulerProduct.eulerProduct_hasProd_mulIndicator
    (f := LeanLab.HeathBrown1985.gm m) (LeanLab.HeathBrown1985.gm_one m)
    (fun hab => LeanLab.HeathBrown1985.gm_mul m hab)
    (LeanLab.HeathBrown1985.summable_abs_gm m hm) (LeanLab.HeathBrown1985.gm_zero m)
  rw [(LeanLab.HeathBrown1985.hasSum_gm m hm).tsum_eq] at hE
  have hP : HasProd
      (fun p : Nat.Primes => ∑' e : ℕ, LeanLab.HeathBrown1985.gm m ((p : ℕ) ^ e))
      (LeanLab.HeathBrown1985.singular m) :=
    hasProd_subtype_iff_mulIndicator.mpr hE
  have he : (fun p : Nat.Primes => ∑' e : ℕ, LeanLab.HeathBrown1985.gm m ((p : ℕ) ^ e)) =
      (fun p : Nat.Primes => if (p : ℕ) ∣ m then 1 + 1 / ((p : ℝ) - 1)
        else 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    funext p
    rw [LeanLab.HeathBrown1985.gm_prime_pow_tsum m p p.property]
    by_cases hd : (p : ℕ) ∣ m
    · rw [LeanLab.HeathBrown1985.vloc_dvd p.property hd, if_pos hd]
    · rw [LeanLab.HeathBrown1985.vloc_not_dvd p.property hd, if_neg hd]
      ring
  rw [he] at hP
  exact hP.tprod_eq

/-- P0082 page 362 case i, finite Euler-factor comparison with the totient product. -/
theorem hb_singular_totient_lower672 (m : ℕ) (hm : 1 ≤ m) (heven : Even m) :
    LeanLab.ChenExplicit.twinC * ((m : ℝ) / (m.totient : ℝ)) ≤
      LeanLab.HeathBrown1985.singular m := by
  classical
  have htwo : 2 ∈ m.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, even_iff_two_dvd.mp heven, by omega⟩
  have hpart : m.primeFactors = insert 2 (m.primeFactors.filter (2 < ·)) := by
    ext p
    constructor
    · intro hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      rcases eq_or_lt_of_le hprime.two_le with h | h
      · exact Finset.mem_insert.mpr (Or.inl h.symm)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp, h⟩))
    · intro hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact htwo
      · exact (Finset.mem_filter.mp hp).1
  have hratio : (m : ℝ) / (m.totient : ℝ) =
      2 * ∏ p ∈ m.primeFactors.filter (2 < ·), (p : ℝ) / ((p : ℝ) - 1) := by
    calc
      (m : ℝ) / (m.totient : ℝ) =
          ∏ p ∈ m.primeFactors, (p : ℝ) / ((p : ℝ) - 1) :=
        LeanLab.HeathBrown1985.div_totient_eq_prod m hm
      _ = ∏ p ∈ insert 2 (m.primeFactors.filter (2 < ·)),
          (p : ℝ) / ((p : ℝ) - 1) :=
        congrArg (fun s : Finset ℕ => ∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)) hpart
      _ = _ := by rw [Finset.prod_insert (by simp)]; norm_num
  have hprod : (∏ p ∈ m.primeFactors.filter (2 < ·), (p : ℝ) / ((p : ℝ) - 1)) ≤
      ∏ p ∈ m.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
      exact div_nonneg (Nat.cast_nonneg p) (by linarith)
    · intro p hp
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
      rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1)
        (by linarith : (0 : ℝ) < (p : ℝ) - 2)]
      nlinarith
  rw [hratio, LeanLab.HeathBrown1985.singular, if_pos heven]
  have h := mul_le_mul_of_nonneg_left hprod
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) LeanLab.ChenExplicit.twinC_pos.le)
  nlinarith

/-- P0082 page 362 case i, discharge of the natural-number named input. -/
theorem singularSeriesEvenLowerBP_proved672 :
    UpJ200.DQLeafAbsentSelected.SingularSeriesEvenLowerBP := by
  refine ⟨LeanLab.ChenExplicit.twinC, LeanLab.ChenExplicit.twinC_pos, ?_⟩
  intro m hm heven
  rw [singularSeries_eq_hb672 m hm]
  exact hb_singular_totient_lower672 m hm heven

/-- P0082 page 362 case i, discharge of the integer-frequency named input. -/
theorem singSeriesLowerHyp_proved672 : UpJ200.DQLeafCoprimeSelected.SingSeriesLowerHyp := by
  refine ⟨LeanLab.ChenExplicit.twinC, LeanLab.ChenExplicit.twinC_pos, ?_⟩
  intro m hm heven
  have hm0 : 0 ≤ m := by omega
  have hcast : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm0
  have hnat : 1 ≤ m.toNat := by omega
  have hevnat : Even m.toNat := by
    exact_mod_cast (show Even (m.toNat : ℤ) by simpa only [hcast] using heven)
  have heq : UpJ200.DQLeafCoprimeSelected.singSeries m =
      UpJ200.DQLeafAbsentSelected.singularSeries m.toNat := by
    unfold UpJ200.DQLeafCoprimeSelected.singSeries UpJ200.DQLeafAbsentSelected.singularSeries
    apply tprod_congr
    intro p
    rw [← hcast]
    simp only [Int.natCast_dvd_natCast, Int.toNat_natCast]
  rw [heq, singularSeries_eq_hb672 m.toNat hnat]
  exact hb_singular_totient_lower672 m.toNat hnat hevnat

end LeanLab.ExceptionalSet.Task672

#print axioms LeanLab.ExceptionalSet.Task672.singularSeries_eq_hb672
#print axioms LeanLab.ExceptionalSet.Task672.hb_singular_totient_lower672
#print axioms LeanLab.ExceptionalSet.Task672.singularSeriesEvenLowerBP_proved672
#print axioms LeanLab.ExceptionalSet.Task672.singSeriesLowerHyp_proved672
