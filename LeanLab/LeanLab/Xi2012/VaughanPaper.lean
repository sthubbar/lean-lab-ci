import LeanLab.PNTPort.BV.Vaughan

/-!
Xi 2012, arXiv 1206.2148v1, page 7 Lemma 4.
The cutoffs are u for Moebius and v for von Mangoldt, as in the paper.
The small von Mangoldt term vanishes when v is less than n.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Xi2012.NatEncoding

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open LeanLab.PNTPort.BV (vF vF' vG vF_add_vF')

/-- The three convolution terms of page 7, with the small term retained globally. -/
theorem vaughan_three_term_identity (u v : ℕ) :
    (Λ : ArithmeticFunction ℝ) = vF v +
      (vG u * log - vG u * vF v * (ζ : ArithmeticFunction ℝ) +
        ((μ : ArithmeticFunction ℝ) - vG u) * vF' v * (ζ : ArithmeticFunction ℝ)) := by
  have hlog : (log : ArithmeticFunction ℝ) =
      (vF v + vF' v) * (ζ : ArithmeticFunction ℝ) := by
    rw [vF_add_vF', vonMangoldt_mul_zeta]
  rw [hlog]
  calc
    (Λ : ArithmeticFunction ℝ) = vF v + vF' v := (vF_add_vF' v).symm
    _ = vF v + (μ * ζ : ArithmeticFunction ℝ) * vF' v := by
      rw [coe_moebius_mul_coe_zeta, one_mul]
    _ = _ := by ring

open Finset
open LeanLab.PNTPort.BV (vF_apply vF'_apply vG_apply af_sub_apply)

/-- Page 7 Lemma 4 with the paper's two positive integer cutoffs. -/
theorem vaughan_paper_identity (u v n : ℕ) (_hu : 1 ≤ u) (_hv : 1 ≤ v) (hvn : v < n) :
    (Λ n : ℝ) =
      (∑ z ∈ n.divisorsAntidiagonal,
        if z.1 ≤ u then (μ z.1 : ℝ) * Real.log z.2 else 0) -
      (∑ z ∈ n.divisorsAntidiagonal, ∑ y ∈ z.1.divisorsAntidiagonal,
        if y.1 ≤ u ∧ y.2 ≤ v then (μ y.1 : ℝ) * Λ y.2 else 0) +
      (∑ z ∈ n.divisorsAntidiagonal, ∑ y ∈ z.1.divisorsAntidiagonal,
        if u < y.1 ∧ v < y.2 then (μ y.1 : ℝ) * Λ y.2 else 0) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hfirst : (vG u * log) n =
      ∑ z ∈ n.divisorsAntidiagonal,
        if z.1 ≤ u then (μ z.1 : ℝ) * Real.log z.2 else 0 := by
    rw [mul_apply]
    apply Finset.sum_congr rfl
    intro z _
    simp only [vG_apply, log_apply]
    split_ifs <;> simp
  have hsecond : (vG u * vF v * (ζ : ArithmeticFunction ℝ)) n =
      ∑ z ∈ n.divisorsAntidiagonal, ∑ y ∈ z.1.divisorsAntidiagonal,
        if y.1 ≤ u ∧ y.2 ≤ v then (μ y.1 : ℝ) * Λ y.2 else 0 := by
    rw [mul_apply]
    apply Finset.sum_congr rfl
    intro z hz
    have hz2 : z.2 ≠ 0 := by
      intro hz0
      have hmul := (Nat.mem_divisorsAntidiagonal.mp hz).1
      rw [hz0, mul_zero] at hmul
      exact hn0 hmul.symm
    rw [natCoe_apply, zeta_apply_ne hz2, Nat.cast_one, mul_one, mul_apply]
    apply Finset.sum_congr rfl
    intro y _
    simp only [vG_apply, vF_apply]
    by_cases h₁ : y.1 ≤ u <;> by_cases h₂ : y.2 ≤ v <;> simp [h₁, h₂]
  have hthird : (((μ : ArithmeticFunction ℝ) - vG u) * vF' v *
      (ζ : ArithmeticFunction ℝ)) n =
      ∑ z ∈ n.divisorsAntidiagonal, ∑ y ∈ z.1.divisorsAntidiagonal,
        if u < y.1 ∧ v < y.2 then (μ y.1 : ℝ) * Λ y.2 else 0 := by
    rw [mul_apply]
    apply Finset.sum_congr rfl
    intro z hz
    have hz2 : z.2 ≠ 0 := by
      intro hz0
      have hmul := (Nat.mem_divisorsAntidiagonal.mp hz).1
      rw [hz0, mul_zero] at hmul
      exact hn0 hmul.symm
    rw [natCoe_apply, zeta_apply_ne hz2, Nat.cast_one, mul_one, mul_apply]
    apply Finset.sum_congr rfl
    intro y _
    simp only [af_sub_apply, intCoe_apply, vG_apply, vF'_apply]
    by_cases h₁ : y.1 ≤ u
    · simp [h₁, not_lt.mpr h₁]
    · have hgt : u < y.1 := lt_of_not_ge h₁
      by_cases h₂ : v < y.2 <;> simp [h₁, hgt, h₂]
  have key := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (vaughan_three_term_identity u v)
  simp only [ArithmeticFunction.add_apply, af_sub_apply, vF_apply,
    ite_eq_right (not_le.mpr hvn), zero_add] at key
  rw [hfirst, hsecond, hthird] at key
  exact key

end LeanLab.Xi2012.NatEncoding
