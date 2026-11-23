/-
P0076, Section 4, page 15, the display after display 4.3: the Euler product over w < p at most y
of the inverse of 1 - omega p / p, minus the divisors of P of y above z, is at most G_1 of z.
Proves leaf_G1_ge_product_sub_tail of G1LowerSplit.lean outright as G1_ge_product_sub_tail_proved,
by the Euler expansion of a squarefree multiplicative weight over the divisors of P of y.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.G1LowerSplit

open Finset Real
open scoped Classical

namespace LeanLab.Teravainen2016

/-- A product of a finset of primes is squarefree. -/
theorem squarefree_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) : Squarefree (∏ p ∈ s, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)
  · intro p hp; exact (hs p hp).squarefree

/-- Page 15, statement of leaf_G1_ge_product_sub_tail, PROVED. Since 1 + h p equals the inverse of
1 - omega p / p for w < p, the Euler product at y is the sum of h d over the divisors d of the
squarefree P of y, and the divisors at most z are terms of G_1 of z, whose other terms are
nonnegative. -/
theorem G1_ge_product_sub_tail_proved :
    ∀ w : ℕ, wBig ≤ w → ∀ y z : ℝ, 1 ≤ y → y ≤ z →
      (∏ p ∈ (range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ y),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹) -
        ∑ d ∈ (envelopingPrimeProduct w y).divisors.filter (fun d : ℕ => z < (d : ℝ)), envelopingH w d ≤
          envelopingG w 1 z := by
  intro w hw y z hy hyz
  set F := (range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ y) with hF
  have hFp : ∀ p ∈ F, p.Prime := fun p hp => (mem_filter.mp hp).2.1
  set P := envelopingPrimeProduct w y with hP
  have hPF : P = ∏ p ∈ F, p := rfl
  have hPsq : Squarefree P := hPF ▸ squarefree_prod_primes F hFp
  have hPpf : P.primeFactors = F := by rw [hPF]; exact Nat.primeFactors_prod hFp
  set g : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors
    (fun p => (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ)) with hg
  have hgm : g.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  have hexp := hgm.prodPrimeFactors_one_add_of_squarefree hPsq
  have hgH : ∀ d ∈ P.divisors, g d = envelopingH w d := by
    intro d hd
    have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    have hdsq : Squarefree d := hPsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    rw [hg, ArithmeticFunction.prodPrimeFactors_apply hd0, envelopingH]
    simp only [hdsq, ↓reduceIte]
  have hgp : ∀ p ∈ F, 1 + g p = (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
    intro p hp
    have hpp := hFp p hp
    have hwp : w < p := (mem_filter.mp hp).2.2.1
    have hwBig1 : (10 : ℝ) ≤ wBig := by
      calc (10 : ℝ) = (10 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (Real.one_le_rpow (by norm_num) (by positivity))
    have h10 : (10 : ℝ) < p := lt_of_le_of_lt (hwBig1.trans hw) (by exact_mod_cast hwp)
    have hω : envelopingOmega w p ≤ 2 := by
      unfold envelopingOmega; split_ifs <;> norm_num
    have hωp : envelopingOmega w p < p := by
      have : (10 : ℕ) < p := by exact_mod_cast h10
      omega
    rw [hg, ArithmeticFunction.prodPrimeFactors_apply hpp.ne_zero, hpp.primeFactors,
      prod_singleton, Nat.cast_sub hωp.le]
    have hωr : (envelopingOmega w p : ℝ) < p := by exact_mod_cast hωp
    have hp0 : (0 : ℝ) < p := by linarith
    have h1 : (p : ℝ) - envelopingOmega w p ≠ 0 := by linarith
    rw [one_sub_div hp0.ne', inv_div]
    field_simp
    ring
  have hprod : (∏ p ∈ F, (1 - (envelopingOmega w p : ℝ) / p)⁻¹) =
      ∑ d ∈ P.divisors, envelopingH w d := by
    rw [← prod_congr rfl hgp, ← hPpf, hexp]
    exact sum_congr rfl hgH
  rw [hprod, ← sum_filter_add_sum_filter_not P.divisors (fun d : ℕ => z < (d : ℝ)),
    add_sub_cancel_left]
  unfold envelopingG
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hd, hdz⟩ := mem_filter.mp hd
    push Not at hdz
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hd1, Nat.le_floor hdz⟩, ?_⟩
    simpa only [Nat.lcm_one_left] using hdz
  · intro d _ _
    exact envelopingH_nonneg w d

/-- The proved theorem has exactly the type of the LEAF in G1LowerSplit.lean. -/
example : type_of% G1_ge_product_sub_tail_proved = type_of% leaf_G1_ge_product_sub_tail := rfl

end LeanLab.Teravainen2016
