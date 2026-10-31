/-
P0045, journal pages 778 to 779, displays 28 and 30.
The weighted support of a single exponent count lies inside a finite Euler product.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LPZ2007.D4Product

namespace LeanLab.LPZ2007.D4Support

open Finset Real
open LeanLab.LPZ2007 LeanLab.LPZ2007.D4Tail

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every occurring squarefree divisor divides the product of the positive differences. -/
theorem support_sum_le (F : Finset ℕ) (M m : ℕ)
    (hF : ∀ d ∈ F, OddSqf d) (hpow : ∀ a ∈ Icc 1 M, 2 ^ a < m) :
    ∑ d ∈ F.filter (fun d => 0 < oneCount d M m), fd d ≤
      ∑ s ∈ (LeanLab.LPZ2007B.opf (∏ a ∈ Icc 1 M, (m - 2 ^ a))).powerset,
        LeanLab.LPZ2007B.W s := by
  let P := ∏ a ∈ Icc 1 M, (m - 2 ^ a)
  have hP0 : P ≠ 0 := prod_ne_zero_iff.2 (fun a ha => by have := hpow a ha; omega)
  have hinj : Set.InjOn Nat.primeFactors (↑(F.filter (fun d => 0 < oneCount d M m))) := by
    intro a ha b hb hab
    have ha' := (hF a (mem_filter.1 ha).1).2
    have hb' := (hF b (mem_filter.1 hb).1).2
    rw [← Nat.prod_primeFactors_of_squarefree ha', ← Nat.prod_primeFactors_of_squarefree hb', hab]
  have hsub : (F.filter (fun d => 0 < oneCount d M m)).image Nat.primeFactors ⊆
      (LeanLab.LPZ2007B.opf P).powerset := by
    intro s hs
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hs
    obtain ⟨hdF, hcnt⟩ := mem_filter.1 hd
    have ho := hF d hdF
    obtain ⟨a, ha⟩ := card_pos.1 hcnt
    obtain ⟨haI, hda⟩ := mem_filter.1 ha
    have hdP : d ∣ P := hda.trans (dvd_prod_of_mem (fun a => m - 2 ^ a) haI)
    rw [mem_powerset]
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hp3 : 2 < p := by
      have hne : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.2 ho.1) (even_iff_two_dvd.2 hpd)
      have := hpp.two_le
      omega
    exact mem_filter.2 ⟨Nat.primeFactors_mono hdP hP0 hp, hp3⟩
  refine sum_le_sum_of_injOn Nat.primeFactors hinj hsub ?_ ?_
  · intro d hd
    exact le_of_eq (Lemma61Port.fd_eq (hF d (mem_filter.1 hd).1))
  · intro s hs _
    exact LeanLab.LPZ2007B.W_nonneg (fun p hp => (mem_filter.1 (mem_powerset.1 hs hp)).2)

/-- Sum the single exponent estimate before applying the product bound. -/
theorem weighted_one_le (F : Finset ℕ) (M m : ℕ)
    (hF : ∀ d ∈ F, OddSqf d) (hpow : ∀ a ∈ Icc 1 M, 2 ^ a < m) :
    ∑ d ∈ F, fd d * (oneCount d M m : ℝ) ≤
      (M : ℝ) * ∑ d ∈ F, romanovTerm d +
      ∑ s ∈ (LeanLab.LPZ2007B.opf (∏ a ∈ Icc 1 M, (m - 2 ^ a))).powerset,
        LeanLab.LPZ2007B.W s := by
  have hmain : ∑ d ∈ F, fd d * (oneCount d M m : ℝ) ≤
      (M : ℝ) * ∑ d ∈ F, romanovTerm d +
      ∑ d ∈ F.filter (fun d => 0 < oneCount d M m), fd d := by
    calc ∑ d ∈ F, fd d * (oneCount d M m : ℝ) ≤
        ∑ d ∈ F, fd d * ((M : ℝ) / xi d + if 0 < oneCount d M m then 1 else 0) :=
          sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left
            (oneCount_bound (hF d hd).1 M m hpow) (fd_nonneg d))
      _ = _ := by
        rw [mul_sum, sum_filter, ← sum_add_distrib]
        apply sum_congr rfl
        intro d hd
        rw [romanovTerm, ite_eq_left (hF d hd)]
        split_ifs <;> ring
  have hs := support_sum_le F M m hF hpow
  linarith

end
end LeanLab.LPZ2007.D4Support

#print axioms LeanLab.LPZ2007.D4Support.support_sum_le

#print axioms LeanLab.LPZ2007.D4Support.weighted_one_le
