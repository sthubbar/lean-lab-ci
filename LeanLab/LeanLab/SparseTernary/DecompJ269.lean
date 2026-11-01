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

/-- LEAF: the per-fraction approximation of display 6.10. -/
theorem per_fraction_approx (A B : ℕ) (hSW : SW (B + 5 * A + 1)) :
    PerFractionApprox (B + 5 * A) (12 * A) := by
  sorry

private lemma ee_eq_one_iff' (q : ℕ) (hq : 0 < q) (j : ℤ) :
    ee ((j : ℝ) / q) = 1 ↔ (q : ℤ) ∣ j := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  unfold ee
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have h1 : (((j : ℝ) / q : ℝ) : ℂ) = n := by
      apply mul_left_cancel₀ hpi; rw [hn]; ring
    push_cast at h1
    have h2 : (j : ℂ) = n * q := by rw [← h1]; field_simp
    have h3 : j = n * q := by exact_mod_cast h2
    exact ⟨n, by rw [h3]; ring⟩
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    push_cast
    rw [mul_div_cancel_left₀ _ hq']; ring

private lemma sum_range_ee' (q : ℕ) (hq : 0 < q) (j : ℤ) :
    ∑ ℓ ∈ range q, ee ((ℓ : ℝ) * (j : ℝ) / q) = if (q : ℤ) ∣ j then (q : ℂ) else 0 := by
  have hz : ∀ ℓ : ℕ, ee ((ℓ : ℝ) * (j : ℝ) / q) = ee ((j : ℝ) / q) ^ ℓ := by
    intro ℓ; rw [← ee_nat_mul]; congr 1; ring
  simp_rw [hz]
  split_ifs with h
  · rw [(ee_eq_one_iff' q hq j).mpr h]; simp
  · have hne : ee ((j : ℝ) / q) ≠ 1 := fun h' => h ((ee_eq_one_iff' q hq j).mp h')
    rw [geom_sum_eq hne, ← ee_nat_mul]
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have : (q : ℝ) * ((j : ℝ) / q) = (j : ℝ) := by field_simp
    rw [this, ee_int]; simp

private lemma dvd_iff_modEq' {q k r : ℕ} : (q : ℤ) ∣ ((k : ℤ) - (r : ℤ)) ↔ k ≡ r [MOD q] := by
  rw [Nat.modEq_iff_dvd]
  constructor
  · rintro ⟨c, hc⟩; exact ⟨-c, by rw [mul_neg, ← hc]; ring⟩
  · rintro ⟨c, hc⟩; exact ⟨-c, by rw [mul_neg, ← hc]; ring⟩

private lemma term_id (q : ℕ) (α : ℝ) (hqR : (q : ℝ) ≠ 0) (k r ℓ : ℕ) :
    ee (-((ℓ : ℝ) * r / q)) *
        ((ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * (α + (ℓ : ℝ) / q)))
      = (ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * α) *
          ee ((ℓ : ℝ) * (((k : ℤ) - (r : ℤ) : ℤ) : ℝ) / q) := by
  have h : ee (-((ℓ : ℝ) * r / q)) * ee ((k : ℝ) * (α + (ℓ : ℝ) / q))
      = ee ((k : ℝ) * α) * ee ((ℓ : ℝ) * (((k : ℤ) - (r : ℤ) : ℤ) : ℝ) / q) := by
    rw [← ee_add, ← ee_add]
    congr 1
    push_cast
    field_simp
    ring
  have h2 : ee (-((ℓ : ℝ) * r / q)) *
      ((ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * (α + (ℓ : ℝ) / q)))
      = (ArithmeticFunction.vonMangoldt k : ℂ) *
        (ee (-((ℓ : ℝ) * r / q)) * ee ((k : ℝ) * (α + (ℓ : ℝ) / q))) := by ring
  rw [h2, h]; ring

/-- LEAF: the expansion 5.3 of S over l and r. -/
theorem s_expansion (Z : ℕ) (u α : ℝ) :
    Sexp Z u α = (1 / (q0 Z : ℂ)) * ∑ ℓ ∈ range (q0 Z), ∑ r ∈ R0 Z,
      ee (-((ℓ : ℝ) * r / q0 Z)) * Stil_alias u (α + ℓ / q0 Z) := by
  classical
  simp only [Sexp, Aset, Stil_alias, Iu]
  set q := q0 Z with hq
  have hqpos : 0 < q := hq ▸ q0_pos Z
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  set A : Finset ℕ := Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊ with hA
  have hTb : ∀ r ∈ R0 Z, 1 ≤ r ∧ r ≤ q := by
    intro r hr
    simp only [R0, Finset.mem_filter, Finset.mem_Icc] at hr
    exact ⟨hr.1.1, hq ▸ hr.1.2⟩
  have huniq : ∀ r ∈ R0 Z, ∀ s ∈ R0 Z, r ≡ s [MOD q] → r = s := by
    intro r hr s hs hrs
    obtain ⟨hr1, hr2⟩ := hTb r hr
    obtain ⟨hs1, hs2⟩ := hTb s hs
    have hr1' : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr1
    have hr2' : (r : ℤ) ≤ (q : ℤ) := by exact_mod_cast hr2
    have hs1' : (1 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs1
    have hs2' : (s : ℤ) ≤ (q : ℤ) := by exact_mod_cast hs2
    have hq1' : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hqpos
    have hdvd : (q : ℤ) ∣ ((r : ℤ) - (s : ℤ)) := by
      rw [← Nat.modEq_iff_dvd]; exact hrs.symm
    by_contra hne
    have hz0 : ((r : ℤ) - (s : ℤ)) ≠ 0 := by
      intro h0
      apply hne
      have : (r : ℤ) = (s : ℤ) := by linarith
      exact_mod_cast this
    have hge : (1 : ℤ) ≤ |(r : ℤ) - (s : ℤ)| := Int.one_le_abs hz0
    have hlt : |(r : ℤ) - (s : ℤ)| < (q : ℤ) := by
      rw [abs_lt]; constructor <;> linarith
    obtain ⟨c, hc⟩ := hdvd
    have habs : |(r : ℤ) - (s : ℤ)| = (q : ℤ) * |c| := by
      rw [hc, abs_mul, abs_of_nonneg (by linarith : (0 : ℤ) ≤ (q : ℤ))]
    have hc1 : (1 : ℤ) ≤ |c| := by
      by_contra h
      push_neg at h
      have hnn : (0 : ℤ) ≤ |c| := abs_nonneg c
      have h0 : |c| = 0 := by omega
      rw [h0, mul_zero] at habs
      rw [habs] at hge
      linarith
    have hle : (q : ℤ) * |c| ≤ |(r : ℤ) - (s : ℤ)| := by
      rw [habs]
    have hqle : (q : ℤ) ≤ (q : ℤ) * |c| := by
      have h := mul_le_mul_of_nonneg_left hc1 (by linarith : (0 : ℤ) ≤ (q : ℤ))
      simpa using h
    linarith
  have horth : ∀ k : ℕ, ∑ ℓ ∈ range q, ∑ r ∈ R0 Z,
      ee ((ℓ : ℝ) * (((k : ℤ) - (r : ℤ) : ℤ) : ℝ) / q)
      = if (∃ r ∈ R0 Z, k ≡ r [MOD q]) then (q : ℂ) else 0 := by
    intro k
    rw [Finset.sum_comm]
    simp only [sum_range_ee' q hqpos]
    by_cases hP : ∃ r ∈ R0 Z, k ≡ r [MOD q]
    · obtain ⟨r₀, hr₀, hr₀k⟩ := hP
      have hP' : ∃ r ∈ R0 Z, k ≡ r [MOD q] := ⟨r₀, hr₀, hr₀k⟩
      rw [if_pos hP', Finset.sum_eq_single r₀]
      · rw [if_pos ((dvd_iff_modEq').mpr hr₀k)]
      · intro b hb hne'
        rw [if_neg]
        intro hd
        exact hne' (huniq b hb r₀ hr₀ (((dvd_iff_modEq').mp hd).symm.trans hr₀k))
      · intro h; exact absurd hr₀ h
    · rw [if_neg hP]
      refine Finset.sum_eq_zero (fun r hr => ?_)
      rw [if_neg]
      intro hd
      exact hP ⟨r, hr, (dvd_iff_modEq').mp hd⟩
  have hA1 : ∀ ℓ r : ℕ,
      ee (-((ℓ : ℝ) * r / q)) * (∑ k ∈ A, (ArithmeticFunction.vonMangoldt k : ℂ) *
        ee ((k : ℝ) * (α + (ℓ : ℝ) / q)))
      = ∑ k ∈ A, (ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * α) *
        ee ((ℓ : ℝ) * (((k : ℤ) - (r : ℤ) : ℤ) : ℝ) / q) := by
    intro ℓ r
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => term_id q α hqR k r ℓ)
  have hB1 : (∑ ℓ ∈ range q, ∑ r ∈ R0 Z, ∑ k ∈ A,
      (ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * α) *
        ee ((ℓ : ℝ) * (((k : ℤ) - (r : ℤ) : ℤ) : ℝ) / q))
      = (∑ ℓ ∈ range q, ∑ k ∈ A, ∑ r ∈ R0 Z,
      (ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * α) *
        ee ((ℓ : ℝ) * (((k : ℤ) - (r : ℤ) : ℤ) : ℝ) / q)) := by
    refine Finset.sum_congr rfl (fun ℓ _ => Finset.sum_comm)
  have hB2 : (∑ ℓ ∈ range q, ∑ k ∈ A, ∑ r ∈ R0 Z,
      (ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * α) *
        ee ((ℓ : ℝ) * (((k : ℤ) - (r : ℤ) : ℤ) : ℝ) / q))
      = (∑ k ∈ A, ∑ ℓ ∈ range q, ∑ r ∈ R0 Z,
      (ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * α) *
        ee ((ℓ : ℝ) * (((k : ℤ) - (r : ℤ) : ℤ) : ℝ) / q)) :=
    Finset.sum_comm
  have hC : (∑ k ∈ A, ∑ ℓ ∈ range q, ∑ r ∈ R0 Z,
      (ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * α) *
        ee ((ℓ : ℝ) * (((k : ℤ) - (r : ℤ) : ℤ) : ℝ) / q))
      = (∑ k ∈ A, (ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * α) *
        (∑ ℓ ∈ range q, ∑ r ∈ R0 Z,
          ee ((ℓ : ℝ) * (((k : ℤ) - (r : ℤ) : ℤ) : ℝ) / q))) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Finset.mul_sum]
  have hD : (∑ k ∈ A, (ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * α) *
        (∑ ℓ ∈ range q, ∑ r ∈ R0 Z,
          ee ((ℓ : ℝ) * (((k : ℤ) - (r : ℤ) : ℤ) : ℝ) / q)))
      = (∑ k ∈ A, (ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * α) *
        (if (∃ r ∈ R0 Z, k ≡ r [MOD q]) then (q : ℂ) else 0)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [horth k]
  have hE : (1 / (q : ℂ)) * (∑ k ∈ A, (ArithmeticFunction.vonMangoldt k : ℂ) *
        ee ((k : ℝ) * α) * (if (∃ r ∈ R0 Z, k ≡ r [MOD q]) then (q : ℂ) else 0))
      = (∑ k ∈ A, (ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * α) *
        (if (∃ r ∈ R0 Z, k ≡ r [MOD q]) then (1 : ℂ) else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : ∃ r ∈ R0 Z, k ≡ r [MOD q]
    · rw [if_pos h, if_pos h]; field_simp
    · rw [if_neg h, if_neg h]; ring
  have hF : (∑ k ∈ A, (ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * α) *
        (if (∃ r ∈ R0 Z, k ≡ r [MOD q]) then (1 : ℂ) else 0))
      = ∑ k ∈ A.filter (fun k => ∃ r ∈ R0 Z, k ≡ r [MOD q]),
          (ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * α) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : ∃ r ∈ R0 Z, k ≡ r [MOD q] <;> simp [h]
  have hmain : (1 / (q : ℂ)) * (∑ ℓ ∈ range q, ∑ r ∈ R0 Z,
      ee (-((ℓ : ℝ) * r / q)) * (∑ k ∈ A, (ArithmeticFunction.vonMangoldt k : ℂ) *
        ee ((k : ℝ) * (α + (ℓ : ℝ) / q))))
      = ∑ k ∈ A.filter (fun k => ∃ r ∈ R0 Z, k ≡ r [MOD q]),
          (ArithmeticFunction.vonMangoldt k : ℂ) * ee ((k : ℝ) * α) := by
    simp only [hA1]
    rw [hB1, hB2, hC, hD, hE, hF]
  exact hmain.symm

private lemma ee_neg_sum_three' (n : ℕ) (x y z : ℝ) :
    ee (-(x / n)) * ee (-(y / n)) * ee (-(z / n)) = ee (-((x + y + z) / n)) := by
  rw [← ee_add, ← ee_add]
  congr 1
  ring

/-- The product of three terms of the expansion, in the order the sums produce them. -/
private lemma cube_term_mul (n : ℕ) (a b c : ℝ) (s₁ s₂ s₃ : ℂ) :
    (ee (-(a / n)) * s₁ * (ee (-(b / n)) * s₂)) * (ee (-(c / n)) * s₃)
      = ee (-((c + b + a) / n)) * s₃ * s₂ * s₁ := by
  rw [← ee_neg_sum_three' n c b a]
  ring

/-- LEAF: the cube expansion 6.11 to 6.12. -/
theorem s_cube_expansion (Z : ℕ) (u α : ℝ) :
    Sexp Z u α ^ 3 = (1 / (q0 Z : ℂ) ^ 3) * ∑ ℓ₁ ∈ range (q0 Z), ∑ r₁ ∈ R0 Z,
      ∑ ℓ₂ ∈ range (q0 Z), ∑ r₂ ∈ R0 Z, ∑ ℓ₃ ∈ range (q0 Z), ∑ r₃ ∈ R0 Z,
      ee (-((ℓ₁ * r₁ + ℓ₂ * r₂ + ℓ₃ * r₃ : ℝ) / q0 Z)) *
      Stil_alias u (α + ℓ₁ / q0 Z) * Stil_alias u (α + ℓ₂ / q0 Z) * Stil_alias u (α + ℓ₃ / q0 Z) := by
  rw [s_expansion Z u α, pow_three]
  set q := q0 Z with hq
  set X : ℂ := ∑ ℓ ∈ range q, ∑ r ∈ R0 Z,
    ee (-((ℓ : ℝ) * r / q)) * Stil_alias u (α + ℓ / q) with hX
  have hX3 : X * X * X = ∑ ℓ₁ ∈ range q, ∑ r₁ ∈ R0 Z,
      ∑ ℓ₂ ∈ range q, ∑ r₂ ∈ R0 Z, ∑ ℓ₃ ∈ range q, ∑ r₃ ∈ R0 Z,
      ((ee (-((ℓ₃ : ℝ) * r₃ / q)) * Stil_alias u (α + ℓ₃ / q)) *
      (ee (-((ℓ₂ : ℝ) * r₂ / q)) * Stil_alias u (α + ℓ₂ / q))) *
      (ee (-((ℓ₁ : ℝ) * r₁ / q)) * Stil_alias u (α + ℓ₁ / q)) := by
    rw [hX]
    simp only [Finset.sum_mul, Finset.mul_sum]
  have hconst : ∀ c : ℂ, (c * X) * (c * X * (c * X)) = c ^ 3 * (X * X * X) := by
    intro c; ring
  rw [hconst, hX3, one_div_pow]
  have hsum : (∑ ℓ₁ ∈ range q, ∑ r₁ ∈ R0 Z,
      ∑ ℓ₂ ∈ range q, ∑ r₂ ∈ R0 Z, ∑ ℓ₃ ∈ range q, ∑ r₃ ∈ R0 Z,
      ((ee (-((ℓ₃ : ℝ) * r₃ / q)) * Stil_alias u (α + ℓ₃ / q)) *
      (ee (-((ℓ₂ : ℝ) * r₂ / q)) * Stil_alias u (α + ℓ₂ / q))) *
      (ee (-((ℓ₁ : ℝ) * r₁ / q)) * Stil_alias u (α + ℓ₁ / q)))
      = ∑ ℓ₁ ∈ range q, ∑ r₁ ∈ R0 Z,
      ∑ ℓ₂ ∈ range q, ∑ r₂ ∈ R0 Z, ∑ ℓ₃ ∈ range q, ∑ r₃ ∈ R0 Z,
      ee (-((ℓ₁ * r₁ + ℓ₂ * r₂ + ℓ₃ * r₃ : ℝ) / q)) *
      Stil_alias u (α + ℓ₁ / q) * Stil_alias u (α + ℓ₂ / q) *
        Stil_alias u (α + ℓ₃ / q) := by
    refine Finset.sum_congr rfl (fun ℓ₁ _ => Finset.sum_congr rfl (fun r₁ _ =>
      Finset.sum_congr rfl (fun ℓ₂ _ => Finset.sum_congr rfl (fun r₂ _ =>
      Finset.sum_congr rfl (fun ℓ₃ _ => Finset.sum_congr rfl (fun r₃ _ => ?_))))))
    exact (cube_term_mul q ((ℓ₃ : ℝ) * r₃) ((ℓ₂ : ℝ) * r₂) ((ℓ₁ : ℝ) * r₁)
      (Stil_alias u (α + ℓ₃ / q)) (Stil_alias u (α + ℓ₂ / q))
      (Stil_alias u (α + ℓ₁ / q))).trans (by ring)
  rw [hsum]

/-- LEAF: disjointness of the major arcs. -/
theorem major_arcs_disjoint (Q : ℝ) :
    ∀ q₁ a₁ q₂ a₂ : ℕ, a₁ < q₁ → a₂ < q₂ → a₁.Coprime q₁ → a₂.Coprime q₂ →
      (q₁ : ℝ) ≤ Real.sqrt (Q / 2) → (q₂ : ℝ) ≤ Real.sqrt (Q / 2) →
      (q₁ ≠ q₂ ∨ a₁ ≠ a₂) →
      Disjoint (Set.Ioo ((a₁ : ℝ) / q₁ - 1 / Q) ((a₁ : ℝ) / q₁ + 1 / Q))
               (Set.Ioo ((a₂ : ℝ) / q₂ - 1 / Q) ((a₂ : ℝ) / q₂ + 1 / Q)) := by
  intro q₁ a₁ q₂ a₂ ha₁ ha₂ hc₁ hc₂ hb₁ hb₂ hne
  have hq₁ : 1 ≤ q₁ := by omega
  have hq₂ : 1 ≤ q₂ := by omega
  have hq₁pos : (0 : ℝ) < (q₁ : ℝ) := by exact_mod_cast hq₁
  have hq₂pos : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast hq₂
  -- the modulus is large
  have hQ2 : (1 : ℝ) ≤ Q / 2 := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (Q / 2) := le_trans (by exact_mod_cast hq₁) hb₁
    rwa [Real.one_le_sqrt] at h1
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQ2nn : (0 : ℝ) ≤ Q / 2 := by linarith
  have hq₁sq : (q₁ : ℝ) ^ 2 ≤ Q / 2 :=
    (Real.sq_le hQ2nn).mpr ⟨by linarith [Real.sqrt_nonneg (Q / 2)], hb₁⟩
  have hq₂sq : (q₂ : ℝ) ^ 2 ≤ Q / 2 :=
    (Real.sq_le hQ2nn).mpr ⟨by linarith [Real.sqrt_nonneg (Q / 2)], hb₂⟩
  -- hence q₁ q₂ ≤ Q / 2
  have hprod : (q₁ : ℝ) * (q₂ : ℝ) ≤ Q / 2 := by
    have h := mul_le_mul hb₁ hb₂ (le_of_lt hq₂pos) (Real.sqrt_nonneg (Q / 2))
    rwa [Real.mul_self_sqrt hQ2nn] at h
  have hprodpos : (0 : ℝ) < (q₁ : ℝ) * (q₂ : ℝ) := by positivity
  -- the two fractions are distinct, hence at distance at least 1/(q₁q₂)
  have hzne : ((a₁ : ℤ) * q₂ - (a₂ : ℤ) * q₁) ≠ 0 := by
    intro h0
    have heq : (a₁ : ℤ) * q₂ = (a₂ : ℤ) * q₁ := sub_eq_zero.mp h0
    have heq' : a₁ * q₂ = a₂ * q₁ := by exact_mod_cast heq
    have hd₁ : q₁ ∣ q₂ := hc₁.symm.dvd_of_dvd_mul_left (by rw [heq']; exact dvd_mul_left _ _)
    have hd₂ : q₂ ∣ q₁ := hc₂.symm.dvd_of_dvd_mul_left (by rw [← heq']; exact dvd_mul_left _ _)
    have hqeq : q₁ = q₂ := Nat.dvd_antisymm hd₁ hd₂
    have haeq : a₁ = a₂ := by
      rw [hqeq] at heq'
      exact Nat.mul_right_cancel (by omega : 0 < q₂) heq'
    rcases hne with h | h
    · exact h hqeq
    · exact h haeq
  have hz1 : (1 : ℝ) ≤ |(((a₁ : ℤ) * q₂ - (a₂ : ℤ) * q₁ : ℤ) : ℝ)| := by
    have h : (1 : ℤ) ≤ |((a₁ : ℤ) * q₂ - (a₂ : ℤ) * q₁ : ℤ)| := Int.one_le_abs hzne
    rw [← Int.cast_abs]
    exact_mod_cast h
  have hzcast : (((a₁ : ℤ) * q₂ - (a₂ : ℤ) * q₁ : ℤ) : ℝ)
      = (a₁ : ℝ) * (q₂ : ℝ) - (a₂ : ℝ) * (q₁ : ℝ) := by push_cast; ring
  have hAB : (a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂
      = (((a₁ : ℤ) * q₂ - (a₂ : ℤ) * q₁ : ℤ) : ℝ) / ((q₁ : ℝ) * (q₂ : ℝ)) := by
    rw [hzcast]; field_simp
  -- distance bound
  have hdist : 2 / Q ≤ |(a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂| := by
    have h1 : 2 / Q ≤ 1 / ((q₁ : ℝ) * (q₂ : ℝ)) := by
      rw [div_le_iff₀ hQ0, one_div, inv_mul_eq_div]
      field_simp
      linarith
    have h2 : 1 / ((q₁ : ℝ) * (q₂ : ℝ))
        ≤ |(((a₁ : ℤ) * q₂ - (a₂ : ℤ) * q₁ : ℤ) : ℝ)| / ((q₁ : ℝ) * (q₂ : ℝ)) := by
      rw [le_div_iff₀ hprodpos, one_div, inv_mul_cancel₀ (ne_of_gt hprodpos)]
      exact hz1
    rw [hAB, abs_div, abs_of_pos hprodpos]
    linarith
  -- and the intervals are within 1/Q of the fractions
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  rw [Set.mem_Ioo] at hx₁ hx₂
  obtain ⟨hx₁a, hx₁b⟩ := hx₁
  obtain ⟨hx₂a, hx₂b⟩ := hx₂
  have e1 : |x - (a₁ : ℝ) / q₁| < 1 / Q := by
    rw [abs_lt]; constructor <;> linarith
  have e2 : |x - (a₂ : ℝ) / q₂| < 1 / Q := by
    rw [abs_lt]; constructor <;> linarith
  have e3 : |(a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂| < 2 / Q := by
    have hsplit : (a₁ : ℝ) / q₁ - (a₂ : ℝ) / q₂
        = ((a₁ : ℝ) / q₁ - x) + (x - (a₂ : ℝ) / q₂) := by ring
    rw [hsplit]
    calc |((a₁ : ℝ) / q₁ - x) + (x - (a₂ : ℝ) / q₂)|
        ≤ |(a₁ : ℝ) / q₁ - x| + |x - (a₂ : ℝ) / q₂| := abs_add_le _ _
      _ < 1 / Q + 1 / Q := by
          rw [abs_sub_comm] at e1
          linarith
      _ = 2 / Q := by ring
  linarith

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
  sorry

theorem Arc613FromSWProp_assembly (A B : ℕ) : Arc613FromSWProp A B := by
  intro hSW
  have h1 := per_fraction_approx A B hSW
  have h2 := s_expansion
  have h3 := s_cube_expansion
  have h4 := major_arcs_disjoint
  exact arc_integration_613 A B h1 h2 h3 h4

end LeanLab.SparseTernary.DecompJ269
