/-
The dense part of Shao Proposition 4.1.
Source: https://arxiv.org/abs/1206.6139v2 pages 14 to 15.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

open Finset
open scoped Classical

namespace LeanLab.DensityGoldbach.Counting408

/-- Shao page 14, the display bounding mass by the size of a superlevel set.
Mathlib sum_le_sum and sum_filter provide the finite sum steps. -/
theorem superlevel_mass {N : ℕ} [NeZero N] (g : ZMod N → ℝ) (B τ : ℝ)
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hg : ∀ x, g x ≤ B / N) :
    (∑ x, g x) ≤ B *
      (((univ.filter (fun x : ZMod N => τ / N ≤ g x)).card : ℝ) / N) + τ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hpoint : ∀ x, g x ≤ (if τ / N ≤ g x then B / N else 0) + τ / N := by
    intro x
    split_ifs with h
    · exact (hg x).trans (le_add_of_nonneg_right (by positivity))
    · have : g x < τ / N := lt_of_not_ge h
      simpa using this.le
  calc
    (∑ x, g x) ≤ ∑ x : ZMod N, ((if τ / N ≤ g x then B / N else 0) + τ / N) :=
      sum_le_sum fun x _ => hpoint x
    _ = B * (((univ.filter (fun x : ZMod N => τ / N ≤ g x)).card : ℝ) / N) + τ := by
      rw [sum_add_distrib, ← sum_filter]
      simp only [sum_const, nsmul_eq_mul, card_univ, ZMod.card]
      field_simp
      <;> ring

/-- Shao page 15, the first display. With delta at most 1/8 and cap
1 + delta/10, the threshold delta squared leaves each density at least delta/2
and their sum at least 1 + delta/2. -/
theorem superlevel_densities (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (mass density : Fin 3 → ℝ)
    (hmass : ∀ i, δ ≤ mass i)
    (htotal : 1 + δ ≤ mass 0 + mass 1 + mass 2)
    (hbound : ∀ i, mass i ≤ (1 + δ / 10) * density i + δ ^ 2) :
    (∀ i, δ / 2 ≤ density i) ∧ 1 + δ / 2 ≤ density 0 + density 1 + density 2 := by
  have hcap : 0 < 1 + δ / 10 := by positivity
  have hind : ∀ i, δ / 2 ≤ density i := by
    intro i
    have hsmall : δ ^ 2 ≤ δ / 8 := by nlinarith
    have hm := hmass i
    have hb := hbound i
    nlinarith
  refine ⟨hind, ?_⟩
  have hb0 := hbound 0
  have hb1 := hbound 1
  have hb2 := hbound 2
  have hsmall : δ ^ 2 ≤ δ / 8 := by nlinarith
  nlinarith

/-- LEAF. Shao page 15 Lemma 4.4, from Li and Pan math/0701240v3
pages 10 to 11 Lemma 3.3 at k = 3. Their parameter is at least theta/4,
so the lower bound is the cube of theta/4 times N squared.
This concerns finite sets only. No weights or Fourier assumptions occur. -/
theorem popular_triples (θ : ℝ) (hθ : 0 < θ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N.Prime → N₀ ≤ N → ∀ [NeZero N],
      ∀ X : Fin 3 → Finset (ZMod N),
      (∀ i, θ * N ≤ ((X i).card : ℝ)) →
      (1 + θ) * N ≤ ((X 0).card : ℝ) + (X 1).card + (X 2).card →
      ∀ x : ZMod N, (θ / 4) ^ 3 * (N : ℝ) ^ 2 ≤
        (((univ : Finset (ZMod N × ZMod N)).filter
          (fun yz => yz.1 ∈ X 0 ∧ yz.2 ∈ X 1 ∧ x - yz.1 - yz.2 ∈ X 2)).card : ℝ) := by
  sorry

/-- Shao page 15, the display after Lemma 4.4. Every counted pair contributes
at least the cube of the superlevel threshold to the weighted sum. -/
theorem weighted_count {N : ℕ} [NeZero N] (g : Fin 3 → ZMod N → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (hg : ∀ i x, 0 ≤ g i x) (x : ZMod N) :
    t ^ 3 * (((univ : Finset (ZMod N × ZMod N)).filter
      (fun yz => t ≤ g 0 yz.1 ∧ t ≤ g 1 yz.2 ∧ t ≤ g 2 (x - yz.1 - yz.2))).card : ℝ) ≤
      ∑ y : ZMod N, ∑ z : ZMod N, g 0 y * g 1 z * g 2 (x - y - z) := by
  let S : Finset (ZMod N × ZMod N) := univ.filter
    (fun yz => t ≤ g 0 yz.1 ∧ t ≤ g 1 yz.2 ∧ t ≤ g 2 (x - yz.1 - yz.2))
  calc
    t ^ 3 * (S.card : ℝ) = ∑ _yz ∈ S, t ^ 3 := by
      rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ yz ∈ S, g 0 yz.1 * g 1 yz.2 * g 2 (x - yz.1 - yz.2) := by
      apply sum_le_sum
      intro yz hyz
      have h := (mem_filter.mp hyz).2
      calc
        t ^ 3 = t * t * t := by ring
        _ ≤ g 0 yz.1 * g 1 yz.2 * g 2 (x - yz.1 - yz.2) :=
          mul_le_mul (mul_le_mul h.1 h.2.1 ht (hg _ _)) h.2.2 ht
            (mul_nonneg (hg _ _) (hg _ _))
    _ ≤ ∑ yz : ZMod N × ZMod N, g 0 yz.1 * g 1 yz.2 * g 2 (x - yz.1 - yz.2) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun yz _ _ =>
        mul_nonneg (mul_nonneg (hg _ _) (hg _ _)) (hg _ _)
    _ = ∑ y : ZMod N, ∑ z : ZMod N, g 0 y * g 1 z * g 2 (x - y - z) := by
      rw [Fintype.sum_prod_type]

end LeanLab.DensityGoldbach.Counting408

#print axioms LeanLab.DensityGoldbach.Counting408.superlevel_mass
#print axioms LeanLab.DensityGoldbach.Counting408.superlevel_densities
#print axioms LeanLab.DensityGoldbach.Counting408.weighted_count
