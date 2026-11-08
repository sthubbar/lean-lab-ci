import Mathlib

/-!
Finite counting in the proof of P0082 Lemma7, pages 363 and 364.
This file uses no cited analytic theorem.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset

/-- Finite Markov counting with the exponents used after P0082 Lemma5,
page 363 before display 20. The first moment has more saving than needed. -/
theorem count_error (s : Finset ℕ) (g : ℕ → ℝ) (c A C E : ℝ) (N : ℕ)
    (hc : 0 < c) (hA : 0 < A) (hC : 0 ≤ C) (hE : 1 ≤ E)
    (hg : ∀ n ∈ s, 0 ≤ g n)
    (hm : ∑ n ∈ s, g n ≤ C * N * E ^ (-(1 / 2 : ℝ))) :
    ((s.filter (fun n => c / (2 * A) * E ^ (-(1 / 10 : ℝ)) < g n)).card : ℝ) ≤
      (2 * A * C / c) * N * E ^ (-(1 / 12 : ℝ)) := by
  classical
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  let T := c / (2 * A) * E ^ (-(1 / 10 : ℝ))
  let u := s.filter (fun n => T < g n)
  have hT : 0 < T := by dsimp [T]; positivity
  have hlow : (u.card : ℝ) * T ≤ ∑ n ∈ u, g n := by
    simpa only [nsmul_eq_mul] using
      u.card_nsmul_le_sum g T (fun n hn => (mem_filter.mp hn).2.le)
  have hsub : u ⊆ s := filter_subset _ _
  have hsum : ∑ n ∈ u, g n ≤ ∑ n ∈ s, g n :=
    sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => hg n hn)
  have hp : E ^ (-(1 / 2 : ℝ)) ≤
      E ^ (-(1 / 12 : ℝ)) * E ^ (-(1 / 10 : ℝ)) := by
    rw [← Real.rpow_add hE0]
    exact Real.rpow_le_rpow_of_exponent_le hE (by norm_num)
  have hupper : C * N * E ^ (-(1 / 2 : ℝ)) ≤
      ((2 * A * C / c) * N * E ^ (-(1 / 12 : ℝ))) * T := by
    calc
      _ ≤ C * N * (E ^ (-(1 / 12 : ℝ)) * E ^ (-(1 / 10 : ℝ))) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by dsimp [T]; field_simp
        <;> ring
  exact (mul_le_mul_iff_left₀ hT).mp (hlow.trans (hsum.trans (hm.trans hupper)))

/-- P0082 pages 363 to 364, Lemma7 counting step. Outside a rare gcd set,
a small coefficient forces a large explicit error. The two counts add. -/
theorem count_coefficient (s t : Finset ℕ) (f g : ℕ → ℝ)
    (c A C B X E : ℝ) (N : ℕ)
    (hc : 0 < c) (hA : 0 < A) (hC : 0 ≤ C) (hX : 0 < X) (hE : 1 ≤ E)
    (hg : ∀ n ∈ s, 0 ≤ g n)
    (hm : ∑ n ∈ s, g n ≤ C * N * E ^ (-(1 / 2 : ℝ)))
    (ht : (t.card : ℝ) ≤ B * N * E ^ (-(1 / 12 : ℝ)))
    (hpoint : ∀ n ∈ s, n ∉ t →
      c * X * E ^ (-(1 / 10 : ℝ)) ≤ f n + A * X * g n) :
    ((s.filter (fun n => f n < c / 2 * X * E ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
      (B + 2 * A * C / c) * N * E ^ (-(1 / 12 : ℝ)) := by
  classical
  let T := c / (2 * A) * E ^ (-(1 / 10 : ℝ))
  let u := s.filter (fun n => T < g n)
  have hu := count_error s g c A C E N hc hA hC hE hg hm
  have hAX : 0 < A * X := mul_pos hA hX
  have hident : A * X * T = c / 2 * X * E ^ (-(1 / 10 : ℝ)) := by
    dsimp [T]
    field_simp
    <;> ring
  have hsub : s.filter (fun n => f n < c / 2 * X * E ^ (-(1 / 10 : ℝ))) ⊆ t ∪ u := by
    intro n hn
    obtain ⟨hns, hnf⟩ := mem_filter.mp hn
    by_cases hnt : n ∈ t
    · exact mem_union.mpr (Or.inl hnt)
    · apply mem_union.mpr
      apply Or.inr
      apply mem_filter.mpr
      refine ⟨hns, ?_⟩
      apply (mul_lt_mul_iff_right₀ hAX).mp
      rw [hident]
      have hp := hpoint n hns hnt
      nlinarith
  have hcard : ((s.filter (fun n => f n < c / 2 * X * E ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
      (t.card : ℝ) + (u.card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le t u)
  change (u.card : ℝ) ≤ _ at hu
  calc
    _ ≤ (t.card : ℝ) + (u.card : ℝ) := hcard
    _ ≤ B * N * E ^ (-(1 / 12 : ℝ)) +
        (2 * A * C / c) * N * E ^ (-(1 / 12 : ℝ)) := add_le_add ht hu
    _ = _ := by ring

end LeanLab.ExceptionalSet.Supply465
