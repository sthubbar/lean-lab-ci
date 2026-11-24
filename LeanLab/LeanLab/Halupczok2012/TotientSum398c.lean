import LeanLab.Halupczok2012.U1462Analytic

/-!
# Reciprocal totient sum over multiples of a modulus

PPS1984 page 531, third display: the sum of `1 / φ(q)` over `q ≤ Q` with `q₁ ∣ q`
is `≪ log Q / φ(q₁)`.

Route: write `q = q₁ m`, use `φ(q₁) φ(m) ≤ φ(q₁ m)`, so the sum is at most
`1 / φ(q₁)` times the full reciprocal totient sum up to `Q`, which is bounded by
`Kc (1/4) (1 + log Q)` via `sum_Hs_div_totient_le` from `U1462Analytic`.
For `Q ≥ 2` we have `1 + log Q ≤ 3 log Q` since `log 2 > 1/2`.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Resplit398c

open Finset

/-- Full reciprocal totient sum up to `N` is at most `Kc (1/4) (1 + log N)`.
Input for PPS1984 page 531, third display. -/
theorem sum_inv_totient_le (N : ℕ) :
    ∑ q ∈ Icc 1 N, 1 / (q.totient : ℝ) ≤ Kc (1 / 4) * (1 + Real.log N) := by
  calc
    _ ≤ ∑ q ∈ Icc 1 N, Hs (1 / 4) q / (q.totient : ℝ) := by
      apply sum_le_sum
      intro q _
      apply div_le_div_of_nonneg_right _ (by positivity)
      unfold Hs
      apply one_le_prod₀
      intro p hp
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : 0 < (p : ℝ) - 1 := by linarith
      exact le_add_of_nonneg_right (by positivity)
    _ ≤ _ := sum_Hs_div_totient_le (by norm_num) (by norm_num) N

/-- Multiples of `q₁`: the sum is at most `1 / φ(q₁)` times the full sum. -/
theorem sum_multiples_inv_totient_le (q₁ Q : ℕ) (hq₁ : 1 ≤ q₁) :
    ∑ q ∈ (Icc 1 Q).filter (q₁ ∣ ·), (1 : ℝ) / q.totient ≤
      (1 / (q₁.totient : ℝ)) * ∑ m ∈ Icc 1 Q, 1 / (m.totient : ℝ) := by
  have hφ1 : (0 : ℝ) < q₁.totient := by exact_mod_cast Nat.totient_pos.mpr hq₁
  have himg : (Icc 1 Q).filter (q₁ ∣ ·) ⊆ ((Icc 1 Q).filter (fun m => q₁ * m ≤ Q)).image
      (fun m => q₁ * m) := by
    intro q hq
    simp only [mem_filter, mem_Icc] at hq
    obtain ⟨⟨h1, h2⟩, m, rfl⟩ := hq
    refine mem_image.mpr ⟨m, ?_, rfl⟩
    simp only [mem_filter, mem_Icc]
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; omega
      · exact h
    exact ⟨⟨hm, le_trans (Nat.le_mul_of_pos_left m hq₁) h2⟩, h2⟩
  calc
    _ ≤ ∑ q ∈ ((Icc 1 Q).filter (fun m => q₁ * m ≤ Q)).image (fun m => q₁ * m),
        (1 : ℝ) / q.totient :=
      sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
    _ ≤ ∑ m ∈ (Icc 1 Q).filter (fun m => q₁ * m ≤ Q), (1 : ℝ) / (q₁ * m).totient :=
      sum_image_le_of_nonneg (fun _ _ => by positivity)
    _ ≤ ∑ m ∈ (Icc 1 Q).filter (fun m => q₁ * m ≤ Q),
        (1 / (q₁.totient : ℝ)) * (1 / (m.totient : ℝ)) := by
      apply sum_le_sum
      intro m hm
      have hm1 : 1 ≤ m := (mem_Icc.mp (mem_filter.mp hm).1).1
      have hφm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm1
      have hsup : ((q₁.totient : ℝ) * m.totient) ≤ (q₁ * m).totient := by
        exact_mod_cast Nat.totient_super_multiplicative q₁ m
      rw [div_mul_div_comm, one_mul]
      exact one_div_le_one_div_of_le (by positivity) hsup
    _ = (1 / (q₁.totient : ℝ)) * ∑ m ∈ (Icc 1 Q).filter (fun m => q₁ * m ≤ Q),
        1 / (m.totient : ℝ) := (mul_sum _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => by positivity)

/-- `1 + log Q ≤ 3 log Q` for `Q ≥ 2`. -/
theorem one_add_log_le_three_log (Q : ℕ) (hQ : 2 ≤ Q) :
    1 + Real.log Q ≤ 3 * Real.log Q := by
  have h2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hl : Real.log 2 ≤ Real.log Q := Real.log_le_log (by norm_num) h2
  have := Real.log_two_gt_d9
  linarith

/-- PPS1984 page 531, third display:
the sum of `1 / φ(q)` over `q ≤ Q` with `q₁ ∣ q` is `≪ log Q / φ(q₁)`. -/
theorem pps531_third_display :
    ∃ C : ℝ, ∀ q₁ Q : ℕ, 1 ≤ q₁ → 2 ≤ Q →
      ∑ q ∈ (Icc 1 Q).filter (q₁ ∣ ·), (1 : ℝ) / q.totient ≤
        C * Real.log Q / q₁.totient := by
  refine ⟨3 * Kc (1 / 4), fun q₁ Q hq₁ hQ => ?_⟩
  have hK : 0 ≤ Kc (1 / 4) := (Real.exp_pos _).le
  have hφ1 : (0 : ℝ) < q₁.totient := by exact_mod_cast Nat.totient_pos.mpr hq₁
  calc
    _ ≤ _ := sum_multiples_inv_totient_le q₁ Q hq₁
    _ ≤ (1 / (q₁.totient : ℝ)) * (Kc (1 / 4) * (1 + Real.log Q)) :=
      mul_le_mul_of_nonneg_left (sum_inv_totient_le Q) (by positivity)
    _ ≤ (1 / (q₁.totient : ℝ)) * (Kc (1 / 4) * (3 * Real.log Q)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (one_add_log_le_three_log Q hQ) hK) (by positivity)
    _ = _ := by field_simp

#print axioms sum_inv_totient_le
#print axioms sum_multiples_inv_totient_le
#print axioms pps531_third_display

end LeanLab.Halupczok2012.Resplit398c
