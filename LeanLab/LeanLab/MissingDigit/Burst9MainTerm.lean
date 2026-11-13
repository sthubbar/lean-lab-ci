import LeanLab.MissingDigit.Burst8Major

/-!
# Burst 9, pieces of Kim's Section 2.2, the main term bound

Paper: P0057, J. Kim, arXiv 2412.19975v1, Section 2.2, pages 10 and 11. The cited leaf
`Burst8P2.main_term_bound` bounds the main term of Proposition 2.4 by `(log X)^7 |[X,X+H]^*|`.
Kim's proof ends with three factors: the kernel bounds (2.8), (2.9), giving `d₃(m')/q`; the
divisor sums (2.10), (2.11), giving `(log X)^2 (log X)^2 |[X,X+H]^*|` through Lemma 2.6 of
Dartyge and Mauduit, which is a citation wall; and the last display of page 11,
`∑_{m ≤ X^{3ε/20}} d₃(m)/m ≪ (log X)^3`. This file PROVES the last display, in the general
form `∑_{m ≤ M} d_k(m)/m ≤ (1 + log M)^k`. It does not split `main_term_bound`: the QUESTIONS on
Lemma 1.8 and on the factor `1/q` in (2.9), recorded in the note
research/burst-20261112/MissingDigit-kim_thm1_1_58b.md, block an assembly that is faithful to the
exact main term `mainK`.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.MissingDigit.Burst9MainTerm

open Finset Real
open LeanLab.MissingDigit LeanLab.MissingDigit.Burst4Split

/-- One Dirichlet convolution step for the logarithmic sum of `d_k`: since
`d_{k+1}(m)/m = ∑_{de = m} (1/d)(d_k(e)/e)`, dropping the condition `de ≤ M` gives
`∑_{m ≤ M} d_{k+1}(m)/m ≤ (∑_{d ≤ M} 1/d) ∑_{e ≤ M} d_k(e)/e`. Used for the last display of
Kim, P0057 Section 2.2, page 11. -/
theorem dk_sum_step (k M : ℕ) :
    ∑ m ∈ Icc 1 M, (dk (k + 1) m : ℝ) / m ≤
      (∑ d ∈ Icc 1 M, (1 : ℝ) / d) * ∑ e ∈ Icc 1 M, (dk k e : ℝ) / e := by
  set F : ℕ × ℕ → ℝ := fun x => (1 : ℝ) / x.1 * ((dk k x.2 : ℝ) / x.2) with hF
  have h1 : ∀ m ∈ Icc 1 M, (dk (k + 1) m : ℝ) / m = ∑ x ∈ m.divisorsAntidiagonal, F x := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (mem_Icc.1 hm).1; omega
    simp only [dk]
    rw [Nat.cast_sum, Finset.sum_div, ← Nat.map_div_right_divisors, Finset.sum_map]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    obtain ⟨e, rfl⟩ := hdm
    have he0 : e ≠ 0 := by rintro rfl; simp at hm0
    have hd' : 0 < d := Nat.pos_of_ne_zero (left_ne_zero_of_mul hm0)
    show (dk k (d * e / d) : ℝ) / ((d * e : ℕ) : ℝ) = 1 / (d : ℝ) * ((dk k (d * e / d) : ℝ) / ((d * e / d : ℕ) : ℝ))
    rw [Nat.mul_div_cancel_left _ hd']
    have he0' : (e : ℝ) ≠ 0 := by exact_mod_cast he0
    push_cast
    field_simp
  set S := (Icc 1 M ×ˢ Icc 1 M).filter (fun x : ℕ × ℕ => x.1 * x.2 ≤ M) with hS
  have h2 : ∑ m ∈ Icc 1 M, ∑ x ∈ m.divisorsAntidiagonal, F x = ∑ x ∈ S, F x := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := Icc 1 M) (g := fun x => x.1 * x.2)]
    · refine Finset.sum_congr rfl fun m hm => ?_
      have hm1 := mem_Icc.1 hm
      congr 1
      ext ⟨a, b⟩
      simp only [Nat.mem_divisorsAntidiagonal, hS, mem_filter, mem_product, mem_Icc]
      constructor
      · rintro ⟨hab, -⟩
        have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hab; omega)
        have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hab; omega)
        refine ⟨⟨⟨⟨ha, ?_⟩, ⟨hb, ?_⟩⟩, by omega⟩, hab⟩
        · calc a ≤ a * b := Nat.le_mul_of_pos_right a hb
            _ ≤ M := by omega
        · calc b ≤ a * b := Nat.le_mul_of_pos_left b ha
            _ ≤ M := by omega
      · rintro ⟨-, hab⟩
        exact ⟨hab, by omega⟩
    · intro x hx
      simp only [hS, mem_filter, mem_product, mem_Icc] at hx ⊢
      exact ⟨Nat.mul_pos (by omega) (by omega), hx.2⟩
  have hFnn : ∀ x, 0 ≤ F x := fun x => by simp only [hF]; positivity
  rw [Finset.sum_congr rfl h1, h2, Finset.sum_mul_sum, ← Finset.sum_product']
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun x _ _ => hFnn x)

/-- `∑_{m ≤ M} d_k(m)/m ≤ (∑_{d ≤ M} 1/d)^k`, by induction on `k` from `dk_sum_step`. -/
theorem sum_dk_div_le (k M : ℕ) :
    ∑ m ∈ Icc 1 M, (dk k m : ℝ) / m ≤ (∑ d ∈ Icc 1 M, (1 : ℝ) / d) ^ k := by
  induction k with
  | zero =>
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · rw [Finset.sum_eq_single 1]
      · simp [dk]
      · intro m _ hm; simp [dk, hm]
      · intro h; exact absurd (mem_Icc.2 ⟨le_rfl, hM⟩) h
  | succ k ih =>
    have hH : 0 ≤ ∑ d ∈ Icc 1 M, (1 : ℝ) / d := Finset.sum_nonneg fun _ _ => by positivity
    calc _ ≤ _ := dk_sum_step k M
      _ ≤ (∑ d ∈ Icc 1 M, (1 : ℝ) / d) * (∑ d ∈ Icc 1 M, (1 : ℝ) / d) ^ k :=
          mul_le_mul_of_nonneg_left ih hH
      _ = _ := by ring

/-- `∑_{d ≤ M} 1/d ≤ 1 + log M`, from Mathlib's `harmonic_le_one_add_log`. -/
theorem harmonic_Icc_le (M : ℕ) : ∑ d ∈ Icc 1 M, (1 : ℝ) / d ≤ 1 + Real.log M := by
  have := harmonic_le_one_add_log M
  rw [harmonic_eq_sum_Icc] at this
  have h : ((∑ i ∈ Icc 1 M, (i : ℚ)⁻¹ : ℚ) : ℝ) = ∑ d ∈ Icc 1 M, (1 : ℝ) / d := by
    push_cast; simp [one_div]
  rw [← h]; exact this

/-- Kim, P0057 Section 2.2, last display of page 11: `∑_{m ≤ X^{3ε/20}} d₃(m)/m ≪ (log X)^3`,
here with the explicit bound `(1 + (3ε/20) log X)^3`, for the range `m ≤ R₄⁶ = X^{3ε/20}` of the
sum over `m` in `mainK`. PROVED. -/
theorem sum_d3_div_le_log {ε : ℝ} (hε : 0 < ε) {X : ℕ} (hX : 1 ≤ X) :
    ∑ m ∈ Icc 1 ⌊R4 ε X ^ 6⌋₊, (dk 3 m : ℝ) / m ≤ (1 + 3 * ε / 20 * Real.log X) ^ 3 := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hR : R4 ε X ^ 6 = (X : ℝ) ^ (3 * ε / 20) := by
    unfold R4; rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num; ring_nf
  have hY1 : (1 : ℝ) ≤ (X : ℝ) ^ (3 * ε / 20) :=
    Real.one_le_rpow (by exact_mod_cast hX) (by positivity)
  set M := ⌊R4 ε X ^ 6⌋₊ with hM
  have hH0 : 0 ≤ ∑ d ∈ Icc 1 M, (1 : ℝ) / d := Finset.sum_nonneg fun _ _ => by positivity
  have hlogM : Real.log M ≤ 3 * ε / 20 * Real.log X := by
    rcases Nat.eq_zero_or_pos M with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
      exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hX))
    · have hMle : (M : ℝ) ≤ (X : ℝ) ^ (3 * ε / 20) := by
        rw [← hR]; exact Nat.floor_le (by rw [hR]; linarith)
      calc Real.log M ≤ Real.log ((X : ℝ) ^ (3 * ε / 20)) :=
            Real.log_le_log (by exact_mod_cast hpos) hMle
        _ = 3 * ε / 20 * Real.log X := Real.log_rpow hX0 _
  calc ∑ m ∈ Icc 1 M, (dk 3 m : ℝ) / m ≤ (∑ d ∈ Icc 1 M, (1 : ℝ) / d) ^ 3 := sum_dk_div_le 3 M
    _ ≤ (1 + 3 * ε / 20 * Real.log X) ^ 3 :=
        pow_le_pow_left₀ hH0 (le_trans (harmonic_Icc_le M) (by linarith)) 3

#print axioms dk_sum_step
#print axioms sum_dk_div_le
#print axioms harmonic_Icc_le
#print axioms sum_d3_div_le_log

end LeanLab.MissingDigit.Burst9MainTerm
