import LeanLab.ChenDoubleSieve.Lemma41Uk
import LeanLab.ChenDoubleSieve.Lemma42

/-!
# Wu 2004 Lemma 4.2 for `σ ∈ U_k(N)`, the remainder as a power saving

P0036 J. Wu 2004, Section 4, Lemma 4.2. Unit U-5405, CLOUD 20261019T1014Z-cloud22.
AI wrote the Lean code.

`lemma42_Uk`: summed over Wu's tuples `t = (p₁, …, p_i)` of `σ ∈ U_k(N)`, with `d_t = p₁⋯p_i`,
`A ⊆ {0, …, N}`, `1 < Δ ≤ 3/2`, `V_j ≥ 3` and thresholds `0 < W ≤ w ≤ k₁ ≤ k₂ ≤ k₃ ≤ z`
depending on `t`,
`5 Σ_t S(A_{d_t}; P(d_t N), z) + Σ_t (Γ₂ + Γ₃ + Γ₄) ≤ Σ_t (Γ₁ + Γ₅ + ⋯ + Γ₂₁) + 3 i (N/W + 2^i ∏ V_j)`,
Wu's printed `P(dN)` read as in `Lemma42.lean`. At Wu's parameters the remainder is his
`O(N^{1-η})`, as explained in `Lemma41Uk.lean`. Binary Goldbach is OPEN.
-/

open Finset

noncomputable section
open scoped Classical

namespace LeanLab.ChenDoubleSieve.Wu41

/-- The remainder sum over Wu's tuples: `Σ_t i (N/(W d_t) + 1) ≤ i (N/W + 2^i ∏ V_j)`. -/
lemma sum_rem_le (N i : ℕ) (V : Fin i → ℝ) {Δ W : ℝ} (hΔ : 1 < Δ) (hΔ' : Δ ≤ 3 / 2)
    (hV : ∀ j, 3 ≤ V j) (hW : 0 < W) :
    ∑ t ∈ Tset N i V Δ, (i : ℝ) * ((N : ℝ) / (W * ((∏ j, t j : ℕ) : ℝ)) + 1) ≤
      i * (N / W + 2 ^ i * ∏ j, V j) := by
  set T := Tset N i V Δ
  have hR : ∑ t ∈ T, (i : ℝ) * ((N : ℝ) / (W * ((∏ j, t j : ℕ) : ℝ)) + 1) =
      i * ((N / W) * ∑ t ∈ T, (1 / ((∏ j, t j : ℕ) : ℝ)) + #T) := by
    rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, mul_sum]
    congr 2
    refine sum_congr rfl fun t _ => ?_
    push_cast
    field_simp
  have hprod : ∏ j, (Δ - 1 + Δ / V j) ≤ 1 := by
    refine prod_le_one₀ (fun j _ => ?_) (fun j _ => ?_)
    · have := hV j; have : 0 < Δ / V j := by apply div_pos <;> linarith
      linarith
    · have := hV j
      have : Δ / V j ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
  have hsum := sum_inv_T_le N i V (fun j => by linarith [hV j]) hΔ.le
  have hcard := card_T_le N i V (fun j => by linarith [hV j]) hΔ.le
  have hpow : ∏ j, (V j + 1) ≤ 2 ^ i * ∏ j, V j := by
    rw [show (2 : ℝ) ^ i = ∏ _j : Fin i, (2 : ℝ) by simp, ← prod_mul_distrib]
    exact prod_le_prod₀ (fun j _ => by linarith [hV j]) (fun j _ => by linarith [hV j])
  have hNW : 0 ≤ (N : ℝ) / W := by positivity
  have hmain : (N : ℝ) / W * ∑ t ∈ T, (1 / ((∏ j, t j : ℕ) : ℝ)) ≤ N / W := by
    calc _ ≤ (N : ℝ) / W * 1 := mul_le_mul_of_nonneg_left (hsum.trans hprod) hNW
      _ = _ := mul_one _
  rw [hR]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- `Err ≤ i (N/(W d_t) + 1)` for a tuple of `i` primes and a level `w ≥ W > 0`. -/
lemma err_T_le {A : Finset ℕ} {N : ℕ} (hA : A ⊆ range (N + 1)) {i : ℕ} {V : Fin i → ℝ} {Δ : ℝ}
    {t : Fin i → ℕ} (ht : t ∈ Tset N i V Δ) {W w z : ℝ} (hW : 0 < W) (hw : W ≤ w) :
    (Err A (∏ j, t j) N w z : ℝ) ≤ i * ((N : ℝ) / (W * ((∏ j, t j : ℕ) : ℝ)) + 1) := by
  have hd : 1 ≤ ∏ j, t j :=
    Nat.one_le_iff_ne_zero.2 (prod_ne_zero_iff.2 fun j _ => (T_prime ht j).ne_zero)
  have h2 := err_le hA hd (z := z) (lt_of_lt_of_le hW hw)
  have hω : (#(∏ j, t j).primeFactors : ℝ) ≤ i := by
    exact_mod_cast card_primeFactors_prod_le t (T_prime ht)
  have hdpos : (0 : ℝ) < ((∏ j, t j : ℕ) : ℝ) := by exact_mod_cast hd
  have h3 : (N : ℝ) / ((∏ j, t j : ℕ) * w) ≤ N / (W * ((∏ j, t j : ℕ) : ℝ)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    rw [mul_comm W]
    exact mul_le_mul_of_nonneg_left hw hdpos.le
  have h4 : (#(∏ j, t j).primeFactors : ℝ) * ((N : ℝ) / ((∏ j, t j : ℕ) * w) + 1) ≤
      i * ((N : ℝ) / (W * ((∏ j, t j : ℕ) : ℝ)) + 1) :=
    mul_le_mul hω (by linarith) (by have := lt_of_lt_of_le hW hw; positivity) (by positivity)
  exact h2.trans h4

end LeanLab.ChenDoubleSieve.Wu41

namespace LeanLab.ChenDoubleSieve.Wu42

open Wu41 (S Err Tset sum_rem_le err_T_le)

/-- The right side of Lemma 4.2 without the error term, for one `d`. -/
def rhs42 (A : Finset ℕ) (d N : ℕ) (w k₁ k₂ k₃ z : ℝ) : ℕ :=
  Γ₁ A d N w k₁ + Γ₅ A d N w k₂ z + Γ₆ A d N w k₁ k₂ k₃ z + Γ₇ A d N w k₁ z
      + Γ₈ A d N w k₁ k₂ z + Γ₉ A d N w k₁ k₃ z + Γ₁₀ A d N w k₁ k₂ z + Γ₁₁ A d N w k₁ k₂ k₃ z
      + Γ₁₂ A d N w k₁ k₃ z + Γ₁₃ A d N w k₁ k₂ z + Γ₁₄ A d N w k₁ k₂ z
      + Γ₁₅ A d N w k₁ k₂ k₃ z + Γ₁₆ A d N w k₂ k₃ z + Γ₁₇ A d N w k₂ k₃ z
      + Γ₁₈ A d N w k₂ k₃ z + Γ₁₉ A d N w k₁ k₂ k₃ z + Γ₂₀ A d N w k₂ k₃ z
      + Γ₂₁ A d N w k₃ z

/-- The subtracted terms `Γ₂ + Γ₃ + Γ₄` for one `d`. -/
def lhs42 (A : Finset ℕ) (d N : ℕ) (w k₂ k₃ z : ℝ) : ℕ :=
  Γ₂ A d N w z + Γ₃ A d N w k₂ z + Γ₄ A d N w k₃ z

/-- **Wu 2004 Lemma 4.2 for `σ ∈ U_k(N)`, with the remainder made explicit.** -/
theorem lemma42_Uk {A : Finset ℕ} {N : ℕ} (hA : A ⊆ range (N + 1)) (i : ℕ) (V : Fin i → ℝ)
    {Δ W : ℝ} (hΔ : 1 < Δ) (hΔ' : Δ ≤ 3 / 2) (hV : ∀ j, 3 ≤ V j) (hW : 0 < W)
    (w k₁ k₂ k₃ z : (Fin i → ℕ) → ℝ) (hw : ∀ t ∈ Tset N i V Δ, W ≤ w t)
    (h01 : ∀ t ∈ Tset N i V Δ, w t ≤ k₁ t) (h12 : ∀ t ∈ Tset N i V Δ, k₁ t ≤ k₂ t)
    (h23 : ∀ t ∈ Tset N i V Δ, k₂ t ≤ k₃ t) (h34 : ∀ t ∈ Tset N i V Δ, k₃ t ≤ z t) :
    5 * ∑ t ∈ Tset N i V Δ, (S A (∏ j, t j) ((∏ j, t j) * N) (z t) : ℝ)
      + ∑ t ∈ Tset N i V Δ, (lhs42 A (∏ j, t j) N (w t) (k₂ t) (k₃ t) (z t) : ℝ) ≤
      ∑ t ∈ Tset N i V Δ, (rhs42 A (∏ j, t j) N (w t) (k₁ t) (k₂ t) (k₃ t) (z t) : ℝ)
        + 3 * (i * (N / W + 2 ^ i * ∏ j, V j)) := by
  have hper : ∀ t ∈ Tset N i V Δ,
      5 * (S A (∏ j, t j) ((∏ j, t j) * N) (z t) : ℝ)
        + (lhs42 A (∏ j, t j) N (w t) (k₂ t) (k₃ t) (z t) : ℝ) ≤
      (rhs42 A (∏ j, t j) N (w t) (k₁ t) (k₂ t) (k₃ t) (z t) : ℝ)
        + 3 * ((i : ℝ) * ((N : ℝ) / (W * ((∏ j, t j : ℕ) : ℝ)) + 1)) := by
    intro t ht
    have h := lemma42_nat A (∏ j, t j) N (h01 t ht) (h12 t ht) (h23 t ht) (h34 t ht)
    have h' : ((5 * S A (∏ j, t j) ((∏ j, t j) * N) (z t)
        + lhs42 A (∏ j, t j) N (w t) (k₂ t) (k₃ t) (z t) : ℕ) : ℝ) ≤
        ((rhs42 A (∏ j, t j) N (w t) (k₁ t) (k₂ t) (k₃ t) (z t)
          + 3 * Err A (∏ j, t j) N (w t) (z t) : ℕ) : ℝ) := by
      unfold lhs42 rhs42; exact_mod_cast (by omega)
    push_cast at h'
    have he := err_T_le hA ht (z := z t) hW (hw t ht)
    linarith
  have hs := sum_le_sum hper
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum] at hs
  have hr := sum_rem_le N i V hΔ hΔ' hV hW
  linarith

end LeanLab.ChenDoubleSieve.Wu42
