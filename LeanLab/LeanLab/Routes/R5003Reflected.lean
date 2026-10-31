import LeanLab.GoldbachGaps.Goldston1990Thm6Core

/-!
# R-5003 addendum: the reflected window correlation is the only loss in Goldston's Theorem

Lab route, unit U-6304, CLOUD 20261020T1017Z-cloud40, T3. AI wrote this file.

With `e = log p 1_{p ≤ N} - 1_{[1,N]}` and window sums `X(z) = Σ_{a<K} e(z - a)`, the Fejér
Goldbach count satisfies, for `1 ≤ K ≤ N`,

`Σ_{|n| ≤ K} (K - |n|) R(N + n) ≥ K² N - K³ - 2 K³ (log N + 1) + 2 K² (θ(N) - N) + C(N, K)`,

`C(N, K) = Σ_z X(z) X(N + K - 1 - z)`, the correlation of the prime window errors at reflected
positions: `fejerC_ge_reflected`. Goldston's Theorem bounds `|C|` by `Σ X(z)² ≈ J(N, K)` through
AM-GM, `Thm6.abs_bil_self_le`, and that is the only step that meets the variance barrier of
display 10. So a sum of two primes lies in `[N - K, N + K]` as soon as `C(N, K)` exceeds
`-(K² N)(1 - o(1))`, `exists_goldbach_of_reflected`; at `K = 1` this is binary Goldbach for `N`
itself, `R(N) > 0`, so the reformulation hides nothing: the parity information sits in the sign of
`C`. A map entry, not progress on Goldbach, which is OPEN.
-/

namespace LeanLab.GoldbachGaps.Goldston1990.Thm6
open Real Chebyshev Finset

/-- The full count dominates the truncated one, termwise. -/
lemma fejerC_ge_bil (N K : ℕ) (hKN : K ≤ N) : bil N K (fN N) (fN N) ≤ fejerC N K := by
  rw [bil_self N K (fN N) (fN_zero N) hKN, fejer_reindex N K hKN, fejerC]
  apply sum_le_sum; intro j hj
  have hj' : j ≤ 2 * K := by have := mem_range.mp hj; omega
  exact mul_le_mul_of_nonneg_left (by linarith [(conv_le_Rg N K (N + j - K) (by omega)).1])
    (weight_nonneg K j hj')

/-- **The exact lower bound with the reflected correlation exposed.** -/
theorem fejerC_ge_reflected (N K : ℕ) (hK : 1 ≤ K) (hKN : K ≤ N) :
    (K : ℝ) ^ 2 * N - K ^ 3 - 2 * K ^ 3 * (Real.log N + 1) + 2 * K ^ 2 * (θ (N : ℝ) - N) +
      bil N K (eN N) (eN N) ≤ fejerC N K := by
  have hsplit : bil N K (fN N) (fN N) = bil N K (gN N) (gN N) + bil N K (gN N) (eN N) +
      bil N K (eN N) (gN N) + bil N K (eN N) (eN N) := by
    rw [fN_eq]
    unfold bil
    simp_rw [win_add]
    rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro z _; ring
  rw [bil_comm N K (eN N) (gN N)] at hsplit
  have hgg := bil_g_left N K (gN N) (gN_zero N) (fun u hu => gN_big hu) K (abs_win_gN N K)
  rw [sum_gN] at hgg
  have hge := bil_g_left N K (eN N) (eN_zero N) (fun u hu => eN_big hu) _ (abs_win_eN N K)
  rw [sum_eN] at hge
  have h1 := fejerC_ge_bil N K hKN
  rw [abs_le] at hgg hge
  have e1 : (K : ℝ) * K ^ 2 = K ^ 3 := by ring
  have e2 : (K : ℝ) * (Real.log N + 1) * K ^ 2 = K ^ 3 * (Real.log N + 1) := by ring
  rw [e1] at hgg
  rw [e2] at hge
  linarith [hgg.1, hge.1]

/-- A positive Fejér sum puts a sum of two primes in the window. -/
lemma exists_of_fejerC_pos (N K : ℕ) (h : 0 < fejerC N K) :
    ∃ j < 2 * K + 1, 0 < RgC (N + j - K) := by
  by_contra hno
  push_neg at hno
  have : fejerC N K ≤ 0 := by
    unfold fejerC
    apply sum_nonpos; intro j hj
    have hj' := mem_range.mp hj
    have hw : 0 ≤ (K : ℝ) - |(j : ℝ) - K| := weight_nonneg K j (by omega)
    exact mul_nonpos_of_nonneg_of_nonpos hw (hno j hj')
  linarith

/-- **Goldbach in the window from the reflected correlation.** If
`C(N, K) > -(K² N - K³ - 2K³(log N + 1) + 2K²(θ(N) - N))`, some `n` with `|n| ≤ K` has
`R(N + n) > 0`. -/
theorem exists_goldbach_of_reflected (N K : ℕ) (hK : 1 ≤ K) (hKN : K ≤ N)
    (hC : -((K : ℝ) ^ 2 * N - K ^ 3 - 2 * K ^ 3 * (Real.log N + 1) + 2 * K ^ 2 * (θ (N : ℝ) - N)) <
      bil N K (eN N) (eN N)) :
    ∃ j < 2 * K + 1, 0 < RgC (N + j - K) :=
  exists_of_fejerC_pos N K (by linarith [fejerC_ge_reflected N K hK hKN])

end LeanLab.GoldbachGaps.Goldston1990.Thm6
