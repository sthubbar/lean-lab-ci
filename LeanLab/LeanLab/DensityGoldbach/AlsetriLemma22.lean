/-
P0085 Alsetri 2025, arXiv 2505.09648, Lemma 2.2: for `n = 2m ≥ 10` and three non-increasing
sequences `a, b, c` in `[0, 1]` of length `n` with averages `A, B, C`, if
`aᵢbⱼ + bⱼcₖ + cₖaᵢ ≤ 1/2 (aᵢ + bⱼ + cₖ)` whenever `i + j + k ≥ n`, then
`AB + BC + CA ≤ 1/2 (A + B + C)`. Same block summations as Shao's Lemma 2.2 (Lemma22.lean),
substitution `x = 4a - 1`, then `half_lemma22_core`.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/
import LeanLab.DensityGoldbach.Lemma22
import LeanLab.DensityGoldbach.AlsetriLemma22Core

open Finset

namespace LeanLab.DensityGoldbach

/-- **Alsetri's Lemma 2.2**, sums form: with `S_a = Σ_{i<n} aᵢ`, `n = 2m ≥ 10`,
`S_a S_b + S_b S_c + S_c S_a ≤ 1/2 n (S_a + S_b + S_c)`. -/
theorem half_lemma22 (m : ℕ) (hm : 5 ≤ m) (a b c : ℕ → ℝ)
    (ha : ∀ i, i < 2 * m → 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, i < 2 * m → 0 ≤ b i ∧ b i ≤ 1)
    (hc : ∀ i, i < 2 * m → 0 ≤ c i ∧ c i ≤ 1)
    (hma : ∀ i j, i ≤ j → j < 2 * m → a j ≤ a i) (hmb : ∀ i j, i ≤ j → j < 2 * m → b j ≤ b i)
    (hmc : ∀ i j, i ≤ j → j < 2 * m → c j ≤ c i)
    (hcond : ∀ i j k, i < 2 * m → j < 2 * m → k < 2 * m → 2 * m ≤ i + j + k →
      a i * b j + b j * c k + c k * a i ≤ 1 / 2 * (a i + b j + c k)) :
    (∑ i ∈ range (2 * m), a i) * (∑ i ∈ range (2 * m), b i)
      + (∑ i ∈ range (2 * m), b i) * (∑ i ∈ range (2 * m), c i)
      + (∑ i ∈ range (2 * m), c i) * (∑ i ∈ range (2 * m), a i)
      ≤ 1 / 2 * (2 * m) * ((∑ i ∈ range (2 * m), a i) + (∑ i ∈ range (2 * m), b i)
        + (∑ i ∈ range (2 * m), c i)) := by
  have : NeZero m := ⟨by omega⟩
  set x : ℕ → ℝ := fun i => 4 * a i - 1 with hx
  set y : ℕ → ℝ := fun i => 4 * b i - 1 with hy
  set z : ℕ → ℝ := fun i => 4 * c i - 1 with hz
  have h3 : ∀ i j k, i < 2 * m → j < 2 * m → k < 2 * m → 2 * m ≤ i + j + k →
      x i * y j + y j * z k + z k * x i ≤ 3 := by
    intro i j k hi hj hk hs
    have := hcond i j k hi hj hk hs
    simp only [hx, hy, hz]
    linear_combination 16 * this
  -- block sums
  set X0 := ∑ i ∈ range m, x i
  set X1 := ∑ i ∈ range m, x (m + i)
  set Y0 := ∑ i ∈ range m, y i
  set Y1 := ∑ i ∈ range m, y (m + i)
  set Z0 := ∑ i ∈ range m, z i
  set Z1 := ∑ i ∈ range m, z (m + i)
  have fs : ∀ f : ℕ → ℝ, ∑ i : Fin m, f i.val = ∑ i ∈ range m, f i :=
    fun f => Fin.sum_univ_eq_sum_range f m
  have fsU : ∀ f : ℕ → ℝ, ∑ i : Fin m, f (m + i.val) = ∑ i ∈ range m, f (m + i) :=
    fun f => Fin.sum_univ_eq_sum_range (fun i => f (m + i)) m
  have lt : ∀ i : Fin m, i.val < m := fun i => i.isLt
  -- pattern bounds
  have pLLU : X0 * Y0 + Y0 * Z1 + Z1 * X0 ≤
      (x 0 * y 0 + y 0 * z m + z m * x 0) + 3 * ((m : ℝ) ^ 2 - 1) := by
    have hs := tri_sum m (fun i => x i.val) (fun j => y j.val) (fun k => z (m + k.val))
    have hb := tri_bound m (fun i j => x i.val * y j.val + y j.val * z (m + (-i - j).val)
      + z (m + (-i - j).val) * x i.val) (fun i j hij => by
        have := idx_ge m i j hij
        have := lt (-i - j); have := lt i; have := lt j
        exact h3 _ _ _ (by omega) (by omega) (by omega) (by omega))
    simp only [fs, fsU] at hs
    rw [hs] at hb
    simpa using hb
  have pLUL : X0 * Y1 + Y1 * Z0 + Z0 * X0 ≤
      (x 0 * y m + y m * z 0 + z 0 * x 0) + 3 * ((m : ℝ) ^ 2 - 1) := by
    have hs := tri_sum m (fun i => x i.val) (fun j => y (m + j.val)) (fun k => z k.val)
    have hb := tri_bound m (fun i j => x i.val * y (m + j.val) + y (m + j.val) * z (-i - j).val
      + z (-i - j).val * x i.val) (fun i j hij => by
        have := idx_ge m i j hij
        have := lt (-i - j); have := lt i; have := lt j
        exact h3 _ _ _ (by omega) (by omega) (by omega) (by omega))
    simp only [fs, fsU] at hs
    rw [hs] at hb
    simpa using hb
  have pULL : X1 * Y0 + Y0 * Z0 + Z0 * X1 ≤
      (x m * y 0 + y 0 * z 0 + z 0 * x m) + 3 * ((m : ℝ) ^ 2 - 1) := by
    have hs := tri_sum m (fun i => x (m + i.val)) (fun j => y j.val) (fun k => z k.val)
    have hb := tri_bound m (fun i j => x (m + i.val) * y j.val + y j.val * z (-i - j).val
      + z (-i - j).val * x (m + i.val)) (fun i j hij => by
        have := idx_ge m i j hij
        have := lt (-i - j); have := lt i; have := lt j
        exact h3 _ _ _ (by omega) (by omega) (by omega) (by omega))
    simp only [fs, fsU] at hs
    rw [hs] at hb
    simpa using hb
  have pUUU : X1 * Y1 + Y1 * Z1 + Z1 * X1 ≤
      (x m * y m + y m * z m + z m * x m) + 3 * ((m : ℝ) ^ 2 - 1) := by
    have hs := tri_sum m (fun i => x (m + i.val)) (fun j => y (m + j.val)) (fun k => z (m + k.val))
    have hb := tri_bound m (fun i j => x (m + i.val) * y (m + j.val)
      + y (m + j.val) * z (m + (-i - j).val) + z (m + (-i - j).val) * x (m + i.val))
      (fun i j _ => by
        have := lt (-i - j); have := lt i; have := lt j
        exact h3 _ _ _ (by omega) (by omega) (by omega) (by omega))
    simp only [fsU] at hs
    rw [hs] at hb
    simpa using hb
  -- pointwise facts
  have xle : ∀ i, i < 2 * m → x i ≤ 3 := fun i hi => by simp only [hx]; linarith [(ha i hi).2]
  have yle : ∀ i, i < 2 * m → y i ≤ 3 := fun i hi => by simp only [hy]; linarith [(hb i hi).2]
  have zle : ∀ i, i < 2 * m → z i ≤ 3 := fun i hi => by simp only [hz]; linarith [(hc i hi).2]
  have xge : ∀ i, i < 2 * m → -1 ≤ x i := fun i hi => by simp only [hx]; linarith [(ha i hi).1]
  have yge : ∀ i, i < 2 * m → -1 ≤ y i := fun i hi => by simp only [hy]; linarith [(hb i hi).1]
  have zge : ∀ i, i < 2 * m → -1 ≤ z i := fun i hi => by simp only [hz]; linarith [(hc i hi).1]
  have xmo : ∀ i j, i ≤ j → j < 2 * m → x j ≤ x i := fun i j h1 h2 => by
    simp only [hx]; linarith [hma i j h1 h2]
  have ymo : ∀ i j, i ≤ j → j < 2 * m → y j ≤ y i := fun i j h1 h2 => by
    simp only [hy]; linarith [hmb i j h1 h2]
  have zmo : ∀ i j, i ≤ j → j < 2 * m → z j ≤ z i := fun i j h1 h2 => by
    simp only [hz]; linarith [hmc i j h1 h2]
  -- upper block bounds `fm - (m - 1) ≤ F1 ≤ m fm`
  have upper : ∀ f : ℕ → ℝ, (∀ i, i < 2 * m → -1 ≤ f i) →
      (∀ i j, i ≤ j → j < 2 * m → f j ≤ f i) →
      f m - (m - 1) ≤ ∑ i ∈ range m, f (m + i) ∧ ∑ i ∈ range m, f (m + i) ≤ m * f m := by
    intro f hge hmo
    constructor
    · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [hk, sum_range_succ', add_zero]
      have : ∑ i ∈ range k, (-1 : ℝ) ≤ ∑ i ∈ range k, f (k + 1 + (i + 1)) :=
        sum_le_sum fun i hi => hge _ (by rw [mem_range] at hi; omega)
      simp only [sum_const, card_range, nsmul_eq_mul] at this
      push_cast; linarith
    · calc ∑ i ∈ range m, f (m + i) ≤ ∑ i ∈ range m, f m :=
            sum_le_sum fun i hi => hmo m (m + i) (by omega) (by rw [mem_range] at hi; omega)
        _ = m * f m := by rw [sum_const, card_range, nsmul_eq_mul]
  obtain ⟨hX1l, hX1u⟩ := upper x xge xmo
  obtain ⟨hY1l, hY1u⟩ := upper y yge ymo
  obtain ⟨hZ1l, hZ1u⟩ := upper z zge zmo
  have t1 := h3 0 m m (by omega) (by omega) (by omega) (by omega)
  have t2 := h3 m 0 m (by omega) (by omega) (by omega) (by omega)
  have t3 := h3 m m 0 (by omega) (by omega) (by omega) (by omega)
  have t4 := h3 m m m (by omega) (by omega) (by omega) (by omega)
  have hm' : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have core := half_lemma22_core m (x 0) (y 0) (z 0) (x m) (y m) (z m) X1 Y1 Z1 hm'
    (xle 0 (by omega)) (yle 0 (by omega)) (zle 0 (by omega))
    (xge m (by omega)) (yge m (by omega)) (zge m (by omega))
    (xmo 0 m (by omega) (by omega)) (ymo 0 m (by omega) (by omega)) (zmo 0 m (by omega) (by omega))
    hX1l hY1l hZ1l hX1u hY1u hZ1u (by linarith) (by linarith) (by linarith)
  -- total in x-form
  have tot : (X0 + X1) * (Y0 + Y1) + (Y0 + Y1) * (Z0 + Z1) + (Z0 + Z1) * (X0 + X1)
      ≤ 12 * (m : ℝ) ^ 2 := by linarith
  have sx : ∑ i ∈ range (2 * m), x i = X0 + X1 := by rw [two_mul, sum_range_add]
  have sy : ∑ i ∈ range (2 * m), y i = Y0 + Y1 := by rw [two_mul, sum_range_add]
  have sz : ∑ i ∈ range (2 * m), z i = Z0 + Z1 := by rw [two_mul, sum_range_add]
  have conv : ∀ f : ℕ → ℝ, ∑ i ∈ range (2 * m), (4 * f i - 1)
      = 4 * ∑ i ∈ range (2 * m), f i - 2 * m := by
    intro f
    rw [sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  rw [← sx, ← sy, ← sz] at tot
  simp only [hx, hy, hz, conv] at tot
  linear_combination (1 / 16) * tot

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.half_lemma22
