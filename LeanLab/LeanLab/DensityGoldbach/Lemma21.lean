/-
P0038 Shao 2012, Lemma 2.1: for `n = 2m ≥ 6` and `1 ≥ a₀ ≥ … ≥ a_{n-1} ≥ 0`, if
`aᵢaⱼ + aⱼaₖ + aₖaᵢ ≤ 5/8 (aᵢ + aⱼ + aₖ)` whenever `i + j + k ≥ n`, then the average is at most
`5/8`. Proof as in the paper: `xᵢ = 16/5 aᵢ - 1`, sum the condition over the triples
`(i, j, m + c)` with `c ≡ -i-j mod m`, then two cases on the sign of the upper block sum.
AI-written Lean code, Claude, 2026-10-17, run 20261016T2303Z-22954, unit U-0096.
-/
import Mathlib

open Finset

namespace LeanLab.DensityGoldbach

/-- The real-number core of the proof, after the summation step. -/
lemma lemma21_core (M S0 S1 x0 xm : ℝ) (hM : 3 ≤ M) (hsum : 2 * M < S0 + S1)
    (hS0 : S0 ≤ 11 / 5 * M) (hx0 : x0 ≤ 11 / 5) (hx0m : xm ≤ x0)
    (hprod : xm ^ 2 + 2 * x0 * xm ≤ 3) (hxm : xm ^ 2 ≤ 1) (hS1 : S1 ≤ M * xm)
    (h4 : S0 ^ 2 + 2 * S0 * S1 ≤ 3 * (M ^ 2 - 1) + x0 ^ 2 + 2 * x0 * xm) : False := by
  have hsq : 4 * M ^ 2 < (S0 + S1) ^ 2 := by nlinarith
  have hexp : (S0 + S1) ^ 2 ≤ 3 * M ^ 2 + x0 ^ 2 - xm ^ 2 + S1 ^ 2 := by nlinarith
  rcases le_or_gt S1 0 with h1 | h1
  · -- `S1 ≤ 0`: then `S1 ≥ -M/5`, so `S1² ≤ M²/25`.
    have hlo : -(M / 5) < S1 := by linarith
    have hS1sq : S1 ^ 2 ≤ M ^ 2 / 25 := by nlinarith
    have hx0sq : x0 ^ 2 ≤ (11 / 5) ^ 2 := by
      have : -1 ≤ xm ∨ True := Or.inr trivial
      nlinarith [sq_nonneg xm]
    nlinarith
  · -- `S1 > 0`: then `xm > 0` and `S1² ≤ M² xm²`.
    have hMpos : 0 < M := by linarith
    have hxmpos : 0 < xm := by
      by_contra h; push Not at h; nlinarith
    have hS1sq : S1 ^ 2 ≤ M ^ 2 * xm ^ 2 := by
      have : S1 ^ 2 ≤ (M * xm) ^ 2 := by nlinarith
      nlinarith
    -- (5): `x0² > 1 + (M² - 1) t` with `t = 1 - xm²`.
    obtain ⟨t, ht⟩ : ∃ t : ℝ, xm ^ 2 = 1 - t := ⟨1 - xm ^ 2, by ring⟩
    have h5 : 1 + (M ^ 2 - 1) * t < x0 ^ 2 := by
      have : 4 * M ^ 2 < 3 * M ^ 2 + x0 ^ 2 - xm ^ 2 + M ^ 2 * xm ^ 2 := by linarith
      rw [ht] at this; linarith
    have ht0 : 0 ≤ t := by linarith
    have ht1 : t < 1 := by nlinarith
    have hx0pos : 0 < x0 := by linarith
    have hpr : x0 * xm ≤ 1 + t / 2 := by rw [ht] at hprod; linarith
    have hpr2 : x0 ^ 2 * xm ^ 2 ≤ (1 + t / 2) ^ 2 := by
      have h0 : 0 ≤ x0 * xm := by positivity
      have := mul_le_mul hpr hpr h0 (by linarith)
      nlinarith
    have hkey : (1 + (M ^ 2 - 1) * t) * (1 - t) ≤ (1 + t / 2) ^ 2 := by
      have : (1 + (M ^ 2 - 1) * t) * (1 - t) ≤ x0 ^ 2 * (1 - t) := by
        apply mul_le_mul_of_nonneg_right h5.le; linarith
      rw [ht] at hpr2
      linarith
    have hx0sq : x0 ^ 2 ≤ (11 / 5) ^ 2 := by
      have := mul_le_mul hx0 hx0 hx0pos.le (by norm_num)
      nlinarith
    rcases eq_or_lt_of_le ht0 with h0 | h0
    · -- `t = 0`: `xm = 1`, so `x0 ≤ 1`, but `x0² > 1`.
      rw [← h0] at ht hpr h5
      have hf : (xm - 1) * (xm + 1) = 0 := by ring_nf; linarith
      have hxm1 : xm = 1 := by
        rcases mul_eq_zero.1 hf with h | h
        · linarith
        · linarith
      rw [hxm1] at hpr
      norm_num at hpr h5
      rw [abs_of_pos hx0pos] at h5
      linarith
    · -- `t > 0`: `(M² - 3) ≤ (M² - 3/4) t`, so `x0²` is too large.
      have hq : t * ((M ^ 2 - 3) - (M ^ 2 - 3 / 4) * t) ≤ 0 := by
        linear_combination hkey
      have hlin : (M ^ 2 - 3) ≤ (M ^ 2 - 3 / 4) * t := by
        by_contra hc; push Not at hc
        have : 0 < t * ((M ^ 2 - 3) - (M ^ 2 - 3 / 4) * t) := mul_pos h0 (by linarith)
        linarith
      have hM2 : 9 ≤ M ^ 2 := by
        have := mul_le_mul hM hM (by norm_num) (by linarith)
        linarith
      have hA : 0 < M ^ 2 - 3 / 4 := by linarith
      have hbig : ((11 / 5) ^ 2 - 1) * (M ^ 2 - 3 / 4) < (M ^ 2 - 1) * (M ^ 2 - 3) := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ M ^ 2 - 9) (by linarith : (0:ℝ) ≤ M ^ 2)]
      have h6 : (M ^ 2 - 1) * (M ^ 2 - 3) ≤ ((M ^ 2 - 1) * t) * (M ^ 2 - 3 / 4) := by
        have := mul_le_mul_of_nonneg_left hlin (by linarith : (0:ℝ) ≤ M ^ 2 - 1)
        linarith
      have h7 : (11 / 5) ^ 2 - 1 < (M ^ 2 - 1) * t := by
        by_contra hc; push Not at hc
        have := mul_le_mul_of_nonneg_right hc hA.le
        linarith
      linarith

/-- The index fact: for `i, j : Fin m` and `c = -i - j`, either `i = j = 0` or
`i + j + c ≥ m`. -/
lemma idx_ge (m : ℕ) [NeZero m] (i j : Fin m) (hij : (i, j) ≠ (0, 0)) :
    m ≤ i.val + j.val + (-i - j).val := by
  set c := -i - j with hc
  have h0 : i + j + c = 0 := by rw [hc]; abel
  have hv := congrArg Fin.val h0
  rw [Fin.val_add, Fin.val_add, Fin.val_zero] at hv
  have hcl : c.val < m := c.isLt
  have hmod : (i.val + j.val + c.val) % m = 0 := by
    rw [Nat.add_mod (i.val + j.val) c.val, Nat.mod_eq_of_lt hcl]
    exact hv
  by_contra hlt
  push Not at hlt
  rw [Nat.mod_eq_of_lt hlt] at hmod
  apply hij
  have hi : i.val = 0 := by omega
  have hj : j.val = 0 := by omega
  simp only [Prod.mk.injEq]
  exact ⟨Fin.ext hi, Fin.ext hj⟩

/-- **Shao's Lemma 2.1**, for `n = 2m ≥ 6`, indices `0, …, n - 1`, triples not necessarily
distinct. -/
theorem shao_lemma21 (m : ℕ) (hm : 3 ≤ m) (a : ℕ → ℝ)
    (hbd : ∀ i, i < 2 * m → 0 ≤ a i ∧ a i ≤ 1)
    (hmono : ∀ i j, i ≤ j → j < 2 * m → a j ≤ a i)
    (hcond : ∀ i j k, i < 2 * m → j < 2 * m → k < 2 * m → 2 * m ≤ i + j + k →
      a i * a j + a j * a k + a k * a i ≤ 5 / 8 * (a i + a j + a k)) :
    ∑ i ∈ range (2 * m), a i ≤ 5 / 8 * (2 * m) := by
  have : NeZero m := ⟨by omega⟩
  by_contra hcon
  push Not at hcon
  set x : ℕ → ℝ := fun i => 16 / 5 * a i - 1 with hxdef
  have hx3 : ∀ i j k, i < 2 * m → j < 2 * m → k < 2 * m → 2 * m ≤ i + j + k →
      x i * x j + x j * x k + x k * x i ≤ 3 := by
    intro i j k hi hj hk hs
    have := hcond i j k hi hj hk hs
    simp only [hxdef]
    linear_combination (256 / 25) * this
  have hxle : ∀ i, i < 2 * m → x i ≤ 11 / 5 := by
    intro i hi; simp only [hxdef]; linarith [(hbd i hi).2]
  have hxmono : ∀ i j, i ≤ j → j < 2 * m → x j ≤ x i := by
    intro i j hij hj; simp only [hxdef]; linarith [hmono i j hij hj]
  set S0 := ∑ i ∈ range m, x i with hS0def
  set S1 := ∑ i ∈ range m, x (m + i) with hS1def
  have hsplit : ∑ i ∈ range (2 * m), x i = S0 + S1 := by
    rw [two_mul, sum_range_add]
  have hxsum : ∑ i ∈ range (2 * m), x i = 16 / 5 * ∑ i ∈ range (2 * m), a i - 2 * m := by
    simp only [hxdef, sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
    push_cast; ring
  have hM : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hsum : 2 * (m : ℝ) < S0 + S1 := by rw [← hsplit, hxsum]; linarith
  have hS0 : S0 ≤ 11 / 5 * m := by
    calc S0 ≤ ∑ i ∈ range m, (11 / 5 : ℝ) :=
          sum_le_sum fun i hi => hxle i (by rw [mem_range] at hi; omega)
      _ = 11 / 5 * m := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hS1 : S1 ≤ m * x m := by
    calc S1 ≤ ∑ i ∈ range m, x m :=
          sum_le_sum fun i hi => hxmono m (m + i) (by omega) (by rw [mem_range] at hi; omega)
      _ = m * x m := by rw [sum_const, card_range, nsmul_eq_mul]
  have hx0 : x 0 ≤ 11 / 5 := hxle 0 (by omega)
  have hx0m : x m ≤ x 0 := hxmono 0 m (by omega) (by omega)
  have hprod : x m ^ 2 + 2 * x 0 * x m ≤ 3 := by
    have := hx3 m m 0 (by omega) (by omega) (by omega) (by omega); nlinarith
  have hxm : x m ^ 2 ≤ 1 := by
    have := hx3 m m m (by omega) (by omega) (by omega) (by omega); nlinarith
  -- The summation over the triples `(i, j, m + c)`, `c = -i - j` in `Fin m`.
  set T : Fin m → Fin m → ℝ := fun i j =>
    x i.val * x j.val + x j.val * x (m + (-i - j).val) + x (m + (-i - j).val) * x i.val with hT
  have hS0f : ∑ i : Fin m, x i.val = S0 := Fin.sum_univ_eq_sum_range x m
  have hS1f : ∑ i : Fin m, x (m + i.val) = S1 := Fin.sum_univ_eq_sum_range (fun i => x (m + i)) m
  have hrot1 : ∀ j : Fin m, ∑ i : Fin m, x (m + (-i - j).val) = S1 := by
    intro j
    rw [← hS1f]
    exact Fintype.sum_equiv (Equiv.subLeft (-j)) _ _ (fun i => by
      simp only [Equiv.subLeft_apply]; congr 3; abel)
  have hrot2 : ∀ i : Fin m, ∑ j : Fin m, x (m + (-i - j).val) = S1 := by
    intro i
    rw [← hS1f]
    exact Fintype.sum_equiv (Equiv.subLeft (-i)) _ _ (fun j => by
      simp only [Equiv.subLeft_apply])
  have hA : ∑ i : Fin m, ∑ j : Fin m, T i j = S0 ^ 2 + 2 * S0 * S1 := by
    simp only [hT, sum_add_distrib]
    have e1 : ∑ i : Fin m, ∑ j : Fin m, x i.val * x j.val = S0 ^ 2 := by
      rw [← hS0f, sq, sum_mul_sum]
    have e2 : ∑ i : Fin m, ∑ j : Fin m, x j.val * x (m + (-i - j).val) = S0 * S1 := by
      rw [sum_comm]
      simp only [← mul_sum, hrot1]
      rw [← sum_mul, hS0f]
    have e3 : ∑ i : Fin m, ∑ j : Fin m, x (m + (-i - j).val) * x i.val = S0 * S1 := by
      simp only [← sum_mul, hrot2]
      rw [← mul_sum, hS0f, mul_comm]
    rw [e1, e2, e3]; ring
  have hT00 : T 0 0 = x 0 ^ 2 + 2 * x 0 * x m := by
    simp only [hT, neg_zero, sub_zero, Fin.val_zero, add_zero]; ring
  have hTle : ∀ p ∈ (univ : Finset (Fin m × Fin m)).erase (0, 0), T p.1 p.2 ≤ 3 := by
    intro p hp
    have hne : (p.1, p.2) ≠ (0, 0) := by simpa using (mem_erase.1 hp).1
    have hge := idx_ge m p.1 p.2 hne
    have hc : (-p.1 - p.2).val < m := (-p.1 - p.2).isLt
    exact hx3 _ _ _ (by have := p.1.isLt; omega) (by have := p.2.isLt; omega) (by omega)
      (by omega)
  have hB : ∑ i : Fin m, ∑ j : Fin m, T i j ≤ x 0 ^ 2 + 2 * x 0 * x m + 3 * ((m : ℝ) ^ 2 - 1) := by
    rw [← Fintype.sum_prod_type', ← add_sum_erase _ _ (mem_univ ((0 : Fin m), (0 : Fin m)))]
    have hcard : #((univ : Finset (Fin m × Fin m)).erase (0, 0)) = m * m - 1 := by
      rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_prod, Fintype.card_fin]
    have hle := sum_le_card_nsmul _ _ _ hTle
    rw [hcard, nsmul_eq_mul] at hle
    have hm1 : 1 ≤ m * m := by nlinarith
    rw [Nat.cast_sub hm1] at hle
    push_cast at hle
    simp only at hT00 ⊢
    rw [hT00]; nlinarith
  have h4 : S0 ^ 2 + 2 * S0 * S1 ≤ 3 * ((m : ℝ) ^ 2 - 1) + x 0 ^ 2 + 2 * x 0 * x m := by
    rw [← hA]; linarith
  exact lemma21_core m S0 S1 (x 0) (x m) hM hsum hS0 hx0 hx0m hprod hxm hS1 h4

end LeanLab.DensityGoldbach
