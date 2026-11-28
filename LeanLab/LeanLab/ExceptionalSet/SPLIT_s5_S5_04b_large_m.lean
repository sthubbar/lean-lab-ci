/-
Second split, of `leaf_karLemma2_small_large` of `SPLIT_s5_S5_04_small_range`, Karacuba 1971 Lemma 2 p. 243 to 244, by the size
of `m` against `P^(τ/2)`.

* `karLemma2_large_m_s5_04b`: PROVED for every `n ≥ 1` when `P^(τ/2) ≤ m`.
* `leaf_karLemma2_small_large_small_m`: LEAF, the range `m < P^(τ/2)`.
* `leaf_karLemma2_small_large_of_leaves`: the statement of `leaf_karLemma2_small_large` verbatim.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.SPLIT_s5_S5_04_small_range

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-- PROVED. Karacuba Lemma 2 p. 243 to 244 for every `n ≥ 1` when `m ≥ P^(τ/2)`: then
`m^(2ρ/τ) ≥ P^ρ` and `(8 n)^(0.5 n l) > 1`, so the right side exceeds the trivial size `P`. -/
theorem karLemma2_large_m_s5_04b :
    ∀ n m P : ℕ, 1 ≤ n → 0 < m → 0 < P → ∀ α : ℕ → ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
    ∀ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 → 1 < q → (q : ℝ) < (P : ℝ) ^ r → |θ| ≤ 1 →
      α r = a / q + θ / (q : ℝ) ^ 2 → (P : ℝ) ^ (karTau P q r / 2) ≤ (m : ℝ) →
      let τ := karTau P q r
      let l := Real.log (12 * n * (n + 1) / τ)
      let ρ := τ / (3 * (n : ℝ) ^ 2 * l)
      ‖∑ x ∈ Finset.Icc 1 P, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖ <
        (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
  intro n m P hn hm hP α r hr2 hr a q θ hg hq hqP hθ hα hbig τ l ρ
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hP1 : (1 : ℝ) < P := by
    by_contra h
    rw [not_lt] at h
    have hP1' : (P : ℝ) = 1 := le_antisymm h (by exact_mod_cast hP)
    rw [hP1', one_pow] at hqP
    linarith
  obtain ⟨hτ0, hτ1⟩ := s5_04_karTau_pos_le_one P q r hP1 hqR hqP
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h24 : (24 : ℝ) ≤ 12 * n * (n + 1) / τ := by
    rw [le_div_iff₀ hτ0]
    nlinarith
  have hl0 : 0 < l := lt_of_lt_of_le (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) h24)
  have hρ0 : 0 < ρ := by positivity
  have hPpos : (0 : ℝ) < P := by linarith
  have hM : (P : ℝ) ^ ρ ≤ (m : ℝ) ^ (2 * ρ / τ) := by
    have h := Real.rpow_le_rpow (by positivity) hbig (by positivity : (0 : ℝ) ≤ 2 * ρ / τ)
    rw [← Real.rpow_mul hPpos.le] at h
    have he : τ / 2 * (2 * ρ / τ) = ρ := by
      have hττ : τ / τ = 1 := div_self (ne_of_gt hτ0)
      rw [show τ / 2 * (2 * ρ / τ) = ρ * (τ / τ) by ring, hττ, mul_one]
    rw [he] at h
    exact h
  have hA : 1 < (8 * n : ℝ) ^ (0.5 * n * l) := Real.one_lt_rpow (by linarith) (by positivity)
  have hsplit : (P : ℝ) = (P : ℝ) ^ ρ * (P : ℝ) ^ (1 - ρ) := by
    rw [← Real.rpow_add hPpos]; simp
  have hB : 0 < (P : ℝ) ^ (1 - ρ) := Real.rpow_pos_of_pos hPpos _
  have hPρ : 0 < (P : ℝ) ^ ρ := Real.rpow_pos_of_pos hPpos _
  calc ‖∑ x ∈ Finset.Icc 1 P, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖
      ≤ P := s5_04_norm_sum_eC_le P _
    _ = (P : ℝ) ^ ρ * (P : ℝ) ^ (1 - ρ) := hsplit
    _ < (8 * n : ℝ) ^ (0.5 * n * l) * (P : ℝ) ^ ρ * (P : ℝ) ^ (1 - ρ) := by
        have : (P : ℝ) ^ ρ < (8 * n : ℝ) ^ (0.5 * n * l) * (P : ℝ) ^ ρ := by nlinarith
        exact mul_lt_mul_of_pos_right this hB
    _ ≤ (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
        apply mul_le_mul_of_nonneg_right _ hB.le
        exact mul_le_mul_of_nonneg_left hM (by linarith)

/-- LEAF: Karacuba Lemma 2 p. 243 to 244, Vinogradov [2], for 1 ≤ n ≤ 11, in the range
`P ≥ (8 n)^(13 n^3)` and `m < P^(τ/2)`, the only range where neither the trivial bound nor the
factor `m^(2ρ/τ)` gives the claim. HARD. This is the Weyl sum estimate proper: shifts
`x ↦ x + yz`, Holder as in Lemma 4, the mean value count, Lemma 3 for `α_r`. The statement is
`leaf_karLemma2_small_large` with `m < P^(τ/2)` added. -/
theorem leaf_karLemma2_small_large_small_m :
    ∀ n m P : ℕ, 1 ≤ n → n < 12 → 0 < m → 0 < P → ∀ α : ℕ → ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
    ∀ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 → 1 < q → (q : ℝ) < (P : ℝ) ^ r → |θ| ≤ 1 →
      α r = a / q + θ / (q : ℝ) ^ 2 →
      (8 * (n : ℝ)) ^ (13 * n ^ 3) ≤ (P : ℝ) →
      (m : ℝ) < (P : ℝ) ^ (karTau P q r / 2) →
      let τ := karTau P q r
      let l := Real.log (12 * n * (n + 1) / τ)
      let ρ := τ / (3 * (n : ℝ) ^ 2 * l)
      ‖∑ x ∈ Finset.Icc 1 P, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖ <
        (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
  sorry

/-- PROVED from the leaves: the statement of `leaf_karLemma2_small_large` verbatim. -/
theorem leaf_karLemma2_small_large_of_leaves :
    ∀ n m P : ℕ, 1 ≤ n → n < 12 → 0 < m → 0 < P → ∀ α : ℕ → ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
    ∀ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 → 1 < q → (q : ℝ) < (P : ℝ) ^ r → |θ| ≤ 1 →
      α r = a / q + θ / (q : ℝ) ^ 2 →
      (8 * (n : ℝ)) ^ (13 * n ^ 3) ≤ (P : ℝ) →
      let τ := karTau P q r
      let l := Real.log (12 * n * (n + 1) / τ)
      let ρ := τ / (3 * (n : ℝ) ^ 2 * l)
      ‖∑ x ∈ Finset.Icc 1 P, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖ <
        (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
  intro n m P hn1 hn hm hP α r hr2 hr a q θ hg hq hqP hθ hα hlarge
  by_cases hs : (m : ℝ) < (P : ℝ) ^ (karTau P q r / 2)
  · exact leaf_karLemma2_small_large_small_m n m P hn1 hn hm hP α r hr2 hr a q θ hg hq hqP hθ hα hlarge hs
  · exact karLemma2_large_m_s5_04b n m P hn1 hm hP α r hr2 hr a q θ hg hq hqP hθ hα (not_lt.1 hs)

/-- Twin: the assembly has exactly the type of the open leaf. -/
example : type_of% @leaf_karLemma2_small_large := @leaf_karLemma2_small_large_of_leaves

end LeanLab.ExceptionalSet.U1539.KaracubaSplit

#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.karLemma2_large_m_s5_04b
