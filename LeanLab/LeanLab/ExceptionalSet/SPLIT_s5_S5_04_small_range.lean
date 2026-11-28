/-
Split of `leaf_karLemma2_small` of `KarLemma2Split`, Karacuba Lemma 2 p. 243 to 244 of
Trudy Mat. Inst. Steklov 112 (1971) for the degrees `1 ≤ n ≤ 11`. The paper states Lemma 2
without proof, citing Vinogradov [2]; the split is by the size of `P`.

* `karLemma2_trivial_range_s5_04`: PROVED for all `n ≥ 1` with `P < (8 n)^(13 n^3)`, by the
  trivial bound, since `τ` lies in `(0, 1]` and `l = log(12 n(n+1)/τ) ≥ log 24 > 3`. In
  particular the statement is not false at small parameters: `l` is never negative or small.
* `leaf_karLemma2_small_large`: LEAF, the range `P ≥ (8 n)^(13 n^3)`, `n ≤ 11`.
* `leaf_karLemma2_small_of_leaves`: the statement of `leaf_karLemma2_small` verbatim.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.KarLemma2Split

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-- PROVED. Karacuba p. 243: the `τ` of Lemma 2 lies in `(0, 1]` when `1 < q < P^r`. -/
theorem s5_04_karTau_pos_le_one (P : ℝ) (q : ℝ) (r : ℕ) (hP : 1 < P) (hq : 1 < q)
    (hqP : q < P ^ r) : 0 < karTau P q r ∧ karTau P q r ≤ 1 := by
  have hLP : 0 < Real.log P := Real.log_pos hP
  have hLq : 0 < Real.log q := Real.log_pos hq
  unfold karTau
  split_ifs with h1 h2
  · have : Real.log q ≤ Real.log P := Real.log_le_log (by linarith) h1
    exact ⟨div_pos hLq hLP, (div_le_one hLP).2 this⟩
  · exact ⟨one_pos, le_rfl⟩
  · rw [not_le] at h1 h2
    have hr1 : (1:ℕ) ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; simp at hqP; linarith
      · exact h
    have hlo : Real.log (P ^ (r - 1)) < Real.log q :=
      Real.log_lt_log (by positivity) h2
    have hhi : Real.log q < Real.log (P ^ r) := Real.log_lt_log (by linarith) hqP
    rw [Real.log_pow] at hlo hhi
    have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub hr1]; simp
    rw [hcast] at hlo
    constructor
    · have : Real.log q / Real.log P < r := by
        rw [div_lt_iff₀ hLP]; linarith
      linarith
    · have : (r : ℝ) - 1 < Real.log q / Real.log P := by
        rw [lt_div_iff₀ hLP]; linarith
      linarith

/-- PROVED. The trivial bound `|Σ_{x=1}^P e(g(x))| ≤ P`. -/
theorem s5_04_norm_sum_eC_le (P : ℕ) (g : ℕ → ℝ) :
    ‖∑ x ∈ Finset.Icc 1 P, eC (g x)‖ ≤ (P : ℝ) := by
  calc ‖∑ x ∈ Finset.Icc 1 P, eC (g x)‖ ≤ ∑ x ∈ Finset.Icc 1 P, ‖eC (g x)‖ := norm_sum_le _ _
    _ = P := by simp [norm_eC]

/-- PROVED. Karacuba Lemma 2 p. 243 to 244 for every `n ≥ 1` in the range
`P < (8 n)^(13 n^3)`, from the trivial bound `|S| ≤ P`: there `P^ρ < (8 n)^(0.5 n l)` because
`τ ≤ 1` and `l ≥ log 24 > 3`. -/
theorem karLemma2_trivial_range_s5_04 :
    ∀ n m P : ℕ, 1 ≤ n → 0 < m → 0 < P → ∀ α : ℕ → ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
    ∀ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 → 1 < q → (q : ℝ) < (P : ℝ) ^ r → |θ| ≤ 1 →
      α r = a / q + θ / (q : ℝ) ^ 2 → (P : ℝ) < (8 * (n : ℝ)) ^ (13 * n ^ 3) →
      let τ := karTau P q r
      let l := Real.log (12 * n * (n + 1) / τ)
      let ρ := τ / (3 * (n : ℝ) ^ 2 * l)
      ‖∑ x ∈ Finset.Icc 1 P, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖ <
        (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
  intro n m P hn hm hP α r hr2 hr a q θ hg hq hqP hθ hα hsmall τ l ρ
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hP1 : (1 : ℝ) < P := by
    by_contra h
    rw [not_lt] at h
    have hP1' : (P : ℝ) = 1 := le_antisymm h (by exact_mod_cast hP)
    rw [hP1', one_pow] at hqP
    linarith
  obtain ⟨hτ0, hτ1⟩ := s5_04_karTau_pos_le_one P q r hP1 hqR hqP
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLP : 0 < Real.log P := Real.log_pos hP1
  -- l ≥ log 24 > 3
  have h24 : (24 : ℝ) ≤ 12 * n * (n + 1) / τ := by
    rw [le_div_iff₀ hτ0]
    nlinarith
  have hl3 : 3 < l := by
    have he : Real.exp 3 < 24 := by
      have := Real.exp_one_lt_d9
      have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h3]
      have h0 : 0 < Real.exp 1 := Real.exp_pos 1
      nlinarith [pow_le_pow_left₀ h0.le this.le 3]
    calc (3 : ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
      _ < Real.log 24 := Real.log_lt_log (Real.exp_pos 3) he
      _ ≤ l := Real.log_le_log (by norm_num) h24
  have hl0 : 0 < l := by linarith
  have hK : 0 < Real.log (8 * (n : ℝ)) := Real.log_pos (by linarith)
  have hLsmall : Real.log P < 13 * (n : ℝ) ^ 3 * Real.log (8 * (n : ℝ)) := by
    have := Real.log_lt_log (by linarith) hsmall
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hρ0 : 0 < ρ := by positivity
  -- key: ρ log P < 0.5 n l log (8n)
  have hkey : ρ * Real.log P < 0.5 * n * l * Real.log (8 * (n : ℝ)) := by
    have hden : 0 < 3 * (n : ℝ) ^ 2 * l := by positivity
    have hρdef : ρ = τ / (3 * (n : ℝ) ^ 2 * l) := rfl
    rw [hρdef, div_mul_eq_mul_div, div_lt_iff₀ hden]
    have h1 : τ * Real.log P ≤ Real.log P := by nlinarith
    have hn3 : 0 < (n : ℝ) ^ 3 := by positivity
    have h2 : 13 * (n : ℝ) ^ 3 * Real.log (8 * (n : ℝ)) ≤
        0.5 * n * l * Real.log (8 * (n : ℝ)) * (3 * (n : ℝ) ^ 2 * l) := by
      have : 0.5 * n * l * Real.log (8 * (n : ℝ)) * (3 * (n : ℝ) ^ 2 * l)
          = 1.5 * l ^ 2 * ((n : ℝ) ^ 3 * Real.log (8 * (n : ℝ))) := by ring
      rw [this]
      have hl9 : 9 ≤ l ^ 2 := by nlinarith
      have hpos : 0 < (n : ℝ) ^ 3 * Real.log (8 * (n : ℝ)) := by positivity
      nlinarith
    linarith
  have hPpos : (0 : ℝ) < P := by linarith
  have hA : (P : ℝ) ^ ρ < (8 * n : ℝ) ^ (0.5 * n * l) := by
    rw [Real.rpow_def_of_pos hPpos, Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_lt_exp.2
    linarith [mul_comm (Real.log P) ρ]
  have hM : (1 : ℝ) ≤ (m : ℝ) ^ (2 * ρ / τ) := by
    apply Real.one_le_rpow (by exact_mod_cast hm) (by positivity)
  have hsplit : (P : ℝ) = (P : ℝ) ^ ρ * (P : ℝ) ^ (1 - ρ) := by
    rw [← Real.rpow_add hPpos]; simp
  have hB : 0 < (P : ℝ) ^ (1 - ρ) := Real.rpow_pos_of_pos hPpos _
  calc ‖∑ x ∈ Finset.Icc 1 P, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖
      ≤ P := s5_04_norm_sum_eC_le P _
    _ = (P : ℝ) ^ ρ * (P : ℝ) ^ (1 - ρ) := hsplit
    _ < (8 * n : ℝ) ^ (0.5 * n * l) * (P : ℝ) ^ (1 - ρ) := by
        exact mul_lt_mul_of_pos_right hA hB
    _ ≤ (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
        have hApos : 0 < (8 * n : ℝ) ^ (0.5 * n * l) := Real.rpow_pos_of_pos (by linarith) _
        nlinarith [mul_le_mul_of_nonneg_left hM hApos.le]


/-- LEAF: Karacuba Lemma 2 p. 243 to 244 for `1 ≤ n ≤ 11` in the range `P ≥ (8 n)^(13 n^3)`, where
the trivial bound `|S| ≤ P` no longer gives the claim, Vinogradov [2]. HARD. Needs Vinogradov's
mean value estimate in degree `n < 12`, which `KarLemma1` does not state, then the same Weyl
shift, Holder and Lemma 3 argument as for `n ≥ 12`. The statement is `leaf_karLemma2_small`
with `(8 n)^(13 n^3) ≤ P` added. -/
theorem leaf_karLemma2_small_large :
    ∀ n m P : ℕ, 1 ≤ n → n < 12 → 0 < m → 0 < P → ∀ α : ℕ → ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
    ∀ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 → 1 < q → (q : ℝ) < (P : ℝ) ^ r → |θ| ≤ 1 →
      α r = a / q + θ / (q : ℝ) ^ 2 →
      (8 * (n : ℝ)) ^ (13 * n ^ 3) ≤ (P : ℝ) →
      let τ := karTau P q r
      let l := Real.log (12 * n * (n + 1) / τ)
      let ρ := τ / (3 * (n : ℝ) ^ 2 * l)
      ‖∑ x ∈ Finset.Icc 1 P, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖ <
        (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
  sorry

/-- PROVED from the leaves: the statement of `leaf_karLemma2_small` verbatim. -/
theorem leaf_karLemma2_small_of_leaves :
    ∀ n m P : ℕ, 1 ≤ n → n < 12 → 0 < m → 0 < P → ∀ α : ℕ → ℝ, ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
    ∀ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 → 1 < q → (q : ℝ) < (P : ℝ) ^ r → |θ| ≤ 1 →
      α r = a / q + θ / (q : ℝ) ^ 2 →
      let τ := karTau P q r
      let l := Real.log (12 * n * (n + 1) / τ)
      let ρ := τ / (3 * (n : ℝ) ^ 2 * l)
      ‖∑ x ∈ Finset.Icc 1 P, eC (m * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖ <
        (8 * n : ℝ) ^ (0.5 * n * l) * (m : ℝ) ^ (2 * ρ / τ) * (P : ℝ) ^ (1 - ρ) := by
  intro n m P hn1 hn hm hP α r hr2 hr a q θ hg hq hqP hθ hα
  by_cases hs : (8 * (n : ℝ)) ^ (13 * n ^ 3) ≤ (P : ℝ)
  · exact leaf_karLemma2_small_large n m P hn1 hn hm hP α r hr2 hr a q θ hg hq hqP hθ hα hs
  · exact karLemma2_trivial_range_s5_04 n m P hn1 hm hP α r hr2 hr a q θ hg hq hqP hθ hα (not_le.1 hs)

/-- Twin: the assembly has exactly the type of the open leaf. -/
example : type_of% @leaf_karLemma2_small := @leaf_karLemma2_small_of_leaves

end LeanLab.ExceptionalSet.U1539.KaracubaSplit

#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.karLemma2_trivial_range_s5_04
