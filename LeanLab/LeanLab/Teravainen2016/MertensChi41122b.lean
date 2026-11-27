/-
P0076, Section 4, page 15: split of leaf_mertens_chi4 in MertensMod4Bias.lean, the Mertens
theorem for the character chi_4, along Davenport, Multiplicative Number Theory, Chapter 4,
specialised to chi_4 where L 1 chi_4 = pi / 4 is the Leibniz series.
Writing chi for chi_4, Lambda for the von Mangoldt function and P y for the partial sum of
chi m / m over m at most y:
  sum over n at most N of chi n log n / n = sum over d at most N of chi d Lambda d / d * P (N / d),
and P (N / d) = pi / 4 + O (d / N), so pi / 4 times the sum of chi d Lambda d / d is
O 1 + O (psi N / N) = O 1 by Chebyshev, then prime powers p ^ k with k at least 2 are removed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.MertensMod4Bias

open Finset Real
open scoped Classical ArithmeticFunction.vonMangoldt
open Filter

namespace LeanLab.Teravainen2016


/-- chi_4 on odd and even arguments. -/
lemma chi4_odd1122b (χ : ℕ → ℝ)
    (hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0) (j : ℕ) :
    χ (2 * j + 1) = (-1) ^ j ∧ χ (2 * j + 2) = 0 := by
  rcases Nat.even_or_odd' j with ⟨t, rfl | rfl⟩
  · refine ⟨?_, ?_⟩
    · rw [hχ, if_pos (by omega), pow_mul]; simp
    · rw [hχ, if_neg (by omega), if_neg (by omega)]
  · refine ⟨?_, ?_⟩
    · rw [hχ, if_neg (by omega), if_pos (by omega), pow_succ, pow_mul]; simp
    · rw [hχ, if_neg (by omega), if_neg (by omega)]

/-- the partial sums of chi_4 m / m are the Leibniz partial sums. -/
lemma chi4_sum_alt1122b (χ : ℕ → ℝ)
    (hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0) (j : ℕ) :
    ∑ m ∈ Ioc 0 (2 * j), χ m / m = ∑ i ∈ range j, (-1 : ℝ) ^ i * (1 / (2 * i + 1)) ∧
    ∑ m ∈ Ioc 0 (2 * j + 1), χ m / m = ∑ i ∈ range (j + 1), (-1 : ℝ) ^ i * (1 / (2 * i + 1)) := by
  induction j with
  | zero =>
    refine ⟨by simp, ?_⟩
    rw [show 2 * 0 + 1 = 1 by rfl]
    simp [hχ]
  | succ j ih =>
    have h1 : ∑ m ∈ Ioc 0 (2 * (j + 1)), χ m / m = ∑ m ∈ Ioc 0 (2 * j + 1), χ m / m := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Finset.sum_Ioc_succ_top (by omega),
        show 2 * j + 1 + 1 = 2 * j + 2 by ring, (chi4_odd1122b χ hχ j).2]
      simp
    refine ⟨by rw [h1, ih.2], ?_⟩
    rw [Finset.sum_Ioc_succ_top (by omega), h1, ih.2, sum_range_succ _ (j + 1),
      show 2 * (j + 1) + 1 = 2 * (j + 1) + 1 by rfl, (chi4_odd1122b χ hχ (j + 1)).1]
    push_cast; ring

/-- alternating series remainder for the Leibniz series, Real.tendsto_sum_pi_div_four. -/
lemma leibniz_alt_bound1122b (j : ℕ) :
    |∑ i ∈ range j, (-1 : ℝ) ^ i * (1 / (2 * i + 1)) - π / 4| ≤ 1 / (2 * j + 1) := by
  set f : ℕ → ℝ := fun i => 1 / (2 * i + 1) with hf
  have hfa : Antitone f := antitone_iff_forall_lt.mpr fun a b hab => by
    simp only [hf]; gcongr
  have hl : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * f i) atTop (nhds (π / 4)) := by
    have := Real.tendsto_sum_pi_div_four
    refine this.congr (fun n => ?_)
    apply sum_congr rfl; intro i _; simp [hf, div_eq_mul_inv]
  change |∑ i ∈ range j, (-1 : ℝ) ^ i * f i - π / 4| ≤ f j
  rcases Nat.even_or_odd' j with ⟨t, rfl | rfl⟩
  · have a := hfa.alternating_series_le_tendsto hl t
    have b := hfa.tendsto_le_alternating_series hl t
    rw [sum_range_succ, pow_mul] at b
    simp at b
    rw [abs_le]; constructor <;> linarith
  · have a := hfa.alternating_series_le_tendsto hl (t + 1)
    have b := hfa.tendsto_le_alternating_series hl t
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring, sum_range_succ, pow_succ, pow_mul] at a
    simp at a
    rw [abs_le]; constructor <;> linarith

/-- Proved, formerly a LEAF: Davenport Chapter 4 input, the Leibniz series with its alternating
tail bound: the partial sum of chi_4 m / m over 1 ≤ m ≤ k differs from L 1 chi_4 = pi / 4 by at
most 1 / k. From Real.tendsto_sum_pi_div_four and the alternating series remainder estimate. -/
theorem leaf_chi4_leibniz_tail1122b (χ : ℕ → ℝ)
    (hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0)
    (k : ℕ) (hk : 1 ≤ k) :
    |∑ m ∈ Ioc 0 k, χ m / m - π / 4| ≤ 1 / k := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [(chi4_sum_alt1122b χ hχ j).1]
    refine (leibniz_alt_bound1122b j).trans ?_
    have : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    push_cast
    gcongr; linarith
  · rw [(chi4_sum_alt1122b χ hχ j).2]
    refine (leibniz_alt_bound1122b (j + 1)).trans ?_
    push_cast
    gcongr; linarith

/-- chi_4 weighted partial sums are alternating sums over odd arguments. -/
lemma chi4_sum_weighted1122b (χ : ℕ → ℝ)
    (hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0)
    (w : ℕ → ℝ) (j : ℕ) :
    ∑ m ∈ Ioc 0 (2 * j), χ m * w m = ∑ i ∈ range j, (-1 : ℝ) ^ i * w (2 * i + 1) ∧
    ∑ m ∈ Ioc 0 (2 * j + 1), χ m * w m = ∑ i ∈ range (j + 1), (-1 : ℝ) ^ i * w (2 * i + 1) := by
  induction j with
  | zero =>
    refine ⟨by simp, ?_⟩
    rw [show 2 * 0 + 1 = 1 by rfl]
    simp [hχ]
  | succ j ih =>
    have h1 : ∑ m ∈ Ioc 0 (2 * (j + 1)), χ m * w m = ∑ m ∈ Ioc 0 (2 * j + 1), χ m * w m := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Finset.sum_Ioc_succ_top (by omega),
        show 2 * j + 1 + 1 = 2 * j + 2 by ring, (chi4_odd1122b χ hχ j).2]
      simp
    refine ⟨by rw [h1, ih.2], ?_⟩
    rw [Finset.sum_Ioc_succ_top (by omega), h1, ih.2, sum_range_succ _ (j + 1),
      (chi4_odd1122b χ hχ (j + 1)).1]

/-- partial sums of an alternating series with antitone nonnegative terms lie in [0, h 0]. -/
lemma alt_antitone_bound1122b : ∀ (n : ℕ) (h : ℕ → ℝ), Antitone h → (∀ i, 0 ≤ h i) →
    0 ≤ ∑ i ∈ range n, (-1 : ℝ) ^ i * h i ∧ ∑ i ∈ range n, (-1 : ℝ) ^ i * h i ≤ h 0 := by
  intro n
  induction n with
  | zero => intro h _ h0; simp [h0 0]
  | succ n ih =>
    intro h ha h0
    have := ih (fun i => h (i + 1)) (fun a b hab => ha (by omega)) (fun i => h0 _)
    rw [sum_range_succ']
    simp only [pow_succ, pow_zero, one_mul, mul_neg_one, neg_mul, sum_neg_distrib] at this ⊢
    have h10 : h 1 ≤ h 0 := ha (by omega)
    constructor <;> linarith [this.1, this.2]

/-- Proved, formerly a LEAF: Davenport Chapter 4, the bound for the sum of chi_4 n log n / n over
n at most N: it is an alternating series in the odd n whose terms log n / n decrease for n at
least 3, so its partial sums are bounded, here by log 3 / 3. -/
theorem leaf_chi4_log_sum_bounded1122b (χ : ℕ → ℝ)
    (hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, |∑ n ∈ Ioc 0 N, χ n * log n / n| ≤ B := by
  set w : ℕ → ℝ := fun n => log n / n with hw
  set g : ℕ → ℝ := fun i => w (2 * (i + 1) + 1) with hg
  have hga : Antitone g := by
    intro a b hab
    simp only [hg, hw]
    have he : exp 1 ≤ (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
    apply Real.log_div_self_antitoneOn
    · simp only [Set.mem_Ici]; push_cast; linarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a)]
    · simp only [Set.mem_Ici]; push_cast; linarith [(Nat.cast_nonneg b : (0:ℝ) ≤ b)]
    · push_cast; gcongr
  have hg0 : ∀ i, 0 ≤ g i := fun i => by
    simp only [hg, hw]; apply div_nonneg (Real.log_nonneg (by push_cast; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)])) (by positivity)
  have key : ∀ j : ℕ, |∑ i ∈ range j, (-1 : ℝ) ^ i * w (2 * i + 1)| ≤ g 0 := by
    intro j
    rcases j with _ | j
    · simp [hg0 0]
    rw [sum_range_succ']
    have := alt_antitone_bound1122b j g hga hg0
    have hw1 : w (2 * 0 + 1) = 0 := by simp [hw]
    rw [hw1, mul_zero, add_zero]
    have hre : ∑ i ∈ range j, (-1 : ℝ) ^ (i + 1) * w (2 * (i + 1) + 1) =
        -∑ i ∈ range j, (-1 : ℝ) ^ i * g i := by
      rw [← sum_neg_distrib]; apply sum_congr rfl; intro i _; simp [hg, pow_succ]
    rw [hre, abs_neg, abs_le]; constructor <;> linarith [this.1, this.2, hg0 0]
  refine ⟨g 0, hg0 0, fun N => ?_⟩
  have hcongr : ∀ M, ∑ n ∈ Ioc 0 M, χ n * log n / n = ∑ n ∈ Ioc 0 M, χ n * w n := fun M => by
    apply sum_congr rfl; intro n _; simp [hw, mul_div_assoc]
  rw [hcongr]
  rcases Nat.even_or_odd' N with ⟨j, rfl | rfl⟩
  · rw [(chi4_sum_weighted1122b χ hχ w j).1]; exact key j
  · rw [(chi4_sum_weighted1122b χ hχ w j).2]; exact key (j + 1)


/-- chi_4 is completely multiplicative. -/
lemma chi4_mul1122b (χ : ℕ → ℝ)
    (hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0) (a b : ℕ) :
    χ (a * b) = χ a * χ b := by
  rw [hχ, hχ a, hχ b, Nat.mul_mod]
  have ha := Nat.mod_lt a (show 4 > 0 by norm_num)
  have hb := Nat.mod_lt b (show 4 > 0 by norm_num)
  generalize a % 4 = r at *
  generalize b % 4 = s at *
  interval_cases r <;> interval_cases s <;> norm_num

/-- Proved, formerly a LEAF: Davenport Chapter 4, the identity log n = sum over d dividing n of
Lambda d together with complete multiplicativity of chi_4, regrouped by d with Mathlib's
ArithmeticFunction.sum_Ioc_mul_eq_sum_sum: the sum of chi_4 n log n / n over n at most N
equals the sum over d at most N of chi_4 d Lambda d / d times the partial sum of chi_4 m / m
over m at most N / d. -/
theorem leaf_chi4_log_convolution1122b (χ : ℕ → ℝ)
    (hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, χ n * log n / n =
      ∑ d ∈ Ioc 0 N, χ d * Λ d / d * ∑ m ∈ Ioc 0 (N / d), χ m / m := by
  let f : ArithmeticFunction ℝ := ⟨fun n => χ n * Λ n / n, by simp⟩
  let g : ArithmeticFunction ℝ := ⟨fun n => χ n / n, by simp⟩
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum f g N
  have hf : ∀ n, f n = χ n * Λ n / n := fun n => rfl
  have hg : ∀ n, g n = χ n / n := fun n => rfl
  simp only [hf, hg] at h
  rw [← h]
  apply sum_congr rfl
  intro n hn
  rw [mem_Ioc] at hn
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)]
  simp only [hf, hg]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn.1
  rw [← ArithmeticFunction.vonMangoldt_sum, mul_sum, sum_div]
  apply sum_congr rfl
  intro i hi
  have hdvd : i ∣ n := Nat.dvd_of_mem_divisors hi
  have hipos : 0 < i := Nat.pos_of_dvd_of_pos hdvd hn.1
  have hmul : i * (n / i) = n := Nat.mul_div_cancel' hdvd
  have hcast : (i : ℝ) * ((n / i : ℕ) : ℝ) = n := by exact_mod_cast hmul
  have hchi : χ i * χ (n / i) = χ n := by rw [← chi4_mul1122b χ hχ, hmul]
  have hir : (0 : ℝ) < i := by exact_mod_cast hipos
  have hqr : (0 : ℝ) < ((n / i : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_pos (Nat.le_of_dvd hn.1 hdvd) hipos
  rw [← hcast, ← hchi]
  field_simp

/-- Helper: If Λ d ≠ 0, then d is a prime power p^k with k ≥ 1, and Λ d = log p. -/
lemma vonMangoldt_char1122b {d : ℕ} (hd : Λ d ≠ 0) :
    ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ p ^ k = d ∧ Λ d = Real.log p := by
  have h₁ : IsPrimePow d := by
    rw [ArithmeticFunction.vonMangoldt_ne_zero_iff] at hd
    exact hd
  obtain ⟨p, k, hp, hk, h_d⟩ := h₁
  have h₂ : Λ (p ^ k) = Real.log p := by
    -- Use the property of vonMangoldt for prime powers
    have h₃ : Λ (p ^ k) = Real.log p := by
      rw [show (p : ℕ) ^ k = p ^ k by rfl]
      -- Use the property of vonMangoldt for prime powers
      have h₄ : Λ (p ^ k) = Real.log p := by
        rw [ArithmeticFunction.vonMangoldt_apply_prime_pow hp]
      exact h₄
    exact h₃
  refine' ⟨p, k, hp, hk, _⟩
  <;> simp_all [h_d]
  <;> norm_num
  <;> linarith

/-- Helper: log p ≤ 2√p for p ≥ 1. -/
lemma log_le_two_sqrt1122b (p : ℕ) (hp : 1 ≤ p) : Real.log (p : ℝ) ≤ 2 * Real.sqrt (p : ℝ) := by
  have h₁ : Real.log (p : ℝ) ≤ 2 * Real.sqrt (p : ℝ) := by
    have h₂ : (0 : ℝ) < (p : ℝ) := by positivity
    have h₃ : Real.log (p : ℝ) = 2 * Real.log (Real.sqrt (p : ℝ)) := by
      have h₄ : Real.sqrt (p : ℝ) ≥ 0 := Real.sqrt_nonneg _
      have h₅ : Real.log (p : ℝ) = Real.log (Real.sqrt (p : ℝ) ^ 2) := by
        have h₆ : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := by
          rw [Real.sq_sqrt] <;> positivity
        rw [h₆]
      rw [h₄]
      have h₅ : Real.log (Real.sqrt (p : ℝ) ^ 2) = 2 * Real.log (Real.sqrt (p : ℝ)) := by
        rw [Real.log_pow] <;> norm_num
        <;> positivity
      rw [h₅]
    rw [h₃]
    have h₄ : Real.log (Real.sqrt (p : ℝ)) ≤ Real.sqrt (p : ℝ) - 1 := by
      have h₅ : (0 : ℝ) < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by positivity)
      have h₆ : Real.log (Real.sqrt (p : ℝ)) ≤ Real.sqrt (p : ℝ) - 1 := by
        linarith [Real.log_le_sub_one_of_pos h₅]
      exact h₆
    nlinarith
  exact h₁

/-- Helper: geometric tail bound ∑_{k=2}^K 1/p^k ≤ 2/p² for p ≥ 2. -/
lemma sum_pow_inv_le1122b (p K : ℕ) (hp : 2 ≤ p) :
    ∑ k in Finset.Icc 2 K, (1 : ℝ) / (p : ℝ) ^ k ≤ 2 / (p : ℝ) ^ 2 := by
  have h₁ : ∑ k in Finset.Icc 2 K, (1 : ℝ) / (p : ℝ) ^ k ≤ ∑ k in Finset.Icc 2 K, (1 : ℝ) / (p : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (k - 2) := by
    apply Finset.sum_le_sum
    intro k hk
    have h₂ : k ∈ Finset.Icc 2 K := hk
    have h₃ : 2 ≤ k := Finset.mem_Icc.mp h₂ |>.1
    have h₄ : k ≤ K := Finset.mem_Icc.mp h₂ |>.2
    have h₅ : (p : ℝ) ≥ 2 := by exact_mod_cast hp
    have h₆ : (1 : ℝ) / (p : ℝ) ^ k ≤ (1 : ℝ) / (p : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (k - 2) := by
      have h₇ : (p : ℝ) ^ k = (p : ℝ) ^ 2 * (p : ℝ) ^ (k - 2) := by
        have h₈ : k ≥ 2 := by exact_mod_cast h₃
        have h₉ : (p : ℝ) ^ k = (p : ℝ) ^ 2 * (p : ℝ) ^ (k - 2) := by
          rw [← pow_add, ← Nat.sub_add_cancel h₈]
          <;> ring_nf
          <;> norm_cast
        exact h₉
      rw [h₇]
      have h₈ : (1 : ℝ) / ((p : ℝ) ^ 2 * (p : ℝ) ^ (k - 2)) = (1 : ℝ) / (p : ℝ) ^ 2 * (1 / (p : ℝ) ^ (k - 2)) := by
        field_simp [pow_ne_zero]
        <;> ring_nf
        <;> field_simp [pow_ne_zero]
        <;> ring_nf
      rw [h₈]
      have h₉ : (1 : ℝ) / (p : ℝ) ^ (k - 2) ≤ (1 / 2 : ℝ) ^ (k - 2) := by
        have h₁₀ : (p : ℝ) ≥ 2 := by exact_mod_cast hp
        have h₁₁ : (p : ℝ) ^ (k - 2) ≥ (2 : ℝ) ^ (k - 2) := by
          exact pow_le_pow_of_le_left (by positivity) h₁₀ (k - 2)
        have h₁₂ : (1 : ℝ) / (p : ℝ) ^ (k - 2) ≤ (1 : ℝ) / (2 : ℝ) ^ (k - 2) := by
          apply one_div_le_one_div_of_le
          · positivity
          · exact h₁₁
        have h₁₃ : (1 : ℝ) / (2 : ℝ) ^ (k - 2) = (1 / 2 : ℝ) ^ (k - 2) := by
          field_simp [pow_ne_zero]
          <;> ring_nf
        rw [h₁₃] at h₁₂
        exact h₁₂
      have h₁₀ : 0 ≤ (1 : ℝ) / (p : ℝ) ^ 2 := by positivity
      nlinarith
    exact h₆
  have h₂ : ∑ k in Finset.Icc 2 K, (1 : ℝ) / (p : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (k - 2) = (1 : ℝ) / (p : ℝ) ^ 2 * ∑ k in Finset.Icc 2 K, (1 / 2 : ℝ) ^ (k - 2) := by
    rw [Finset.mul_sum]
    <;> apply Finset.sum_congr rfl
    <;> intro k hk
    <;> ring_nf
  rw [h₂] at h₁
  have h₃ : ∑ k in Finset.Icc 2 K, (1 / 2 : ℝ) ^ (k - 2) ≤ 2 := by
    have h₄ : ∑ k in Finset.Icc 2 K, (1 / 2 : ℝ) ^ (k - 2) ≤ ∑ k in Finset.range K, (1 / 2 : ℝ) ^ k := by
      have h₅ : ∑ k in Finset.Icc 2 K, (1 / 2 : ℝ) ^ (k - 2) ≤ ∑ k in Finset.Icc 2 K, (1 / 2 : ℝ) ^ (k - 2) := le_refl _
      have h₆ : ∑ k in Finset.Icc 2 K, (1 / 2 : ℝ) ^ (k - 2) ≤ ∑ k in Finset.range K, (1 / 2 : ℝ) ^ k := by
        have h₇ : ∑ k in Finset.Icc 2 K, (1 / 2 : ℝ) ^ (k - 2) = ∑ k in Finset.Icc 2 K, (1 / 2 : ℝ) ^ (k - 2) := rfl
        rw [h₇]
        have h₈ : ∑ k in Finset.Icc 2 K, (1 / 2 : ℝ) ^ (k - 2) ≤ ∑ k in Finset.range K, (1 / 2 : ℝ) ^ k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp only [Finset.mem_Icc, Finset.mem_range] at hx ⊢
            omega
          · intro x _ _
            positivity
        exact h₈
      exact h₆
    have h₅ : ∑ k in Finset.range K, (1 / 2 : ℝ) ^ k ≤ 2 := by
      have h₆ : ∑ k in Finset.range K, (1 / 2 : ℝ) ^ k ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ k := by
        apply Finset.sum_le_tsum
        · intro i _
          positivity
        · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
      have h₇ : ∑' k : ℕ, (1 / 2 : ℝ) ^ k = 2 := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        <;> norm_num
      linarith
    linarith
  have h₄ : (1 : ℝ) / (p : ℝ) ^ 2 * ∑ k in Finset.Icc 2 K, (1 / 2 : ℝ) ^ (k - 2) ≤ (1 : ℝ) / (p : ℝ) ^ 2 * 2 := by
    have h₅ : 0 ≤ (1 : ℝ) / (p : ℝ) ^ 2 := by positivity
    nlinarith
  have h₅ : (1 : ℝ) / (p : ℝ) ^ 2 * 2 = 2 / (p : ℝ) ^ 2 := by ring
  linarith

/-- Helper: ∑_{m=2}^N 1/(m√m) ≤ 2. -/
lemma sum_inv_sqrt_le_two1122b (N : ℕ) :
    ∑ m in Finset.Icc 2 N, (1 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤ 2 := by
  have h₁ : ∀ m : ℕ, 2 ≤ m → (1 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤ 2 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := by
    intro m hm
    have h₂ : (m : ℝ) ≥ 2 := by exact_mod_cast hm
    have h₃ : (m - 1 : ℕ) ≥ 1 := by
      have h₄ : m ≥ 2 := hm
      omega
    have h₄ : 0 < Real.sqrt ((m - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have h₅ : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have h₆ : 0 < Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ) := by positivity
    have h₇ : (1 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤ 2 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := by
      have h₈ : Real.sqrt ((m - 1 : ℕ) : ℝ) ≥ 0 := Real.sqrt_nonneg _
      have h₉ : Real.sqrt (m : ℝ) ≥ 0 := Real.sqrt_nonneg _
      have h₁₀ : Real.sqrt ((m - 1 : ℕ) : ℝ) < Real.sqrt (m : ℝ) := by
        apply Real.sqrt_lt_sqrt
        · positivity
        · have h₁₁ : ((m - 1 : ℕ) : ℝ) < (m : ℝ) := by
            have h₁₂ : (m : ℝ) ≥ 2 := by exact_mod_cast hm
            have h₁₃ : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
              have h₁₄ : m ≥ 1 := by linarith
              norm_num [Nat.cast_sub, h₁₄]
              <;> ring_nf
              <;> field_simp
              <;> ring_nf
            rw [h₁₃]
            linarith
          positivity
      have h₁₁ : 0 < Real.sqrt ((m - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
      have h₁₂ : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by positivity)
      have h₁₃ : 0 < Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ) := by positivity
      have h₁₄ : 0 < (m : ℝ) := by positivity
      have h₁₅ : 0 < (m : ℝ) * Real.sqrt (m : ℝ) := by positivity
      -- Use the inequality 1/(m√m) ≤ 2(1/√(m-1) - 1/√m)
      have h₁₆ : 2 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) = 2 * (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) / (Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ)) := by
        field_simp [h₄.ne', h₅.ne']
        <;> ring_nf
        <;> field_simp [h₄.ne', h₅.ne']
        <;> ring_nf
      rw [h₁₆]
      have h₁₇ : (1 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤ 2 * (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) / (Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ)) := by
        -- Prove that 1/(m√m) ≤ 2(√m - √(m-1))/(√(m-1)√m)
        -- This is equivalent to √(m-1)√m ≤ 2m(√m - √(m-1))
        -- Which is equivalent to √(m-1)√m ≤ 2m√m - 2m√(m-1)
        -- Or 2m√(m-1) + √(m-1)√m ≤ 2m√m
        -- Or √(m-1)(2m + √m) ≤ 2m√m
        -- Squaring: (m-1)(4m² + 4m√m + m) ≤ 4m³
        -- This is true for m ≥ 2
        have h₁₈ : 0 ≤ Real.sqrt ((m - 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
        have h₁₉ : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
        have h₂₀ : 0 ≤ Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ) := by positivity
        have h₂₁ : 0 ≤ (m : ℝ) := by positivity
        have h₂₂ : 0 ≤ (m : ℝ) * Real.sqrt (m : ℝ) := by positivity
        have h₂₃ : 0 ≤ (m : ℝ) * Real.sqrt ((m - 1 : ℕ) : ℝ) := by positivity
        have h₂₄ : (Real.sqrt ((m - 1 : ℕ) : ℝ)) ^ 2 = ((m - 1 : ℕ) : ℝ) := by
          rw [Real.sq_sqrt] <;> positivity
        have h₂₅ : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := by
          rw [Real.sq_sqrt] <;> positivity
        have h₂₆ : 2 * (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) / (Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ)) ≥ 0 := by positivity
        -- Use nlinarith with the squared inequality
        have h₂₇ : Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ) ≤ 2 * (m : ℝ) * (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) := by
          nlinarith [Real.sq_sqrt (by positivity : 0 ≤ ((m - 1 : ℕ) : ℝ)),
            Real.sq_sqrt (by positivity : 0 ≤ (m : ℝ)),
            sq_nonneg (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)),
            sq_nonneg (Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ)),
            mul_nonneg h₁₈ h₁₉,
            mul_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)) h₁₈,
            mul_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)) h₁₉]
        have h₂₈ : 0 < Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ) := by positivity
        have h₂₉ : 0 < (m : ℝ) * Real.sqrt (m : ℝ) := by positivity
        calc
          (1 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤ (Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ)) / ((m : ℝ) * Real.sqrt (m : ℝ) * (Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ))) := by
            apply div_le_div_of_le_left (by positivity) (by positivity)
            nlinarith [Real.sqrt_nonneg ((m - 1 : ℕ) : ℝ), Real.sqrt_nonneg (m : ℝ),
              Real.sq_sqrt (by positivity : 0 ≤ ((m - 1 : ℕ) : ℝ)),
              Real.sq_sqrt (by positivity : 0 ≤ (m : ℝ))]
          _ = 1 / (m : ℝ) := by
            field_simp [h₄.ne', h₅.ne', h₁₄.ne', h₁₅.ne']
            <;> ring_nf
            <;> field_simp [h₄.ne', h₅.ne', h₁₄.ne', h₁₅.ne']
            <;> nlinarith [Real.sq_sqrt (by positivity : 0 ≤ ((m - 1 : ℕ) : ℝ)),
              Real.sq_sqrt (by positivity : 0 ≤ (m : ℝ))]
          _ ≤ 2 * (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) / (Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ)) := by
            have h₃₀ : (1 : ℝ) / (m : ℝ) ≤ 2 * (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) / (Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ)) := by
              have h₃₁ : 0 < (m : ℝ) := by positivity
              have h₃₂ : 0 < Real.sqrt ((m - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
              have h₃₃ : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by positivity)
              have h₃₄ : 0 < Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ) := by positivity
              rw [div_le_div_iff (by positivity) (by positivity)]
              nlinarith [Real.sq_sqrt (by positivity : 0 ≤ ((m - 1 : ℕ) : ℝ)),
                Real.sq_sqrt (by positivity : 0 ≤ (m : ℝ)),
                sq_nonneg (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)),
                mul_nonneg h₃₂ h₃₃,
                mul_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ)) h₃₂,
                mul_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ)) h₃₃]
            linarith
      linarith
    exact h₇
  -- Use the telescoping sum
  have h₂ : ∑ m in Finset.Icc 2 N, (1 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤ ∑ m in Finset.Icc 2 N, 2 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := by
    apply Finset.sum_le_sum
    intro m hm
    have h₃ : m ∈ Finset.Icc 2 N := hm
    have h₄ : 2 ≤ m := Finset.mem_Icc.mp h₃ |>.1
    have h₅ : (1 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤ 2 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := h₁ m h₄
    exact h₅
  have h₃ : ∑ m in Finset.Icc 2 N, 2 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) ≤ 2 := by
    have h₄ : ∑ m in Finset.Icc 2 N, 2 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) = 2 * ∑ m in Finset.Icc 2 N, (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := by
      rw [Finset.mul_sum]
    rw [h₄]
    have h₅ : ∑ m in Finset.Icc 2 N, (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) ≤ 1 := by
      -- Telescoping sum
      have h₆ : ∑ m in Finset.Icc 2 N, (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) = ∑ m in Finset.Icc 2 N, (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := rfl
      rw [h₆]
      have h₇ : ∑ m in Finset.Icc 2 N, (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) ≤ 1 := by
        -- The sum telescopes to 1/√1 - 1/√N ≤ 1
        have h₈ : ∀ N : ℕ, ∑ m in Finset.Icc 2 N, (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) ≤ 1 := by
          intro N
          induction' N with N ih
          · norm_num [Finset.sum_range_zero, Finset.Ioc_self]
          · cases N with
            | zero => norm_num [Finset.sum_Icc_succ_top]
            | succ N =>
              simp_all [Finset.sum_Icc_succ_top, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
              <;>
              (try norm_num) <;>
              (try linarith [Real.sqrt_nonneg (N + 2 + 1 : ℝ), Real.sqrt_nonneg (N + 2 : ℝ)]) <;>
              (try
                {
                  have h₉ : 0 < Real.sqrt (N + 2 + 1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
                  have h₁₀ : 0 < Real.sqrt (N + 2 : ℝ) := Real.sqrt_pos.mpr (by positivity)
                  field_simp [h₉.ne', h₁₀.ne'] at *
                  <;> ring_nf at * <;>
                  nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (N + 2 + 1 : ℝ)),
                    Real.sq_sqrt (by positivity : 0 ≤ (N + 2 : ℝ)),
                    Real.sqrt_nonneg (N + 2 + 1 : ℝ), Real.sqrt_nonneg (N + 2 : ℝ)]
                })
        exact h₈ N
      exact h₇
    have h₆ : 2 * ∑ m in Finset.Icc 2 N, (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) ≤ 2 * (1 : ℝ) := by
      gcongr
    linarith
  linarith

/-- Main estimate: the sum over nonprime d of Λ d / d is bounded by 4. -/
lemma nonprime_vonMangoldt_sum_le1122b (N : ℕ) :
    ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime), (Λ d : ℝ) / d ≤ 4 := by
  have h₁ : ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime), (Λ d : ℝ) / d = ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (Λ d : ℝ) / d := by
    apply Eq.symm
    apply Finset.sum_subset
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hd ⊢
      by_cases h : Λ d = 0
      · simp_all
      · aesop
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hd ⊢
      aesop
  rw [h₁]
  have h₂ : ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (Λ d : ℝ) / d ≤ 4 := by
    -- For each d with Λ d ≠ 0 and ¬ d.Prime, d = p^k with p prime, k ≥ 2
    have h₃ : ∀ d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ p ^ k = d ∧ Λ d = Real.log p := by
      intro d hd
      have h₄ : d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0) := hd
      have h₅ : ¬ d.Prime ∧ Λ d ≠ 0 := (Finset.mem_filter.mp h₄).2
      have h₆ : ¬ d.Prime := h₅.1
      have h₇ : Λ d ≠ 0 := h₅.2
      obtain ⟨p, k, hp, hk₁, hk₂, hΛ⟩ := vonMangoldt_char1122b h₇
      have h₈ : 1 ≤ k := hk₁
      have h₉ : p ^ k = d := hk₂
      have h₁₀ : Λ d = Real.log p := hΛ
      have h₁₁ : 2 ≤ k := by
        by_contra h
        have h₁₂ : k ≤ 1 := by linarith
        have h₁₃ : k = 1 := by
          omega
        rw [h₁₃] at hk₂
        have h₁₄ : p ^ 1 = d := by simpa using hk₂
        have h₁₅ : p = d := by simpa using h₁₄
        have h₁₆ : d.Prime := by rw [h₁₅]; exact hp
        contradiction
      exact ⟨p, k, hp, h₁₁, hk₂, hΛ⟩
    -- Group by prime base
    have h₄ : ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (Λ d : ℝ) / d ≤ ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, ∑ k in Finset.Icc 2 N, (Real.log p : ℝ) / (p : ℝ) ^ k := by
      -- Use the fact that each d corresponds to a unique (p, k) pair
      have h₅ : ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (Λ d : ℝ) / d ≤ ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, ∑ k in Finset.Icc 2 N, if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 := by
        apply Finset.sum_le_sum
        intro d hd
        have h₆ : ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ p ^ k = d ∧ Λ d = Real.log p := h₃ d hd
        obtain ⟨p, k, hp, hk₁, hk₂, hΛ⟩ := h₆
        have h₇ : (Λ d : ℝ) / d = (Real.log p : ℝ) / (p : ℝ) ^ k := by
          have h₈ : (Λ d : ℝ) = Real.log p := by exact_mod_cast hΛ
          have h₉ : (d : ℝ) = (p : ℝ) ^ k := by
            norm_cast
            <;> simp [hk₂]
            <;> norm_cast
          rw [h₈, h₉]
          <;> field_simp
          <;> ring_nf
          <;> norm_cast
        have h₈ : ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, ∑ k in Finset.Icc 2 N, (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) ≥ (Real.log p : ℝ) / (p : ℝ) ^ k := by
          have h₉ : p ∈ (Finset.Ioc 0 N).filter Nat.Prime := by
            have h₁₀ : d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0) := hd
            have h₁₁ : d ∈ Finset.Ioc 0 N := (Finset.mem_filter.mp h₁₀).1
            have h₁₂ : 0 < d := (Finset.mem_Ioc.mp h₁₁).1
            have h₁₃ : d ≤ N := (Finset.mem_Ioc.mp h₁₁).2
            have h₁₄ : p ^ k = d := hk₂
            have h₁₅ : p ≤ d := by
              have h₁₆ : p ^ k = d := hk₂
              have h₁₇ : p ≤ p ^ k := by
                exact Nat.le_self_pow (by linarith [hp.two_le]) k
              linarith
            have h₁₆ : p ≤ N := by linarith
            have h₁₇ : 0 < p := hp.pos
            simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE] at *
            exact ⟨⟨by linarith, by linarith⟩, hp⟩
          have h₁₀ : k ∈ Finset.Icc 2 N := by
            have h₁₁ : 2 ≤ k := hk₁
            have h₁₂ : k ≤ N := by
              have h₁₃ : p ^ k = d := hk₂
              have h₁₄ : d ≤ N := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).2
              have h₁₅ : p ^ k ≤ N := by linarith
              have h₁₆ : k ≤ N := by
                by_contra h
                have h₁₇ : k ≥ N + 1 := by omega
                have h₁₈ : p ^ k ≥ p ^ (N + 1) := pow_le_pow_right (by linarith [hp.two_le]) h₁₇
                have h₁₉ : p ^ (N + 1) > N := by
                  have h₂₀ : p ≥ 2 := hp.two_le
                  have h₂₁ : p ^ (N + 1) ≥ 2 ^ (N + 1) := pow_le_pow_of_le_left (by positivity) (by linarith) (N + 1)
                  have h₂₂ : 2 ^ (N + 1) > N := by
                    have h₂₃ : 2 ^ (N + 1) > N := by
                      calc
                        2 ^ (N + 1) ≥ 2 ^ (N + 1) := le_refl _
                        _ > N := by
                          have h₂₄ : N < 2 ^ (N + 1) := by
                            calc
                              N < 2 ^ N := by
                                exact Nat.lt_pow_self (by norm_num) N
                              _ ≤ 2 ^ (N + 1) := by
                                exact pow_le_pow_right (by norm_num) (by omega)
                          linarith
                    linarith
                  linarith
                linarith
              linarith
            simp only [Finset.mem_Icc]
            exact ⟨by omega, by omega⟩
          calc
            ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, ∑ k in Finset.Icc 2 N, (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) ≥ ∑ k in Finset.Icc 2 N, (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) := by
              apply Finset.single_le_sum (fun x _ => by
                apply Finset.sum_nonneg
                intro y _
                split_ifs <;> positivity) h₉
            _ ≥ (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) := by
              apply Finset.single_le_sum (fun x _ => by
                split_ifs <;> positivity) h₁₀
            _ = (Real.log p : ℝ) / (p : ℝ) ^ k := by
              simp [hk₂]
        linarith
      have h₆ : ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, ∑ k in Finset.Icc 2 N, (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) = ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, ∑ k in Finset.Icc 2 N, ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) := by
        rw [Finset.sum_comm]
        <;> rw [Finset.sum_comm]
      have h₇ : ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, ∑ k in Finset.Icc 2 N, ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) ≤ ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, ∑ k in Finset.Icc 2 N, (Real.log p : ℝ) / (p : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro k hk
        have h₈ : ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) ≤ (Real.log p : ℝ) / (p : ℝ) ^ k := by
          have h₉ : ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) ≤ ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) := le_refl _
          have h₁₀ : ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) ≤ (Real.log p : ℝ) / (p : ℝ) ^ k := by
            -- At most one d satisfies p^k = d
            have h₁₁ : ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) ≤ (Real.log p : ℝ) / (p : ℝ) ^ k := by
              calc
                _ = ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) := rfl
                _ ≤ ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) := le_refl _
                _ ≤ (Real.log p : ℝ) / (p : ℝ) ^ k := by
                  -- The sum is either 0 or the term itself
                  have h₁₂ : ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) ≤ (Real.log p : ℝ) / (p : ℝ) ^ k := by
                    classical
                    by_cases h₁₃ : p ^ k ∈ (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0)
                    · -- Case: p^k is in the set
                      have h₁₄ : ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) = (Real.log p : ℝ) / (p : ℝ) ^ k := by
                        calc
                          _ = ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) := rfl
                          _ = (if p ^ k = p ^ k then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) := by
                            rw [Finset.sum_ite_eq' (Finset.mem_filter.mp h₁₃ |>.1)]
                            <;> simp_all
                          _ = (Real.log p : ℝ) / (p : ℝ) ^ k := by simp
                      rw [h₁₄]
                    · -- Case: p^k is not in the set
                      have h₁₄ : ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) = 0 := by
                        apply Finset.sum_eq_zero
                        intro d hd
                        have h₁₅ : d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0) := hd
                        have h₁₆ : ¬(p ^ k = d) := by
                          intro h
                          apply h₁₃
                          simp_all [Finset.mem_filter]
                          <;> aesop
                        simp [h₁₆]
                      rw [h₁₄]
                      have h₁₅ : (0 : ℝ) ≤ (Real.log p : ℝ) / (p : ℝ) ^ k := by positivity
                      linarith
                  exact h₁₂
            exact h₁₁
          exact h₁₀
        linarith
      calc
        ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (Λ d : ℝ) / d ≤ ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, ∑ k in Finset.Icc 2 N, (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) := h₅
        _ = ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, ∑ k in Finset.Icc 2 N, ∑ d in (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), (if p ^ k = d then (Real.log p : ℝ) / (p : ℝ) ^ k else 0 : ℝ) := by rw [h₆]
        _ ≤ ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, ∑ k in Finset.Icc 2 N, (Real.log p : ℝ) / (p : ℝ) ^ k := h₇
    have h₅ : ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, ∑ k in Finset.Icc 2 N, (Real.log p : ℝ) / (p : ℝ) ^ k ≤ 4 := by
      have h₆ : ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, ∑ k in Finset.Icc 2 N, (Real.log p : ℝ) / (p : ℝ) ^ k = ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, (Real.log p : ℝ) * ∑ k in Finset.Icc 2 N, (1 : ℝ) / (p : ℝ) ^ k := by
        apply Finset.sum_congr rfl
        intro p hp
        have h₇ : ∑ k in Finset.Icc 2 N, (Real.log p : ℝ) / (p : ℝ) ^ k = (Real.log p : ℝ) * ∑ k in Finset.Icc 2 N, (1 : ℝ) / (p : ℝ) ^ k := by
          have h₈ : ∑ k in Finset.Icc 2 N, (Real.log p : ℝ) / (p : ℝ) ^ k = ∑ k in Finset.Icc 2 N, (Real.log p : ℝ) * ((1 : ℝ) / (p : ℝ) ^ k) := by
            apply Finset.sum_congr rfl
            intro k hk
            field_simp [pow_ne_zero]
            <;> ring_nf
            <;> field_simp [pow_ne_zero]
            <;> ring_nf
          rw [h₈]
          rw [Finset.mul_sum]
          <;> apply Finset.sum_congr rfl
          <;> intro k hk
          <;> ring_nf
        rw [h₇]
        <;> ring_nf
      rw [h₆]
      have h₇ : ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, (Real.log p : ℝ) * ∑ k in Finset.Icc 2 N, (1 : ℝ) / (p : ℝ) ^ k ≤ ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, (Real.log p : ℝ) * (2 / (p : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro p hp
        have h₈ : p ∈ (Finset.Ioc 0 N).filter Nat.Prime := hp
        have h₉ : p.Prime := (Finset.mem_filter.mp h₈).2
        have h₁₀ : 2 ≤ p := h₉.two_le
        have h₁₁ : ∑ k in Finset.Icc 2 N, (1 : ℝ) / (p : ℝ) ^ k ≤ 2 / (p : ℝ) ^ 2 := sum_pow_inv_le1122b p N h₁₀
        have h₁₂ : 0 ≤ (Real.log p : ℝ) := by exact Real.log_nonneg (by exact_mod_cast h₁₀)
        nlinarith
      have h₈ : ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, (Real.log p : ℝ) * (2 / (p : ℝ) ^ 2) = ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, 2 * (Real.log p : ℝ) / (p : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        ring_nf
      rw [h₈] at h₇
      have h₉ : ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, 2 * (Real.log p : ℝ) / (p : ℝ) ^ 2 ≤ 4 := by
        have h₁₀ : ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, 2 * (Real.log p : ℝ) / (p : ℝ) ^ 2 ≤ ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, 2 * (2 / ((p : ℝ) * Real.sqrt (p : ℝ))) := by
          apply Finset.sum_le_sum
          intro p hp
          have h₁₁ : p ∈ (Finset.Ioc 0 N).filter Nat.Prime := hp
          have h₁₂ : p.Prime := (Finset.mem_filter.mp h₁₁).2
          have h₁₃ : 2 ≤ p := h₁₂.two_le
          have h₁₄ : Real.log (p : ℝ) ≤ 2 * Real.sqrt (p : ℝ) := log_le_two_sqrt1122b p (by exact_mod_cast h₁₃)
          have h₁₅ : 0 < (p : ℝ) := by positivity
          have h₁₆ : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by positivity)
          have h₁₇ : 0 < (p : ℝ) * Real.sqrt (p : ℝ) := by positivity
          have h₁₈ : (Real.log p : ℝ) / (p : ℝ) ^ 2 ≤ 2 / ((p : ℝ) * Real.sqrt (p : ℝ)) := by
            have h₁₉ : Real.log (p : ℝ) ≤ 2 * Real.sqrt (p : ℝ) := log_le_two_sqrt1122b p (by exact_mod_cast h₁₃)
            have h₂₀ : 0 < (p : ℝ) := by positivity
            have h₂₁ : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by positivity)
            have h₂₂ : 0 < (p : ℝ) ^ 2 := by positivity
            have h₂₃ : 0 < (p : ℝ) * Real.sqrt (p : ℝ) := by positivity
            -- Use the fact that log p / p² ≤ 2 / (p√p) for p ≥ 2
            have h₂₄ : Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ (2 * Real.sqrt (p : ℝ)) / (p : ℝ) ^ 2 := by
              gcongr
            have h₂₅ : (2 * Real.sqrt (p : ℝ)) / (p : ℝ) ^ 2 ≤ 2 / ((p : ℝ) * Real.sqrt (p : ℝ)) := by
              rw [div_le_div_iff (by positivity) (by positivity)]
              have h₂₆ : (2 * Real.sqrt (p : ℝ)) * ((p : ℝ) * Real.sqrt (p : ℝ)) = 2 * (p : ℝ) * (Real.sqrt (p : ℝ)) ^ 2 := by ring
              have h₂₇ : (Real.sqrt (p : ℝ)) ^ 2 = (p : ℝ) := by
                rw [Real.sq_sqrt] <;> positivity
              nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (p : ℝ)), Real.sqrt_nonneg (p : ℝ)]
            linarith
          have h₂₆ : 0 ≤ (2 : ℝ) := by norm_num
          nlinarith
        have h₁₁ : ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, 2 * (2 / ((p : ℝ) * Real.sqrt (p : ℝ))) = ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, 4 / ((p : ℝ) * Real.sqrt (p : ℝ)) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring_nf
        rw [h₁₁] at h₁₀
        have h₁₂ : ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, 4 / ((p : ℝ) * Real.sqrt (p : ℝ)) ≤ 4 := by
          have h₁₃ : ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, 4 / ((p : ℝ) * Real.sqrt (p : ℝ)) ≤ ∑ m in Finset.Icc 2 N, 4 / ((m : ℝ) * Real.sqrt (m : ℝ)) := by
            have h₁₄ : ∑ p in (Finset.Ioc 0 N).filter Nat.Prime, 4 / ((p : ℝ) * Real.sqrt (p : ℝ)) ≤ ∑ m in (Finset.Ioc 0 N).filter Nat.Prime, 4 / ((m : ℝ) * Real.sqrt (m : ℝ)) := by
              simp [Finset.sum_filter]
            have h₁₅ : ∑ m in (Finset.Ioc 0 N).filter Nat.Prime, 4 / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤ ∑ m in Finset.Icc 2 N, 4 / ((m : ℝ) * Real.sqrt (m : ℝ)) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro m hm
                simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE] at hm ⊢
                aesop
              · intro m _ _
                positivity
            linarith
          have h₁₄ : ∑ m in Finset.Icc 2 N, 4 / ((m : ℝ) * Real.sqrt (m : ℝ)) = 4 * ∑ m in Finset.Icc 2 N, (1 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ)) := by
            rw [Finset.mul_sum]
            <;> apply Finset.sum_congr rfl
            <;> intro m hm
            <;> ring_nf
          rw [h₁₄] at h₁₃
          have h₁₅ : 4 * ∑ m in Finset.Icc 2 N, (1 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤ 4 * 2 := by
            have h₁₆ : ∑ m in Finset.Icc 2 N, (1 : ℝ) / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤ 2 := sum_inv_sqrt_le_two1122b N
            nlinarith
          linarith
        linarith
      linarith
    linarith
  linarith

/-- LEAF: Davenport Chapter 4, the passage from Lambda to primes, the character free part: the
prime powers p ^ k with k at least 2 contribute a bounded amount to the sums of Lambda d / d,
since Lambda p ^ k = log p and the sum over p and k at least 2 of log p / p ^ k is at most the
sum of log p / p p - 1, which converges. The d with Lambda d = 0 contribute nothing.
Class MEDIUM. -/
theorem leaf_vonMangoldt_nonprime_bounded1122b :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∑ d ∈ (Ioc 0 N).filter (fun d => ¬ d.Prime), Λ d / d ≤ B := by
  refine' ⟨4, by norm_num, _⟩
  intro N
  have h₁ : ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime), (Λ d : ℝ) / d ≤ 4 := nonprime_vonMangoldt_sum_le1122b N
  simpa using h₁

/-- Proved from leaf_vonMangoldt_nonprime_bounded1122b, formerly a LEAF: Davenport Chapter 4, the
passage from Lambda to primes: the primes d give exactly the prime sum since Lambda p = log p,
and the rest is bounded in absolute value by the sum of Lambda d / d over nonprime d. -/
theorem leaf_chi4_prime_powers1122b (χ : ℕ → ℝ)
    (hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      |∑ d ∈ Ioc 0 N, χ d * Λ d / d - ∑ p ∈ Nat.primesLE N, χ p * log p / p| ≤ B := by
  obtain ⟨B, hB, HB⟩ := leaf_vonMangoldt_nonprime_bounded1122b
  refine ⟨B, hB, fun N => ?_⟩
  have hset : (Ioc 0 N).filter Nat.Prime = Nat.primesLE N := by
    ext p
    simp only [mem_filter, mem_Ioc, Nat.primesLE, Nat.primesBelow, mem_range]
    constructor
    · rintro ⟨⟨_, h2⟩, hp⟩; exact ⟨by omega, hp⟩
    · rintro ⟨h1, hp⟩; exact ⟨⟨hp.pos, by omega⟩, hp⟩
  have hsplit := (sum_filter_add_sum_filter_not (Ioc 0 N) Nat.Prime (fun d => χ d * Λ d / d)).symm
  have hprime : ∑ d ∈ (Ioc 0 N).filter Nat.Prime, χ d * Λ d / d =
      ∑ p ∈ Nat.primesLE N, χ p * log p / p := by
    rw [hset]; apply sum_congr rfl; intro p hp
    have hp' : p.Prime := (Nat.mem_primesLE.1 hp).2
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp']
  rw [hsplit, hprime, add_sub_cancel_left]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun d _ => ?_).trans (HB N))
  have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
  rw [abs_div, abs_mul, abs_of_nonneg hΛ, Nat.abs_cast]
  have hχ1 : |χ d| ≤ 1 := by rw [hχ]; split_ifs <;> simp
  gcongr
  calc |χ d| * Λ d ≤ 1 * Λ d := by gcongr
    _ = Λ d := one_mul _

lemma chi4_abs_le1122b (χ : ℕ → ℝ)
    (hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0) (n : ℕ) :
    |χ n| ≤ 1 := by
  rw [hχ]; split_ifs <;> simp

/-- floor bound: for 1 ≤ d ≤ N, the reciprocal of N / d is at most 2 d / N. -/
lemma inv_div_le1122b {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    (1 : ℝ) / ((N / d : ℕ) : ℝ) ≤ 2 * d / N := by
  have hq : 1 ≤ N / d := (Nat.one_le_div_iff hd).2 hdN
  have hN : N < 2 * (N / d) * d := by
    have h1 := Nat.div_add_mod N d
    have h2 := Nat.mod_lt N hd
    have h3 : d ≤ d * (N / d) := Nat.le_mul_of_pos_right d hq
    nlinarith
  have hNr : (N : ℝ) ≤ 2 * ((N / d : ℕ) : ℝ) * d := by exact_mod_cast hN.le
  have hqpos : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by exact_mod_cast hq
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hd hdN)
  rw [div_le_div_iff₀ hqpos hNpos]
  linarith

/-- The Chebyshev step: Davenport Chapter 4 with Mathlib's Chebyshev.psi_le_const_mul_self.
Pi / 4 times the sum of chi_4 d Lambda d / d over d at most N is bounded. -/
theorem chi4_vonMangoldt_bounded1122b (χ : ℕ → ℝ)
    (hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, |∑ d ∈ Ioc 0 N, χ d * Λ d / d| ≤ B := by
  obtain ⟨BU, hBU, HU⟩ := leaf_chi4_log_sum_bounded1122b χ hχ
  set C : ℝ := Real.log 4 + 4
  have hC : 0 ≤ C := by positivity
  refine ⟨2 * (BU + 2 * C), by positivity, ?_⟩
  intro N
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; simp; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  set T := ∑ d ∈ Ioc 0 N, χ d * Λ d / d
  set E := ∑ d ∈ Ioc 0 N, χ d * Λ d / d * (∑ m ∈ Ioc 0 (N / d), χ m / m - π / 4)
  have hid : π / 4 * T = ∑ n ∈ Ioc 0 N, χ n * log n / n - E := by
    rw [leaf_chi4_log_convolution1122b χ hχ N]
    simp only [E, T]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply sum_congr rfl; intro d _; ring
  have hE : |E| ≤ 2 * C := by
    calc |E| ≤ ∑ d ∈ Ioc 0 N, |χ d * Λ d / d * (∑ m ∈ Ioc 0 (N / d), χ m / m - π / 4)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Ioc 0 N, 2 / (N : ℝ) * Λ d := by
          apply sum_le_sum; intro d hd
          rw [mem_Ioc] at hd
          have hdpos : (0 : ℝ) < d := by exact_mod_cast hd.1
          have hq : 1 ≤ N / d := (Nat.one_le_div_iff hd.1).2 hd.2
          have hL := leaf_chi4_leibniz_tail1122b χ hχ (N / d) hq
          have hI := inv_div_le1122b hd.1 hd.2
          have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
          rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hΛ, abs_of_pos hdpos]
          have hχ1 := chi4_abs_le1122b χ hχ d
          calc |χ d| * Λ d / d * |∑ m ∈ Ioc 0 (N / d), χ m / m - π / 4|
              ≤ 1 * Λ d / d * (2 * d / N) := by
                gcongr
                exact hL.trans hI
            _ = 2 / (N : ℝ) * Λ d := by field_simp
      _ = 2 / (N : ℝ) * Chebyshev.psi N := by
          rw [← mul_sum, Chebyshev.psi, Nat.floor_natCast]
      _ ≤ 2 / (N : ℝ) * (C * N) := by
          gcongr; exact Chebyshev.psi_le_const_mul_self hNr.le
      _ = 2 * C := by field_simp
  have hT : π / 4 * |T| ≤ BU + 2 * C := by
    have h1 : |π / 4 * T| ≤ BU + 2 * C := by
      rw [hid]
      calc _ ≤ |∑ n ∈ Ioc 0 N, χ n * log n / n| + |E| := abs_sub _ _
        _ ≤ _ := add_le_add (HU N) hE
    rwa [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < π / 4)] at h1
  have hpi : (1 : ℝ) / 2 ≤ π / 4 := by linarith [Real.pi_gt_three]
  nlinarith [abs_nonneg T]

/-- leaf_mertens_chi4 from the four LEAFs above, Davenport Chapter 4. -/
theorem leaf_mertens_chi4_of_leaves :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊,
        (if p % 4 = 1 then (1 : ℝ) else if p % 4 = 3 then -1 else 0) * log p / p| ≤ B₀ := by
  set χ : ℕ → ℝ := fun n => if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0 with hχd
  have hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0 :=
    fun n => rfl
  obtain ⟨B1, hB1, H1⟩ := chi4_vonMangoldt_bounded1122b χ hχ
  obtain ⟨B2, hB2, H2⟩ := leaf_chi4_prime_powers1122b χ hχ
  refine ⟨B1 + B2, by positivity, fun x _ => ?_⟩
  set N := ⌊x⌋₊
  have h := H2 N
  have h1 := H1 N
  change |∑ p ∈ Nat.primesLE N, χ p * log p / p| ≤ B1 + B2
  have := abs_sub_abs_le_abs_sub (∑ p ∈ Nat.primesLE N, χ p * log p / p)
    (∑ d ∈ Ioc 0 N, χ d * Λ d / d)
  rw [abs_sub_comm] at this
  linarith

end LeanLab.Teravainen2016
