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

/-- LEAF: Davenport Chapter 4, the passage from Lambda to primes, the character free part: the
prime powers p ^ k with k at least 2 contribute a bounded amount to the sums of Lambda d / d,
since Lambda p ^ k = log p and the sum over p and k at least 2 of log p / p ^ k is at most the
sum of log p / p p - 1, which converges. The d with Lambda d = 0 contribute nothing.
Class MEDIUM. -/
theorem leaf_vonMangoldt_nonprime_bounded1122b :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∑ d ∈ (Ioc 0 N).filter (fun d => ¬ d.Prime), Λ d / d ≤ B := by
  have hsum : Summable (fun n : ℕ => 16 * (n : ℝ) ^ (-(3 : ℝ) / 2)) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left 16
  refine ⟨∑' n : ℕ, 16 * (n : ℝ) ^ (-(3 : ℝ) / 2),
    tsum_nonneg (fun n => by positivity), fun N => ?_⟩
  set P := (Ioc 0 N).filter Nat.Prime with hP
  set T := P ×ˢ Icc 2 N with hT
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 ^ x.2) (T : Set (ℕ × ℕ)) := by
    rintro ⟨p, k⟩ hx ⟨q, j⟩ hy hxy
    simp only [hT, hP, coe_product, Set.mem_prod, mem_coe, mem_filter, mem_Icc] at hx hy
    simp only at hxy
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj hx.1.2 hy.1.2 hxy
    rw [h1, h2]
  have step1 : ∑ d ∈ (Ioc 0 N).filter (fun d => ¬ d.Prime), Λ d / d ≤
      ∑ x ∈ T, Real.log x.1 / (x.1 : ℝ) ^ x.2 := by
    have himg : ∑ x ∈ T, Real.log x.1 / (x.1 : ℝ) ^ x.2 =
        ∑ d ∈ T.image (fun x : ℕ × ℕ => x.1 ^ x.2), Λ d / d := by
      rw [sum_image hinj]
      refine sum_congr rfl fun x hx => ?_
      simp only [hT, hP, mem_product, mem_filter, mem_Icc] at hx
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hx.1.2]
      push_cast; rfl
    rw [himg, ← sum_filter_ne_zero]
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      rw [mem_filter, mem_filter, mem_Ioc] at hd
      obtain ⟨hd, hne⟩ := hd
      have hΛ : Λ d ≠ 0 := by
        intro h; apply hne; rw [h, zero_div]
      rw [ArithmeticFunction.vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at hΛ
      obtain ⟨p, k, hp, hk, rfl⟩ := hΛ
      have hk1 : k ≠ 1 := by rintro rfl; exact hd.2 (by simpa using hp)
      rw [mem_image]
      refine ⟨(p, k), ?_, rfl⟩
      have hkp : k < p ^ k := Nat.lt_pow_self hp.one_lt
      have hpp : p ≤ p ^ k := Nat.le_self_pow (by omega) p
      simp only [hT, hP, mem_product, mem_filter, mem_Ioc, mem_Icc]
      exact ⟨⟨⟨hp.pos, by omega⟩, hp⟩, by omega, by omega⟩
    · intro d _ _
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  have step2 : ∀ p ∈ P, ∑ k ∈ Icc 2 N, Real.log p / (p : ℝ) ^ k ≤
      8 * (Real.log p / (p : ℝ) ^ 2) := by
    intro p hp
    simp only [hP, mem_filter] at hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hc : 0 ≤ Real.log p / (p : ℝ) ^ 2 := by positivity
    calc ∑ k ∈ Icc 2 N, Real.log p / (p : ℝ) ^ k
        ≤ ∑ k ∈ Icc 2 N, 4 * (Real.log p / (p : ℝ) ^ 2) * (1 / 2 : ℝ) ^ k := by
          refine sum_le_sum fun k hk => ?_
          rw [mem_Icc] at hk
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
          have hpj : (2 : ℝ) ^ j ≤ (p : ℝ) ^ j := pow_le_pow_left₀ (by norm_num) hp2 j
          rw [div_le_iff₀ (by positivity)]
          have e : 4 * (Real.log p / (p : ℝ) ^ 2) * (1 / 2 : ℝ) ^ (j + 2) * (p : ℝ) ^ (j + 2)
              = Real.log p * ((p : ℝ) ^ j / 2 ^ j) := by
            have h12 : (1 / 2 : ℝ) ^ j * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
            field_simp
            linear_combination (Real.log p * (p : ℝ) ^ 2 * (p : ℝ) ^ j) * h12
          rw [e]
          have : 1 ≤ (p : ℝ) ^ j / 2 ^ j := by
            rw [le_div_iff₀ (by positivity)]; linarith
          nlinarith
      _ = 4 * (Real.log p / (p : ℝ) ^ 2) * ∑ k ∈ Icc 2 N, (1 / 2 : ℝ) ^ k := by
          rw [mul_sum]
      _ ≤ 4 * (Real.log p / (p : ℝ) ^ 2) * 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (summable_geometric_two.sum_le_tsum _ (fun k _ => by positivity)).trans
            (le_of_eq tsum_geometric_two)
      _ = 8 * (Real.log p / (p : ℝ) ^ 2) := by ring
  have step3 : ∀ p ∈ P, 8 * (Real.log p / (p : ℝ) ^ 2) ≤ 16 * (p : ℝ) ^ (-(3 : ℝ) / 2) := by
    intro p hp
    simp only [hP, mem_filter] at hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    have hl := Real.log_le_rpow_div hp0.le (by norm_num : (0 : ℝ) < 1 / 2)
    have e : (p : ℝ) ^ (-(3 : ℝ) / 2) * (p : ℝ) ^ 2 = (p : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hp0]; norm_num
    have hl' : Real.log p ≤ 2 * (p : ℝ) ^ ((1 : ℝ) / 2) := by
      linarith [hl, show (p : ℝ) ^ ((1 : ℝ) / 2) / (1 / 2) = 2 * (p : ℝ) ^ ((1 : ℝ) / 2) by ring]
    calc 8 * (Real.log p / (p : ℝ) ^ 2) ≤ 8 * (2 * (p : ℝ) ^ ((1 : ℝ) / 2) / (p : ℝ) ^ 2) := by
          gcongr
      _ = 16 * (p : ℝ) ^ (-(3 : ℝ) / 2) := by
          rw [← e]; field_simp; norm_num
  calc ∑ d ∈ (Ioc 0 N).filter (fun d => ¬ d.Prime), Λ d / d
      ≤ ∑ x ∈ T, Real.log x.1 / (x.1 : ℝ) ^ x.2 := step1
    _ = ∑ p ∈ P, ∑ k ∈ Icc 2 N, Real.log p / (p : ℝ) ^ k := by rw [hT, sum_product]
    _ ≤ ∑ p ∈ P, 16 * (p : ℝ) ^ (-(3 : ℝ) / 2) :=
        sum_le_sum fun p hp => (step2 p hp).trans (step3 p hp)
    _ ≤ ∑' n : ℕ, 16 * (n : ℝ) ^ (-(3 : ℝ) / 2) :=
        hsum.sum_le_tsum _ (fun n _ => by positivity)

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
