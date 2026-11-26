/-
P0076, Section 4, page 15, the second inequality of the display after display 4.3.
Split of leaf_mertens_mod4_bias in MertensMod4Split.lean by partial summation:
the bias of sums of 1/p between the classes 1 and 3 mod 4 is the block sum of chi_4 p / p,
which Abel summation bounds by the partial sums of chi_4 p log p / p. Those are bounded by
the Mertens theorem for the character chi_4, the one cited LEAF here.
The Abel step follows abel_recip in AlmostPrimes/Decomp1528b with the weight chi_4.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.MertensMod4Split

open Finset Real
open scoped Classical

namespace LeanLab.Teravainen2016

section Chi4MertensAux

open scoped ArithmeticFunction.vonMangoldt
open Filter

/-- chi_4 on odd and even arguments. -/
private lemma chi4_odd_w (χ : ℕ → ℝ)
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
private lemma chi4_sum_alt_w (χ : ℕ → ℝ)
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
        show 2 * j + 1 + 1 = 2 * j + 2 by ring, (chi4_odd_w χ hχ j).2]
      simp
    refine ⟨by rw [h1, ih.2], ?_⟩
    rw [Finset.sum_Ioc_succ_top (by omega), h1, ih.2, sum_range_succ _ (j + 1),
      show 2 * (j + 1) + 1 = 2 * (j + 1) + 1 by rfl, (chi4_odd_w χ hχ (j + 1)).1]
    push_cast; ring

/-- alternating series remainder for the Leibniz series, Real.tendsto_sum_pi_div_four. -/
private lemma leibniz_alt_bound_w (j : ℕ) :
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
private theorem leaf_chi4_leibniz_tail_w (χ : ℕ → ℝ)
    (hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0)
    (k : ℕ) (hk : 1 ≤ k) :
    |∑ m ∈ Ioc 0 k, χ m / m - π / 4| ≤ 1 / k := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [(chi4_sum_alt_w χ hχ j).1]
    refine (leibniz_alt_bound_w j).trans ?_
    have : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    push_cast
    gcongr; linarith
  · rw [(chi4_sum_alt_w χ hχ j).2]
    refine (leibniz_alt_bound_w (j + 1)).trans ?_
    push_cast
    gcongr; linarith

/-- chi_4 weighted partial sums are alternating sums over odd arguments. -/
private lemma chi4_sum_weighted_w (χ : ℕ → ℝ)
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
        show 2 * j + 1 + 1 = 2 * j + 2 by ring, (chi4_odd_w χ hχ j).2]
      simp
    refine ⟨by rw [h1, ih.2], ?_⟩
    rw [Finset.sum_Ioc_succ_top (by omega), h1, ih.2, sum_range_succ _ (j + 1),
      (chi4_odd_w χ hχ (j + 1)).1]

/-- partial sums of an alternating series with antitone nonnegative terms lie in [0, h 0]. -/
private lemma alt_antitone_bound_w : ∀ (n : ℕ) (h : ℕ → ℝ), Antitone h → (∀ i, 0 ≤ h i) →
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
private theorem leaf_chi4_log_sum_bounded_w (χ : ℕ → ℝ)
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
    have := alt_antitone_bound_w j g hga hg0
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
  · rw [(chi4_sum_weighted_w χ hχ w j).1]; exact key j
  · rw [(chi4_sum_weighted_w χ hχ w j).2]; exact key (j + 1)


/-- chi_4 is completely multiplicative. -/
private lemma chi4_mul_w (χ : ℕ → ℝ)
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
private theorem leaf_chi4_log_convolution_w (χ : ℕ → ℝ)
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
  have hchi : χ i * χ (n / i) = χ n := by rw [← chi4_mul_w χ hχ, hmul]
  have hir : (0 : ℝ) < i := by exact_mod_cast hipos
  have hqr : (0 : ℝ) < ((n / i : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_pos (Nat.le_of_dvd hn.1 hdvd) hipos
  rw [← hcast, ← hchi]
  field_simp

/-! ### Private helpers for `leaf_vonMangoldt_nonprime_bounded_w` -/

/-- Partial sums of a geometric series of ratio at most `1 / 2` are at most `2`. -/
private lemma geom_series_le_two_w {r : ℝ} (h0 : 0 ≤ r) (h1 : 2 * r ≤ 1) :
    ∀ K : ℕ, ∑ j ∈ Finset.range K, r ^ j ≤ 2 := by
  have key : ∀ K : ℕ, ∑ j ∈ Finset.range K, r ^ j ≤ 2 - 2 * r ^ K := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hK : (0 : ℝ) ≤ r ^ K := pow_nonneg h0 K
      nlinarith
  intro K
  have h2 := key K
  have h3 : (0 : ℝ) ≤ 2 * r ^ K := by positivity
  linarith

/-- `∑ k ∈ Icc 2 K, f k` as a range sum of `f (j + 2)`. -/
private lemma sum_Icc_two_eq_sum_range_w (K : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 2 K, f k = ∑ j ∈ Finset.range (K - 1), f (j + 2) := by
  rcases lt_or_ge K 2 with hK | hK
  · have h1 : K = 0 ∨ K = 1 := by omega
    rcases h1 with rfl | rfl
    · rw [Finset.Icc_eq_empty (by omega)]
      simp
    · rw [Finset.Icc_eq_empty (by omega)]
      simp
  · have himg : Finset.Icc 2 K =
        (Finset.range (K - 1)).map ⟨fun j => j + 2, fun a b h => Nat.add_right_cancel h⟩ := by
      ext k
      constructor
      · intro hk
        rw [Finset.mem_Icc] at hk
        refine Finset.mem_map.2 ⟨k - 2, Finset.mem_range.2 (by omega), ?_⟩
        show k - 2 + 2 = k
        omega
      · intro hk
        rw [Finset.mem_map] at hk
        obtain ⟨j, hj, rfl⟩ := hk
        rw [Finset.mem_range] at hj
        rw [Finset.mem_Icc]
        show 2 ≤ j + 2 ∧ j + 2 ≤ K
        omega
    rw [himg, Finset.sum_map]
    rfl

/-- The tail `∑ k ∈ Icc 2 K, log p / p ^ k` is at most `2 log p / p ^ 2` for `p ≥ 2`. -/
private lemma log_div_pow_tail_le_w {p : ℝ} (hp : 2 ≤ p) (K : ℕ) :
    ∑ k ∈ Finset.Icc 2 K, Real.log p / p ^ k ≤ 2 * (Real.log p / p ^ 2) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : 2 * (1 / p) ≤ 1 := by
    have h2 : 2 / p ≤ 1 := by
      rw [div_le_one hp0]
      linarith
    calc 2 * (1 / p) = 2 / p := by ring
      _ ≤ 1 := h2
  have hstep : ∀ j : ℕ, Real.log p / p ^ (j + 2) = (Real.log p / p ^ 2) * (1 / p) ^ j := by
    intro j
    have hpw : p ^ (j + 2) = p ^ 2 * p ^ j := by ring
    have hinv : (1 / p) ^ j = (p ^ j)⁻¹ := by rw [one_div, inv_pow]
    rw [hpw, hinv]
    field_simp
  have hlog : (0 : ℝ) ≤ Real.log p / p ^ 2 :=
    div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
  rw [sum_Icc_two_eq_sum_range_w]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range (K - 1)) => hstep j)]
  rw [← Finset.mul_sum]
  have hg := geom_series_le_two_w hr0 hr1 (K - 1)
  calc (Real.log p / p ^ 2) * ∑ j ∈ Finset.range (K - 1), (1 / p) ^ j
      ≤ (Real.log p / p ^ 2) * 2 := by gcongr
    _ = 2 * (Real.log p / p ^ 2) := by ring

/-- On a prime power `Λ d / d = log p / p ^ k`, `p = minFac d`, `k` the exponent. -/
private lemma vonMangoldt_div_eq_w {d : ℕ} (hd : IsPrimePow d) :
    Λ d / (d : ℝ) =
      Real.log (d.minFac : ℝ) / (d.minFac : ℝ) ^ (d.factorization d.minFac) := by
  have hΛ : Λ d = Real.log (d.minFac : ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply, if_pos hd]
  have hd_pow : (d : ℝ) = (d.minFac : ℝ) ^ (d.factorization d.minFac) := by
    rw [← Nat.cast_pow, hd.minFac_pow_factorization_eq]
  rw [hΛ, hd_pow]

/-- The non-prime part of the von Mangoldt sum is bounded by the box sum over primes `p` and
exponents `k` with `2 ≤ k ≤ log 2 N`. -/
private lemma nonprime_vonMangoldt_sum_le_w (N : ℕ) :
    ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime), Λ d / (d : ℝ)
      ≤ ∑ p ∈ Nat.primesLE N,
          ∑ k ∈ Finset.Icc 2 (Nat.log 2 N), Real.log (p : ℝ) / (p : ℝ) ^ k := by
  set S : Finset ℕ := (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime) with hS
  set Spp : Finset ℕ := S.filter IsPrimePow with hSpp
  have hzero : ∑ d ∈ S.filter (fun d => ¬ IsPrimePow d), Λ d / (d : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [Finset.mem_filter] at hd
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hd.2, zero_div]
  have ha : ∑ d ∈ S, Λ d / (d : ℝ) = ∑ d ∈ Spp, Λ d / (d : ℝ) := by
    have h := Finset.sum_filter_add_sum_filter_not S IsPrimePow (fun d => Λ d / (d : ℝ))
    rw [hzero, add_zero] at h
    exact h.symm
  have hinj : ∀ a ∈ Spp, ∀ b ∈ Spp,
      ((a.minFac, a.factorization a.minFac) : ℕ × ℕ)
        = ((b.minFac, b.factorization b.minFac) : ℕ × ℕ) → a = b := by
    intro a ha' b hb' hab
    have haP : IsPrimePow a := (Finset.mem_filter.1 ha').2
    have hbP : IsPrimePow b := (Finset.mem_filter.1 hb').2
    have h1 : a.minFac = b.minFac := congrArg Prod.fst hab
    have h2 : a.factorization a.minFac = b.factorization b.minFac := congrArg Prod.snd hab
    rw [← haP.minFac_pow_factorization_eq, ← hbP.minFac_pow_factorization_eq, h2, h1]
  have hstep : ∑ d ∈ Spp, Λ d / (d : ℝ)
      = ∑ q ∈ Spp.image (fun d => ((d.minFac, d.factorization d.minFac) : ℕ × ℕ)),
          Real.log (q.1 : ℝ) / (q.1 : ℝ) ^ q.2 := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun d hd => vonMangoldt_div_eq_w (Finset.mem_filter.1 hd).2
  have hsub : Spp.image (fun d => ((d.minFac, d.factorization d.minFac) : ℕ × ℕ))
      ⊆ Nat.primesLE N ×ˢ Finset.Icc 2 (Nat.log 2 N) := by
    intro q hq
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨hdS, hdP⟩ := Finset.mem_filter.1 hd
    obtain ⟨hdI, hdnp⟩ := Finset.mem_filter.1 hdS
    obtain ⟨hd0, hdN⟩ := Finset.mem_Ioc.1 hdI
    have hprime : (d.minFac).Prime := Nat.minFac_prime hdP.ne_one
    have hk0 : d.factorization d.minFac ≠ 0 := Nat.factorization_minFac_ne_zero hdP.one_lt
    have hk2 : 2 ≤ d.factorization d.minFac := by
      rcases Nat.lt_or_ge (d.factorization d.minFac) 2 with h | h
      · have hk1 : d.factorization d.minFac = 1 := by omega
        exact absurd (by
          rw [← hdP.minFac_pow_factorization_eq, hk1, pow_one]
          exact hprime) hdnp
      · exact h
    have hpow : 2 ^ d.factorization d.minFac ≤ N := by
      calc 2 ^ d.factorization d.minFac ≤ d.minFac ^ d.factorization d.minFac :=
            Nat.pow_le_pow_left hprime.two_le _
        _ = d := hdP.minFac_pow_factorization_eq
        _ ≤ N := hdN
    rw [Finset.mem_product, Nat.mem_primesLE, Finset.mem_Icc]
    exact ⟨⟨le_trans (Nat.minFac_le hd0) hdN, hprime⟩, hk2,
      Nat.le_log_of_pow_le (by norm_num) hpow⟩
  have hnn : ∀ q ∈ Nat.primesLE N ×ˢ Finset.Icc 2 (Nat.log 2 N),
      (0 : ℝ) ≤ Real.log (q.1 : ℝ) / (q.1 : ℝ) ^ q.2 := by
    intro q hq
    obtain ⟨hq1, _⟩ := Finset.mem_product.1 hq
    have hqp : (q.1).Prime := (Nat.mem_primesLE.1 hq1).2
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hqp.one_le)) (by positivity)
  calc ∑ d ∈ S, Λ d / (d : ℝ)
      = ∑ d ∈ Spp, Λ d / (d : ℝ) := ha
    _ = ∑ q ∈ Spp.image (fun d => ((d.minFac, d.factorization d.minFac) : ℕ × ℕ)),
          Real.log (q.1 : ℝ) / (q.1 : ℝ) ^ q.2 := hstep
    _ ≤ ∑ q ∈ Nat.primesLE N ×ˢ Finset.Icc 2 (Nat.log 2 N),
          Real.log (q.1 : ℝ) / (q.1 : ℝ) ^ q.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun q hq _ => hnn q hq
    _ = ∑ p ∈ Nat.primesLE N,
          ∑ k ∈ Finset.Icc 2 (Nat.log 2 N), Real.log (p : ℝ) / (p : ℝ) ^ k :=
        Finset.sum_product _ _ _

/-- The majorant `∑ n, log n / n ^ 2` is summable. -/
private lemma summable_log_div_sq_w :
    Summable (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
  have hmaj : ∀ n : ℕ, Real.log (n : ℝ) / (n : ℝ) ^ 2 ≤ 2 / (n : ℝ) ^ ((3 : ℝ) / 2) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      norm_num
    have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    have hl : Real.log (n : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
      have h1 := Real.log_le_rpow_div hn.le (show (0 : ℝ) < 1 / 2 by norm_num)
      calc Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) / (1 / 2) := h1
        _ = 2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by ring
    have hkey : (n : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) = (n : ℝ) ^ 2 := by
      rw [← Real.rpow_add hn]
      rw [show (3 : ℝ) / 2 + 1 / 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hs : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hn _
    have ht : (0 : ℝ) < (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hn _
    rw [← hkey]
    rw [div_le_div_iff₀ (by positivity) ht]
    have h2 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := hs.le
    nlinarith [hl, h2, hs, ht]
  have hbase : Summable (fun n : ℕ => 2 / (n : ℝ) ^ ((3 : ℝ) / 2)) := by
    have h := (Real.summable_one_div_nat_rpow (p := (3 : ℝ) / 2)).mpr (by norm_num)
    simpa [div_eq_mul_inv] using h.mul_left 2
  exact Summable.of_nonneg_of_le
    (fun n => div_nonneg (Real.log_natCast_nonneg n) (by positivity)) hmaj hbase

/-- LEAF: Davenport Chapter 4, the passage from Lambda to primes, the character free part: the
prime powers p ^ k with k at least 2 contribute a bounded amount to the sums of Lambda d / d,
since Lambda p ^ k = log p and the sum over p and k at least 2 of log p / p ^ k is at most the
sum of log p / p p - 1, which converges. The d with Lambda d = 0 contribute nothing.
Class MEDIUM. -/
private theorem leaf_vonMangoldt_nonprime_bounded_w :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∑ d ∈ (Ioc 0 N).filter (fun d => ¬ d.Prime), Λ d / d ≤ B := by
  have hsumm := summable_log_div_sq_w
  refine ⟨2 * ∑' n : ℕ, Real.log (n : ℝ) / (n : ℝ) ^ 2, ?_, fun N => ?_⟩
  · have hnn : (0 : ℝ) ≤ ∑' n : ℕ, Real.log (n : ℝ) / (n : ℝ) ^ 2 :=
      tsum_nonneg fun n => div_nonneg (Real.log_natCast_nonneg n) (by positivity)
    linarith
  · have h1 := nonprime_vonMangoldt_sum_le_w N
    have h2 : ∑ p ∈ Nat.primesLE N,
          ∑ k ∈ Finset.Icc 2 (Nat.log 2 N), Real.log (p : ℝ) / (p : ℝ) ^ k
        ≤ ∑ p ∈ Nat.primesLE N, 2 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
      refine Finset.sum_le_sum fun p hp => ?_
      exact log_div_pow_tail_le_w (by exact_mod_cast (Nat.mem_primesLE.1 hp).2.two_le) _
    have hsub2 : Nat.primesLE N ⊆ Finset.Icc 2 N := by
      intro p hp
      rw [Nat.mem_primesLE] at hp
      exact Finset.mem_Icc.2 ⟨hp.2.two_le, hp.1⟩
    have h3 : ∑ p ∈ Nat.primesLE N, 2 * (Real.log (p : ℝ) / (p : ℝ) ^ 2)
        ≤ 2 * ∑' n : ℕ, Real.log (n : ℝ) / (n : ℝ) ^ 2 := by
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      calc ∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) / (p : ℝ) ^ 2
          ≤ ∑ p ∈ Finset.Icc 2 N, Real.log (p : ℝ) / (p : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub2
              (fun x _ _ => div_nonneg (Real.log_natCast_nonneg x) (by positivity))
        _ ≤ ∑' n : ℕ, Real.log (n : ℝ) / (n : ℝ) ^ 2 :=
            hsumm.sum_le_tsum _ (fun i _ => div_nonneg (Real.log_natCast_nonneg i) (by positivity))
    exact le_trans h1 (le_trans h2 h3)

/-- Proved from leaf_vonMangoldt_nonprime_bounded_w, formerly a LEAF: Davenport Chapter 4, the
passage from Lambda to primes: the primes d give exactly the prime sum since Lambda p = log p,
and the rest is bounded in absolute value by the sum of Lambda d / d over nonprime d. -/
private theorem leaf_chi4_prime_powers_w (χ : ℕ → ℝ)
    (hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      |∑ d ∈ Ioc 0 N, χ d * Λ d / d - ∑ p ∈ Nat.primesLE N, χ p * log p / p| ≤ B := by
  obtain ⟨B, hB, HB⟩ := leaf_vonMangoldt_nonprime_bounded_w
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

private lemma chi4_abs_le_w (χ : ℕ → ℝ)
    (hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0) (n : ℕ) :
    |χ n| ≤ 1 := by
  rw [hχ]; split_ifs <;> simp

/-- floor bound: for 1 ≤ d ≤ N, the reciprocal of N / d is at most 2 d / N. -/
private lemma inv_div_le_w {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
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
private theorem chi4_vonMangoldt_bounded_w (χ : ℕ → ℝ)
    (hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, |∑ d ∈ Ioc 0 N, χ d * Λ d / d| ≤ B := by
  obtain ⟨BU, hBU, HU⟩ := leaf_chi4_log_sum_bounded_w χ hχ
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
    rw [leaf_chi4_log_convolution_w χ hχ N]
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
          have hL := leaf_chi4_leibniz_tail_w χ hχ (N / d) hq
          have hI := inv_div_le_w hd.1 hd.2
          have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
          rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hΛ, abs_of_pos hdpos]
          have hχ1 := chi4_abs_le_w χ hχ d
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
private theorem mertens_chi4_of_leaves_w :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊,
        (if p % 4 = 1 then (1 : ℝ) else if p % 4 = 3 then -1 else 0) * log p / p| ≤ B₀ := by
  set χ : ℕ → ℝ := fun n => if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0 with hχd
  have hχ : ∀ n, χ n = if n % 4 = 1 then (1 : ℝ) else if n % 4 = 3 then -1 else 0 :=
    fun n => rfl
  obtain ⟨B1, hB1, H1⟩ := chi4_vonMangoldt_bounded_w χ hχ
  obtain ⟨B2, hB2, H2⟩ := leaf_chi4_prime_powers_w χ hχ
  refine ⟨B1 + B2, by positivity, fun x _ => ?_⟩
  set N := ⌊x⌋₊
  have h := H2 N
  have h1 := H1 N
  change |∑ p ∈ Nat.primesLE N, χ p * log p / p| ≤ B1 + B2
  have := abs_sub_abs_le_abs_sub (∑ p ∈ Nat.primesLE N, χ p * log p / p)
    (∑ d ∈ Ioc 0 N, χ d * Λ d / d)
  rw [abs_sub_comm] at this
  linarith


end Chi4MertensAux

/-- LEAF: page 15, second inequality of the display after display 4.3, the Mertens theorem for
the nonprincipal character chi_4: the sums over primes p at most x of chi_4 p log p / p are
bounded uniformly in x at least 2. Class HARD. Davenport, Multiplicative Number Theory,
Chapter 4, the proof of Dirichlet's theorem, where it follows from L 1 chi_4 = pi / 4 nonzero.
Here chi_4 p is 1 for p = 1 mod 4, -1 for p = 3 mod 4 and 0 for p = 2. -/
theorem leaf_mertens_chi4 :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊,
        (if p % 4 = 1 then (1 : ℝ) else if p % 4 = 3 then -1 else 0) * log p / p| ≤ B₀ :=
  mertens_chi4_of_leaves_w

/-- Abel summation for the sum of chi_4 p / p over a block of primes, for any weight chi, the weighted form of
abel_recip in AlmostPrimes/Decomp1528b. -/
theorem abel_weighted (χ : ℕ → ℝ) {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    ∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime,
        χ p / p =
      (∑ p ∈ Nat.primesLE ⌊x⌋₊,
          χ p * log p / p) / log x -
        (∑ p ∈ Nat.primesLE ⌊y⌋₊,
          χ p * log p / p) / log y +
        ∫ t in y..x, (∑ p ∈ Nat.primesLE ⌊t⌋₊,
          χ p * log p / p) /
            (t * log t ^ 2) := by
  let c : ℕ → ℝ := fun n => if n.Prime then χ n * log n / n else 0
  let f : ℝ → ℝ := fun t => (log t)⁻¹
  have hs (t : ℝ) : (∑ k ∈ Icc 0 ⌊t⌋₊, c k) =
      ∑ p ∈ Nat.primesLE ⌊t⌋₊, χ p * log p / p := by
    simp only [c, ← sum_filter]
    congr 1
    ext k
    simp [Nat.mem_primesLE]
  have hd (t : ℝ) (ht : 1 < t) : HasDerivAt f (-(1 / (t * log t ^ 2))) t := by
    have ht0 : t ≠ 0 := by linarith
    have hl : log t ≠ 0 := (Real.log_pos ht).ne'
    convert (Real.hasDerivAt_log ht0).inv hl using 1
    field_simp
  have hc : ContinuousOn (fun t : ℝ => -(1 / (t * log t ^ 2))) (Set.Icc y x) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have hden : t * log t ^ 2 ≠ 0 := mul_ne_zero ht0 (pow_ne_zero 2 hl)
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  have hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc y x) := by
    exact hc.integrableOn_Icc.congr_fun
      (fun t ht => (hd t (by linarith [ht.1])).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul c (by linarith : 0 ≤ y) hyx
    (fun t ht => (hd t (by linarith [ht.1])).differentiableAt) hi
  have hleft : (∑ k ∈ Ioc ⌊y⌋₊ ⌊x⌋₊, f k * c k) =
      ∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, χ p / p := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p _
    dsimp [f, c]
    split_ifs with hp
    · have hl : log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      field_simp
    · simp
  have hI : (∫ t in Set.Ioc y x, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =
      -(∫ t in y..x, (∑ p ∈ Nat.primesLE ⌊t⌋₊, χ p * log p / p) / (t * log t ^ 2)) := by
    rw [← intervalIntegral.integral_of_le hyx, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hyx] at ht
    change deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) =
      -((∑ p ∈ Nat.primesLE ⌊t⌋₊, χ p * log p / p) / (t * log t ^ 2))
    rw [(hd t (by linarith [ht.1])).deriv, hs]
    ring
  rw [hleft, hs, hs, hI] at h
  simpa [f, div_eq_mul_inv, mul_comm, sub_neg_eq_add] using h

/-- The statement of leaf_mertens_mod4_bias, CONDITIONAL ON leaf_mertens_chi4.
Abel summation gives a block bound 2 B_0 / log y, and log 2 is above 1/2. -/
theorem leaf_mertens_mod4_bias_of_leaves :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y x : ℝ, 2 ≤ y → y ≤ x →
      ∑ p ∈ ((Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime).filter (fun p => p % 4 = 1), (1 : ℝ) / p -
        ∑ p ∈ ((Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime).filter (fun p => p % 4 = 3), (1 : ℝ) / p ≤ B := by
  obtain ⟨B₀, hB₀, H⟩ := leaf_mertens_chi4
  refine ⟨4 * B₀, by positivity, ?_⟩
  intro y x hy hyx
  set χ : ℕ → ℝ := fun p => if p % 4 = 1 then (1 : ℝ) else if p % 4 = 3 then -1 else 0 with hχ
  set F := (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime
  have heq : ∑ p ∈ F.filter (fun p => p % 4 = 1), (1 : ℝ) / p -
      ∑ p ∈ F.filter (fun p => p % 4 = 3), (1 : ℝ) / p = ∑ p ∈ F, χ p / p := by
    rw [Finset.sum_filter (s := F), Finset.sum_filter (s := F), ← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    simp only [hχ]
    split_ifs with h1 h3 <;> first | omega | ring
  rw [heq, abel_weighted χ hy hyx]
  have hx2 : 2 ≤ x := hy.trans hyx
  have hl2 : (1 / 2 : ℝ) < log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hly : 1 / 2 < log y := lt_of_lt_of_le hl2 (Real.log_le_log (by norm_num) hy)
  have hlx : 1 / 2 < log x := lt_of_lt_of_le hl2 (Real.log_le_log (by norm_num) hx2)
  have hlyp : 0 < log y := by linarith
  have hlxp : 0 < log x := by linarith
  set Bf : ℝ → ℝ := fun t => ∑ p ∈ Nat.primesLE ⌊t⌋₊, χ p * log p / p with hBf
  let w : ℝ → ℝ := fun t => 1 / (t * log t ^ 2)
  have hwi : IntervalIntegrable w MeasureTheory.volume y x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hyx]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have hden : t * log t ^ 2 ≠ 0 := mul_ne_zero ht0 (pow_ne_zero 2 hl)
    apply ContinuousAt.continuousWithinAt
    dsimp [w]
    fun_prop (disch := assumption)
  have hint : (∫ t in y..x, w t) = 1 / log y - 1 / log x := by
    have hd : ∀ t ∈ Set.uIcc y x,
        HasDerivAt (fun t : ℝ => -(log t)⁻¹) (w t) t := by
      intro t ht
      rw [Set.uIcc_of_le hyx] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      convert ((Real.hasDerivAt_log ht0).inv hl).neg using 1
      dsimp [w]
      field_simp
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hwi
    simpa only [one_div, neg_sub_neg] using hi
  have hbound : |∫ t in y..x, Bf t / (t * log t ^ 2)| ≤ ∫ t in y..x, B₀ * w t := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
      (f := fun t => Bf t / (t * log t ^ 2)) hyx
      (g := fun t => B₀ * w t) (Filter.Eventually.of_forall (fun t ht => by
        have ht2 : 2 ≤ t := le_trans hy ht.1.le
        have hden : 0 < t * log t ^ 2 := by
          have hlog := Real.log_pos (by linarith : 1 < t)
          positivity
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
        have h := H t ht2
        exact (div_le_div_of_nonneg_right h hden.le).trans_eq (by dsimp [w]; ring)))
      (hwi.const_mul B₀)
    exact hb
  rw [intervalIntegral.integral_const_mul, hint] at hbound
  have hBx := H x hx2
  have hBy := H y hy
  have h1 : Bf x / log x ≤ B₀ / log x := by
    rw [div_le_div_iff_of_pos_right hlxp]; exact (le_abs_self _).trans hBx
  have h2 : -(Bf y / log y) ≤ B₀ / log y := by
    rw [← neg_div, div_le_div_iff_of_pos_right hlyp]; exact (neg_le_abs _).trans hBy
  have h3 : (∫ t in y..x, Bf t / (t * log t ^ 2)) ≤ B₀ * (1 / log y - 1 / log x) :=
    (le_abs_self _).trans hbound
  have hiy : 1 / log y ≤ 2 := by rw [div_le_iff₀ hlyp]; linarith
  have hmain : Bf x / log x - Bf y / log y + ∫ t in y..x, Bf t / (t * log t ^ 2) ≤
      2 * B₀ * (1 / log y) := by
    have : B₀ / log x + B₀ / log y + B₀ * (1 / log y - 1 / log x) = 2 * B₀ * (1 / log y) := by
      ring
    linarith
  calc _ ≤ 2 * B₀ * (1 / log y) := hmain
    _ ≤ 2 * B₀ * 2 := mul_le_mul_of_nonneg_left hiy (by positivity)
    _ = 4 * B₀ := by ring

end LeanLab.Teravainen2016
