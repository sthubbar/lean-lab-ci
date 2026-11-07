import LeanLab.ExceptionalSet.Decomp385a

/-!
Split of the sealed statement `leaf_mean_square` of `LeanLab.ExceptionalSet.Decomp385a` into
three strictly smaller steps, plus an assembly `leaf_mean_square_split` whose statement is the
sealed statement and whose proof uses only the three leaves.

`leaf_mean_square` bounds the second moment of the even weighted error: for `1/2 ≤ Θ < 3/4`, a
zero-free region past `Θ` and `0 < ε < 3/2 - 2Θ`, the sum of `error n ^ 2` over the even
`n ≤ X` is at most `C X ^ (3/2 + 2 Θ + ε)`.  The split keeps the analytic content at a single
scale, which is where the uniform arc estimate is needed, and reduces the passage from one scale
to the whole prefix to an elementary induction that halves the range.

The steps are:
* `leaf_window_energy_four_dvd` and `leaf_window_energy_four_not_dvd`: the second moment over one
  window `(Y/2, Y]`, separated into the even indices divisible by `4` and the even indices not
  divisible by `4`.  These are the two classes of the singular series: only the indices divisible
  by `4` carry the prime `2` in the Euler product of `Sing`, and the two classes are of different
  shape there.  Each leaf sums over a subset of a single window, so each is strictly weaker than
  the prefix statement, which sums over every scale at once.
* `leaf_coarse_even_energy`: an unconditional second moment bound with the much larger exponent
  `5`, which uses no zero-free region at all and needs only a pointwise polynomial size for
  `error`.  It controls the ranges below the window threshold and it is what makes the induction
  start.

The assembly does the bookkeeping: split the prefix at the half `⌊X/2⌋`, bound the window at the
larger scale by the two window leaves and the prefix at half the scale by the induction
hypothesis, and sum the geometric constant `2^p / (2^p - 1)`.

AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.BG2026.Supply385

open Finset Real

/-- `(log x)^2 ≤ 4 x` for `x ≥ 1`, from `log x = 2 log √x ≤ 2 √x`. -/
private lemma log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsub := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hx0.le] at hsub
  have h1 : Real.log x ≤ 2 * Real.sqrt x := by linarith
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h2 : Real.log x * Real.log x ≤ (2 * Real.sqrt x) * (2 * Real.sqrt x) :=
    mul_le_mul h1 h1 h0 (by linarith)
  have h3 : (2 * Real.sqrt x) * (2 * Real.sqrt x) = 4 * x := by
    have : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    nlinarith [this]
  nlinarith [h2, h3]

/-- Each factor of the singular series at a prime `p > 2` is at most `p`. -/
private lemma one_add_inv_two_le {p : ℕ} (hp : 2 < p) : 1 + 1 / ((p : ℝ) - 2) ≤ (p : ℝ) := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpos : 0 < (p : ℝ) - 2 := by linarith
  have hq : 0 < (p : ℝ) := by linarith
  have hkey : 1 / ((p : ℝ) - 2) ≤ (p : ℝ) - 1 := by
    rw [div_le_iff₀ hpos]
    nlinarith [mul_nonneg hq.le (show (0 : ℝ) ≤ (p : ℝ) - 3 by linarith)]
  linarith

/-- The product of the prime factors of `n > 0` over a subcollection is at most `n`. -/
private lemma prod_filter_primeFactors_le {n : ℕ} (hn : 1 ≤ n) :
    ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), (p : ℝ) ≤ (n : ℝ) := by
  have hnpos : 0 < n := by omega
  have hsub : n.primeFactors.filter (fun p => 2 < p) ⊆ n.primeFactors :=
    Finset.filter_subset _ _
  have h1 : (∏ p ∈ n.primeFactors.filter (fun p => 2 < p), p) ∣ ∏ p ∈ n.primeFactors, p :=
    Finset.prod_dvd_prod_of_subset _ _ _ hsub
  have h2 : (∏ p ∈ n.primeFactors, p) ∣ n := Nat.prod_primeFactors_dvd n
  have h3 : (∏ p ∈ n.primeFactors.filter (fun p => 2 < p), p) ≤ n :=
    Nat.le_of_dvd hnpos (h1.trans h2)
  calc ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), (p : ℝ)
      = ((∏ p ∈ n.primeFactors.filter (fun p => 2 < p), p : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (n : ℝ) := by exact_mod_cast h3

/-- `𝔖(n) ≤ 2 C₀ n` for `n ≥ 1`: the Euler product is bounded by the primes themselves. -/
private lemma Sing_le {n : ℕ} (hn : 1 ≤ n) : Sing n ≤ 2 * C0 * (n : ℝ) := by
  have hC0 : (0 : ℝ) ≤ C0 := le_of_lt C0_pos
  have hnonneg : ∀ p ∈ n.primeFactors.filter (fun p => 2 < p),
      (0 : ℝ) ≤ 1 + 1 / ((p : ℝ) - 2) := by
    intro p hp
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Finset.mem_filter.mp hp).2
    have : 0 < (p : ℝ) - 2 := by linarith
    positivity
  have hfac : ∀ p ∈ n.primeFactors.filter (fun p => 2 < p),
      (1 + 1 / ((p : ℝ) - 2)) ≤ (p : ℝ) := by
    intro p hp
    exact one_add_inv_two_le (Finset.mem_filter.mp hp).2
  have hprod : ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2))
      ≤ (n : ℝ) :=
    (Finset.prod_le_prod₀ hnonneg hfac).trans (prod_filter_primeFactors_le hn)
  show 2 * C0 * ∏ p ∈ n.primeFactors.filter (fun p => 2 < p),
      (1 + 1 / ((p : ℝ) - 2)) ≤ 2 * C0 * (n : ℝ)
  exact mul_le_mul_of_nonneg_left hprod (by linarith)

/-- `r₂ n ≤ 8 n²` for `n ≥ 1`: every term is at most `(log n)^2` and there are `n+1` of them. -/
private lemma r2_le {n : ℕ} (hn : 1 ≤ n) : r2 n ≤ 8 * (n : ℝ) ^ 2 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlogsq : Real.log (n : ℝ) ^ 2 ≤ 4 * (n : ℝ) := log_sq_le_four_mul hnR
  have hterm : ∀ m ∈ Finset.range (n + 1),
      ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt (n - m)
        ≤ Real.log (n : ℝ) * Real.log (n : ℝ) := by
    intro m hm
    have hmn : m ≤ n := by
      have := Finset.mem_range.mp hm
      omega
    have h1 : ArithmeticFunction.vonMangoldt m ≤ Real.log (n : ℝ) := by
      have hv := ArithmeticFunction.vonMangoldt_le_log (n := m)
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0] at hv ⊢
        simpa using hlogn
      · have hmono : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hmn)
        linarith
    have h2 : ArithmeticFunction.vonMangoldt (n - m) ≤ Real.log (n : ℝ) := by
      have hv := ArithmeticFunction.vonMangoldt_le_log (n := n - m)
      rcases Nat.eq_zero_or_pos (n - m) with h0 | h0
      · rw [h0] at hv ⊢
        simpa using hlogn
      · have hmono : Real.log ((n - m : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast Nat.sub_le n m)
        linarith
    exact mul_le_mul h1 h2 ArithmeticFunction.vonMangoldt_nonneg hlogn
  have hsum : r2 n ≤ ∑ m ∈ Finset.range (n + 1),
      Real.log (n : ℝ) * Real.log (n : ℝ) := Finset.sum_le_sum hterm
  have hval : ∑ m ∈ Finset.range (n + 1), Real.log (n : ℝ) * Real.log (n : ℝ)
      = ((n : ℝ) + 1) * (Real.log (n : ℝ) * Real.log (n : ℝ)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hstep : ((n : ℝ) + 1) * (Real.log (n : ℝ) * Real.log (n : ℝ)) ≤ 8 * (n : ℝ) ^ 2 := by
    have h1 : ((n : ℝ) + 1) ≤ 2 * (n : ℝ) := by linarith
    have h2 : (0 : ℝ) ≤ Real.log (n : ℝ) * Real.log (n : ℝ) := mul_nonneg hlogn hlogn
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    have h4 : (2 * (n : ℝ)) * (Real.log (n : ℝ) * Real.log (n : ℝ)) ≤
        (2 * (n : ℝ)) * (4 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [h3, h4]
  linarith [hsum, hval, hstep]

/-- Pointwise square bound: `(error n)^2 ≤ (8 + 2 C₀)^2 n^4`, with the case `n = 0` giving `0`. -/
private lemma error_sq_le (n : ℕ) : (error n) ^ 2 ≤ (8 + 2 * C0) ^ 2 * (n : ℝ) ^ 4 := by
  have hC0 : (0 : ℝ) ≤ C0 := le_of_lt C0_pos
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · have hv0 : ArithmeticFunction.vonMangoldt 0 = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero
    have hr2 : r2 0 = 0 := by
      simp [r2, hv0]
    rw [h0]
    simp [error, hr2]
  · have hn : 1 ≤ n := h0
    have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hr2 : 0 ≤ r2 n := by
      unfold r2
      exact Finset.sum_nonneg (fun m _ =>
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg)
    have hSing0 : 0 ≤ Sing n := le_of_lt (Sing_pos n)
    have hr2le : r2 n ≤ 8 * (n : ℝ) ^ 2 := r2_le hn
    have hSingle : (n : ℝ) * Sing n ≤ 2 * C0 * (n : ℝ) ^ 2 := by
      have := Sing_le hn
      nlinarith [hnR]
    have habs : |error n| ≤ (8 + 2 * C0) * (n : ℝ) ^ 2 := by
      have h1 : error n ≤ (8 + 2 * C0) * (n : ℝ) ^ 2 := by
        unfold error
        nlinarith
      have h2 : -((8 + 2 * C0) * (n : ℝ) ^ 2) ≤ error n := by
        unfold error
        nlinarith
      exact abs_le.mpr ⟨h2, h1⟩
    have hsq : |error n| ^ 2 ≤ ((8 + 2 * C0) * (n : ℝ) ^ 2) ^ 2 := by
      have h0' : (0 : ℝ) ≤ |error n| := abs_nonneg _
      have h1' : (0 : ℝ) ≤ (8 + 2 * C0) * (n : ℝ) ^ 2 := by positivity
      nlinarith [habs, h0', h1']
    rw [sq_abs] at hsq
    calc (error n) ^ 2 ≤ ((8 + 2 * C0) * (n : ℝ) ^ 2) ^ 2 := hsq
      _ = (8 + 2 * C0) ^ 2 * (n : ℝ) ^ 4 := by ring

/-- LEAF 1 of 3, the coarse step: the unconditional second moment bound with exponent `5` for the
whole even prefix.  This is the whole-prefix statement with an exponent far above the analytic one,
so no zero-free region is involved: a pointwise polynomial size for `error` and the number of
terms suffice.  It is the start of the induction in the assembly. -/
theorem leaf_coarse_even_energy :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      ∑ n ∈ (Finset.range (X + 1)).filter Even, (error n) ^ 2 ≤ C * (X : ℝ) ^ 5 := by
  refine ⟨2 * (8 + 2 * C0) ^ 2, by positivity, ?_⟩
  intro X hX
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hterm : ∀ n ∈ (Finset.range (X + 1)).filter Even,
      (error n) ^ 2 ≤ (8 + 2 * C0) ^ 2 * (X : ℝ) ^ 4 := by
    intro n hn
    have hnX : n ≤ X := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
      omega
    have hnR : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast hnX
    have h4 : (n : ℝ) ^ 4 ≤ (X : ℝ) ^ 4 := by
      have h0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      exact pow_le_pow_left₀ h0 hnR 4
    exact (error_sq_le n).trans (mul_le_mul_of_nonneg_left h4 (by positivity))
  have hcard : (((Finset.range (X + 1)).filter Even).card : ℝ) ≤ (X : ℝ) + 1 := by
    have h1 : ((Finset.range (X + 1)).filter Even).card ≤ X + 1 := by
      have := Finset.card_filter_le (Finset.range (X + 1)) Even
      simpa using this
    have : (((Finset.range (X + 1)).filter Even).card : ℝ) ≤ ((X + 1 : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at this
    linarith
  have hX1 : (X : ℝ) + 1 ≤ 2 * (X : ℝ) := by linarith
  calc ∑ n ∈ (Finset.range (X + 1)).filter Even, (error n) ^ 2
      ≤ ∑ n ∈ (Finset.range (X + 1)).filter Even, (8 + 2 * C0) ^ 2 * (X : ℝ) ^ 4 :=
        Finset.sum_le_sum hterm
    _ = (((Finset.range (X + 1)).filter Even).card : ℝ) * ((8 + 2 * C0) ^ 2 * (X : ℝ) ^ 4) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((X : ℝ) + 1) * ((8 + 2 * C0) ^ 2 * (X : ℝ) ^ 4) := by
        have h0 : (0 : ℝ) ≤ (8 + 2 * C0) ^ 2 * (X : ℝ) ^ 4 := by positivity
        exact mul_le_mul_of_nonneg_right hcard h0
    _ ≤ 2 * (8 + 2 * C0) ^ 2 * (X : ℝ) ^ 5 := by
        have h0 : (0 : ℝ) ≤ (8 + 2 * C0) ^ 2 * (X : ℝ) ^ 4 := by positivity
        have h3 := mul_le_mul_of_nonneg_right hX1 h0
        nlinarith [h3]

/-- LEAF 2 of 3, one scale of the analytic step, on the even indices divisible by `4`: some
nonnegative `C` bounds the second moment over the window `(Y/2, Y]` restricted to the even `n`
with `4 ∣ n`, by `C Y ^ (3/2 + 2 Θ + ε)`, for every `Y` past a fixed threshold.  This is a sum
over a subset of one window, not over the prefix.  It is where the uniform arc estimate from the
zero-free region enters. -/
theorem leaf_window_energy_four_dvd (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ 4 ∣ n), (error n) ^ 2 ≤
        C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- LEAF 3 of 3, the other class of the same scale: the second moment over the window `(Y/2, Y]`
restricted to the even `n` with `4 ∤ n`, that is `n ≡ 2 (mod 4)`, with the same exponent.  At these
indices the prime `2` contributes to the singular series only through the constant `2 C₀`, which is
why the class is estimated separately.  Strictly easier than the prefix statement: one window, one
class. -/
theorem leaf_window_energy_four_not_dvd (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ ¬ 4 ∣ n), (error n) ^ 2 ≤
        C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- The geometric constant step: if `K` dominates `Cw * 2^p / (2^p - 1)` then `Cw` plus the half
of `K` in the scale `2^p` still fits inside `K`.  This is the inequality that makes the halving
induction of the assembly close. -/
private lemma const_step {Cw K p : ℝ} (hp : 0 < p)
    (hK : Cw * (2 : ℝ) ^ p / ((2 : ℝ) ^ p - 1) ≤ K) :
    K / (2 : ℝ) ^ p + Cw ≤ K := by
  have ht1 : (1 : ℝ) < (2 : ℝ) ^ p := Real.one_lt_rpow (by norm_num) hp
  have ht0 : (0 : ℝ) < (2 : ℝ) ^ p - 1 := by linarith
  have htpos : (0 : ℝ) < (2 : ℝ) ^ p := by linarith
  have hA : Cw * (2 : ℝ) ^ p ≤ K * ((2 : ℝ) ^ p - 1) := by
    rw [div_le_iff₀ ht0] at hK
    linarith
  have hkey : K / (2 : ℝ) ^ p + Cw = (K + Cw * (2 : ℝ) ^ p) / (2 : ℝ) ^ p := by
    field_simp
  rw [hkey, div_le_iff₀ htpos]
  linarith

/-- Splitting the even prefix at `m ≤ X`: the terms with `n < m` and the terms `m ≤ n ≤ X`. -/
private lemma sum_window_split {f : ℕ → ℝ} {m X : ℕ} (hm : m ≤ X) :
    ∑ n ∈ (Finset.range (X + 1)).filter Even, f n =
      ∑ n ∈ (Finset.range m).filter Even, f n + ∑ n ∈ (Finset.Icc m X).filter Even, f n := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_range_add_sum_Ico (fun n => if Even n then f n else 0)
    (by omega : m ≤ X + 1)]
  rw [Finset.Ico_add_one_right_eq_Icc]

/-- Splitting the even terms of an interval into the class divisible by `4` and its complement. -/
private lemma window_four_split {f : ℕ → ℝ} {a b : ℕ} :
    ∑ n ∈ (Finset.Icc a b).filter Even, f n =
      ∑ n ∈ (Finset.Icc a b).filter (fun n => Even n ∧ 4 ∣ n), f n
        + ∑ n ∈ (Finset.Icc a b).filter (fun n => Even n ∧ ¬ 4 ∣ n), f n := by
  have hpoint : ∀ n : ℕ, (if Even n then f n else 0) =
      (if Even n ∧ 4 ∣ n then f n else 0) + (if Even n ∧ ¬ 4 ∣ n then f n else 0) := by
    intro n
    by_cases h1 : Even n
    · by_cases h2 : (4 : ℕ) ∣ n
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [h1]
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun n _ => hpoint n)

/-- `leaf_mean_square` of `LeanLab.ExceptionalSet.Decomp385a`, assembled from the three leaves:
the coarse prefix bound starts the induction, the two window leaves bound one scale, and the
prefix at half the scale comes from the induction hypothesis. -/
theorem leaf_mean_square_split (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2 ≤
        C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  obtain ⟨Cc, hCc0, hcoarse⟩ := leaf_coarse_even_energy
  obtain ⟨C4, hC40, Y4, hY4, hwin4⟩ :=
    leaf_window_energy_four_dvd Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C2, hC20, Y2, hY2, hwin2⟩ :=
    leaf_window_energy_four_not_dvd Θ hΘ1 hΘ2 hZF ε hε hsublinear
  set p : ℝ := 3 / 2 + 2 * Θ + ε with hpdef
  have hp0 : 0 < p := by rw [hpdef]; linarith
  set Cw : ℝ := C4 + C2 with hCwdef
  have hCw0 : 0 ≤ Cw := by rw [hCwdef]; linarith
  set N₁ : ℕ := max (max Y4 Y2) 2 with hN1def
  have hN1ge : 1 ≤ N₁ := by rw [hN1def]; omega
  have hY4N : Y4 ≤ N₁ := by rw [hN1def]; omega
  have hY2N : Y2 ≤ N₁ := by rw [hN1def]; omega
  set K : ℝ := max (Cw * (2 : ℝ) ^ p / ((2 : ℝ) ^ p - 1)) (Cc * (N₁ : ℝ) ^ 5) with hKdef
  have hKN : Cc * (N₁ : ℝ) ^ 5 ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hKc : Cw * (2 : ℝ) ^ p / ((2 : ℝ) ^ p - 1) ≤ K := by
    rw [hKdef]; exact le_max_left _ _
  have hK0 : 0 ≤ K := le_trans (by positivity) hKN
  have hwin4' : ∀ Y : ℕ, N₁ ≤ Y →
      ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ 4 ∣ n), (error n) ^ 2 ≤
        C4 * (Y : ℝ) ^ p := by
    intro Y hY
    exact hwin4 Y (le_trans hY4N hY)
  have hwin2' : ∀ Y : ℕ, N₁ ≤ Y →
      ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ ¬ 4 ∣ n), (error n) ^ 2 ≤
        C2 * (Y : ℝ) ^ p := by
    intro Y hY
    exact hwin2 Y (le_trans hY2N hY)
  refine ⟨K, N₁, ?_⟩
  have key : ∀ X : ℕ, N₁ ≤ X →
      ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2 ≤ K * (X : ℝ) ^ p := by
    intro X
    refine Nat.strong_induction_on X ?_
    intro X ih hX
    by_cases hsmall : X ≤ N₁
    · -- below the threshold: the coarse bound at the threshold
      have hX1 : 1 ≤ X := le_trans hN1ge hX
      have hmono : ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2
          ≤ ∑ n ∈ (range (N₁ + 1)).filter Even, (error n) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
          exact ⟨by omega, hn.2⟩
        · intro n _ _
          positivity
      have hXp1 : (1 : ℝ) ≤ (X : ℝ) ^ p := by
        have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
        calc (1 : ℝ) = (1 : ℝ) ^ p := by simp
          _ ≤ (X : ℝ) ^ p := Real.rpow_le_rpow (by norm_num) hXR hp0.le
      calc ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2
          ≤ ∑ n ∈ (range (N₁ + 1)).filter Even, (error n) ^ 2 := hmono
        _ ≤ Cc * (N₁ : ℝ) ^ 5 := hcoarse N₁ hN1ge
        _ ≤ K := hKN
        _ = K * 1 := by ring
        _ ≤ K * (X : ℝ) ^ p := mul_le_mul_of_nonneg_left hXp1 hK0
    · -- above the threshold: one window plus the prefix at half the scale
      have hXgt : N₁ < X := lt_of_not_ge hsmall
      have hX1 : 1 ≤ X := by omega
      have hX2 : 2 ≤ X := by omega
      have hhalf_lt : X / 2 < X := Nat.div_lt_self (by omega : 0 < X) (by norm_num)
      have hw : ∑ n ∈ (Icc (X / 2 + 1) X).filter Even, (error n) ^ 2 ≤ Cw * (X : ℝ) ^ p := by
        have hfour := window_four_split (f := fun n => (error n) ^ 2) (a := X / 2 + 1) (b := X)
        rw [hfour]
        have h4 := hwin4' X (le_of_lt hXgt)
        have h2 := hwin2' X (le_of_lt hXgt)
        calc ∑ n ∈ (Icc (X / 2 + 1) X).filter (fun n => Even n ∧ 4 ∣ n), (error n) ^ 2
            + ∑ n ∈ (Icc (X / 2 + 1) X).filter (fun n => Even n ∧ ¬ 4 ∣ n), (error n) ^ 2
            ≤ C4 * (X : ℝ) ^ p + C2 * (X : ℝ) ^ p := add_le_add h4 h2
          _ = (C4 + C2) * (X : ℝ) ^ p := by ring
          _ = Cw * (X : ℝ) ^ p := by rw [hCwdef]
      have hpre : ∑ n ∈ (range (X / 2 + 1)).filter Even, (error n) ^ 2
          ≤ K * ((X : ℝ) / 2) ^ p := by
        have hhalf : ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) / 2 := by
          have h := Nat.div_mul_le_self X 2
          have h' : ((X / 2 : ℕ) : ℝ) * 2 ≤ (X : ℝ) := by exact_mod_cast h
          linarith
        by_cases hmid : N₁ ≤ X / 2
        · have h := ih (X / 2) hhalf_lt hmid
          have hmono := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg (X / 2)) hhalf hp0.le) hK0
          exact le_trans h hmono
        · have hmid' : X / 2 ≤ N₁ := le_of_lt (lt_of_not_ge hmid)
          have hmono : ∑ n ∈ (range (X / 2 + 1)).filter Even, (error n) ^ 2
              ≤ ∑ n ∈ (range (N₁ + 1)).filter Even, (error n) ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro n hn
              simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
              exact ⟨by omega, hn.2⟩
            · intro n _ _
              positivity
          have hco := hcoarse N₁ hN1ge
          have hbase : ∑ n ∈ (range (X / 2 + 1)).filter Even, (error n) ^ 2 ≤ K := by
            calc ∑ n ∈ (range (X / 2 + 1)).filter Even, (error n) ^ 2
                ≤ ∑ n ∈ (range (N₁ + 1)).filter Even, (error n) ^ 2 := hmono
              _ ≤ Cc * (N₁ : ℝ) ^ 5 := hco
              _ ≤ K := hKN
          have hhalf1 : (1 : ℝ) ≤ ((X : ℝ) / 2) ^ p := by
            have hXR : (1 : ℝ) ≤ (X : ℝ) / 2 := by
              have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
              linarith
            calc (1 : ℝ) = (1 : ℝ) ^ p := by simp
              _ ≤ ((X : ℝ) / 2) ^ p := Real.rpow_le_rpow (by norm_num) hXR hp0.le
          calc ∑ n ∈ (range (X / 2 + 1)).filter Even, (error n) ^ 2 ≤ K := hbase
            _ = K * 1 := by ring
            _ ≤ K * ((X : ℝ) / 2) ^ p := mul_le_mul_of_nonneg_left hhalf1 hK0
      have hsplit := sum_window_split (f := fun n => (error n) ^ 2) (m := X / 2 + 1) (X := X)
        (by omega)
      rw [hsplit]
      have hXp : 0 ≤ (X : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg X) p
      have hstep : K * ((2 : ℝ) ^ p)⁻¹ + Cw ≤ K := by
        have := const_step hp0 hKc
        simpa [div_eq_mul_inv] using this
      calc ∑ n ∈ (range (X / 2 + 1)).filter Even, (error n) ^ 2
          + ∑ n ∈ (Icc (X / 2 + 1) X).filter Even, (error n) ^ 2
          ≤ K * ((X : ℝ) / 2) ^ p + Cw * (X : ℝ) ^ p := add_le_add hpre hw
        _ = (K * ((2 : ℝ) ^ p)⁻¹) * (X : ℝ) ^ p + Cw * (X : ℝ) ^ p := by
            rw [Real.div_rpow (Nat.cast_nonneg X) (by norm_num) p]
            ring
        _ = ((K * ((2 : ℝ) ^ p)⁻¹) + Cw) * (X : ℝ) ^ p := by ring
        _ ≤ K * (X : ℝ) ^ p := mul_le_mul_of_nonneg_right hstep hXp
  exact key

-- Axiom audit drivers.
#print axioms leaf_coarse_even_energy
#print axioms leaf_mean_square_split

end LeanLab.ExceptionalSet.BG2026.Supply385
