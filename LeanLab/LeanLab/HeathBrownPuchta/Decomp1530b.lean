/-
Heath-Brown and Puchta 2002, Integers represented as a sum of primes and powers of two,
arXiv math/0201299. Unit U-1530, run 20261026T0004Z-24325, type DECOMPOSE, file b of three.

Lemma 8, Section 5: `J = ∫₀¹ |S(α) T(α)|² dα ≤ {C₀ C₁ C₂ / log² 2 + 1/log 2 + o(1)} N`, with
`S(α) = Σ_{ϖN < p ≤ N} e(αp)`, `T(α) = Σ_{1 ≤ ν ≤ L} e(α 2^ν)`, `L = [log(N/2K)/log 2]`.
In Assembly.lean it enters through `lemma9_out_of_lemma8` as the hypothesis `h8`, still open.
The proof in Section 5, split here into leaves:

* `J = Σ_{μ, ν ≤ L} r(2^μ - 2^ν)`, `r(n) = #{ϖN < p₁, p₂ ≤ N : p₁ - p₂ = n}`;
* diagonal `μ = ν`: `L` terms each `π(N) - π(ϖN) ≤ (1 + o(1)) N / log N`, total `≤ N/log 2`;
* off diagonal: Chen's bound `r(n) ≤ C₀ C₁ h(n) N / log² N` stays an open input, not split
  here; `h(2^μ - 2^ν) = h(2^{μ-ν} - 1)`; grouping by `l = |μ - ν|` gives
  `2 Σ_{l ≤ L} (L - l) h(2^l - 1)`;
* `Σ_{j ≤ J} h(2^j - 1) = Σ_e κ(e) [J/e] ≤ C₂ J`, then partial summation gives
  `Σ_{l ≤ L} (L - l) h(2^l - 1) ≤ C₂ L²/2`, so the off diagonal is `≤ C₀ C₁ C₂ N / log² 2`.

Only the upper bound `Σ_{j ≤ J} h(2^j - 1) ≤ C₂ J` is needed for Lemma 8; the paper states the
asymptotic `C₂ J + O(J^{1/2})`. Page numbers are not visible in the arXiv text read for this
unit; Section and display numbers are given. The paper copy was NOT FOUND in either lab location;
the text used is arXiv math/0201299 through WebFetch, 2026-10-26.

ASSEMBLY, real proofs, CONDITIONAL ON the leaves below and using the lab's proved
`sum_kappaTrue_divisors`: `hsum_bound`, `offdiag_total`, `offdiag_main_term`.

AI-written Lean code, Claude, 2026-10-26. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import LeanLab.HeathBrownPuchta.Decomp1530a
import LeanLab.HeathBrownPuchta.C2Inputs

namespace LeanLab.HeathBrownPuchta.Decomp1530b

open Finset Real Filter LeanLab.HeathBrownPuchta.Decomp1530a
open LeanLab.HeathBrownPuchta.Lemma8Const LeanLab.HeathBrownPuchta.C2Inputs
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

/-- The primes `p` with `ϖN < p ≤ N`, Section 2. -/
noncomputable def primesIn (N : ℕ) (w : ℝ) : Finset ℕ :=
  (Icc 1 N).filter fun p => p.Prime ∧ w * N < p

/-- `S(α) = Σ_{ϖN < p ≤ N} e(αp)`, Section 2. -/
noncomputable def Sp (N : ℕ) (w : ℝ) (α : ℝ) : ℂ := ∑ p ∈ primesIn N w, ee (α * p)

/-- `T(α) = Σ_{1 ≤ ν ≤ L} e(α 2^ν)`, Section 2. -/
noncomputable def Tp (L : ℕ) (α : ℝ) : ℂ := ∑ ν ∈ Icc 1 L, ee (α * 2 ^ ν)

/-- `J = ∫₀¹ |S(α) T(α)|² dα`, Section 5. -/
noncomputable def Jint (N : ℕ) (w : ℝ) (L : ℕ) : ℝ := ∫ α in (0 : ℝ)..1, ‖Sp N w α * Tp L α‖ ^ 2

/-- `r(n) = #{ϖN < p₁, p₂ ≤ N : p₁ - p₂ = n}`, Section 5. -/
noncomputable def rcount (N : ℕ) (w : ℝ) (n : ℤ) : ℕ :=
  ((primesIn N w ×ˢ primesIn N w).filter fun x => (x.1 : ℤ) - x.2 = n).card

/-- `L = [log(N/2K)/log 2]`, Section 2. -/
noncomputable def Lpar (N K : ℕ) : ℕ := ⌊Real.log (N / (2 * K)) / Real.log 2⌋₊

/-! ### Leaves: the expansion of `J` -/

/-- LEAF. Unit U-1530. Orthogonality: `∫₀¹ e(αm) dα` is `1` for `m = 0` and `0` for every other
integer `m`; Section 5, the expansion of `J`. -/
theorem orth (m : ℤ) : ∫ α in (0 : ℝ)..1, ee (α * m) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [ee]
  · rw [if_neg hm]
    unfold ee
    have hc : 2 * (π : ℂ) * Complex.I * m ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero) (by exact_mod_cast hm)
    have hh := integral_exp_mul_complex (a := (0 : ℝ)) (b := 1) hc
    have hp : Complex.exp (2 * (π : ℂ) * Complex.I * m) = 1 := by
      simpa only [mul_comm] using Complex.exp_int_mul_two_pi_mul_I m
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, hp, sub_self, zero_div] at hh
    convert hh using 1
    apply intervalIntegral.integral_congr
    intro α hα
    congr 1
    push_cast
    ring

/-- Finite character Parseval identity, paper page 20, the first expansion of Lemma 8. -/
theorem finite_parseval {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∫ α in (0 : ℝ)..1, ‖∑ i ∈ s, ee (α * f i)‖ ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, (if f i = f j then (1 : ℝ) else 0) := by
  classical
  have hn (z : ℂ) : Complex.ofReal (‖z‖ ^ 2) = z * (starRingEnd ℂ) z := by
    simpa only [Complex.normSq_eq_norm_sq] using (Complex.mul_conj z).symm
  have hc (x : ℝ) : (starRingEnd ℂ) (ee x) = ee (-x) := by
    unfold ee
    rw [← Complex.exp_conj]
    congr 1
    simp [map_ofNat]
  have hadd (x y : ℝ) : ee (x + y) = ee x * ee y := by
    unfold ee
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  have hp (α : ℝ) : Complex.ofReal (‖∑ i ∈ s, ee (α * f i)‖ ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, ee (α * ((f i - f j : ℤ) : ℝ)) := by
    rw [hn]
    simp only [map_sum, hc, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [← hadd]
    congr 1
    push_cast
    ring
  have hex (i j : ι) : Continuous fun α : ℝ => ee (α * ((f i - f j : ℤ) : ℝ)) := by
    unfold ee
    fun_prop
  have hinner (i : ι) :
      (∫ α in (0 : ℝ)..1, ∑ j ∈ s, ee (α * ((f i - f j : ℤ) : ℝ))) =
        ∑ j ∈ s, ∫ α in (0 : ℝ)..1, ee (α * ((f i - f j : ℤ) : ℝ)) :=
    intervalIntegral.integral_finsetSum (fun j hj => (hex i j).intervalIntegrable 0 1)
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hp]
  rw [intervalIntegral.integral_finsetSum (fun i hi => by
    apply Continuous.intervalIntegrable
    unfold ee
    fun_prop)]
  simp_rw [hinner, orth, sub_eq_zero]
  push_cast
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  split_ifs <;> norm_num

/-- LEAF. Unit U-1530. `J = Σ_{1 ≤ μ, ν ≤ L} r(2^μ - 2^ν)`; Section 5, first display of the
proof of Lemma 8. -/
theorem J_expand (N : ℕ) (w : ℝ) (L : ℕ) :
    Jint N w L = ∑ μ ∈ Icc 1 L, ∑ ν ∈ Icc 1 L, (rcount N w ((2 : ℤ) ^ μ - 2 ^ ν) : ℝ) := by
  classical
  let s := Icc 1 L ×ˢ primesIn N w
  let f : ℕ × ℕ → ℤ := fun x => x.2 - (2 : ℤ) ^ x.1
  have hc (x : ℝ) : (starRingEnd ℂ) (ee x) = ee (-x) := by
    unfold ee
    rw [← Complex.exp_conj]
    congr 1
    simp [map_ofNat]
  have hadd (x y : ℝ) : ee (x + y) = ee x * ee y := by
    unfold ee
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  have heq (α : ℝ) : Sp N w α * (starRingEnd ℂ) (Tp L α) = ∑ x ∈ s, ee (α * f x) := by
    unfold Sp Tp
    simp only [map_sum, hc, mul_sum, sum_mul]
    dsimp [s, f]
    rw [sum_product]
    apply sum_congr rfl
    intro μ hμ
    apply sum_congr rfl
    intro p hp
    rw [← hadd]
    congr 1
    push_cast
    ring
  calc
    Jint N w L = ∫ α in (0 : ℝ)..1, ‖∑ x ∈ s, ee (α * f x)‖ ^ 2 := by
      unfold Jint
      apply intervalIntegral.integral_congr
      intro α hα
      dsimp only
      rw [← heq]
      simp [norm_mul]
    _ = ∑ x ∈ s, ∑ y ∈ s, (if f x = f y then (1 : ℝ) else 0) := finite_parseval s f
    _ = _ := by
      dsimp [s, f]
      simp_rw [sum_product]
      apply sum_congr rfl
      intro μ hμ
      rw [sum_comm]
      apply sum_congr rfl
      intro ν hν
      unfold rcount
      simp only [Finset.card_eq_sum_ones, sum_filter, sum_product, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero]
      apply sum_congr rfl
      intro p hp
      apply sum_congr rfl
      intro q hq
      have hi : ((p : ℤ) - (2 : ℤ) ^ μ = q - (2 : ℤ) ^ ν) ↔
          (p : ℤ) - q = (2 : ℤ) ^ μ - (2 : ℤ) ^ ν := by omega
      simp only [hi]

/-! ### Leaves: the diagonal -/

/-- LEAF. Unit U-1530. The prime number theorem upper half on `(ϖN, N]`: for `ϖ ≥ 0` and every
`ε > 0`, eventually `#{ϖN < p ≤ N} ≤ (1 + ε) N / log N`; Section 5, the diagonal terms of the
proof of Lemma 8. -/
theorem pi_upper {w : ℝ} (hw : 0 ≤ w) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ((primesIn N w).card : ℝ) ≤ (1 + ε) * N / Real.log N := by
  sorry

/-- LEAF. Unit U-1530. For `N ≥ 1` and `K ≥ 1`, `L = [log(N/2K)/log 2] ≤ log N/log 2`; Section 2,
the definition of `L`. -/
theorem Lpar_le_log {N K : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    (Lpar N K : ℝ) ≤ Real.log N / Real.log 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  unfold Lpar
  by_cases hz : 0 ≤ Real.log ((N : ℝ) / (2 * K)) / Real.log 2
  · apply (Nat.floor_le hz).trans
    apply div_le_div_of_nonneg_right _ h2.le
    apply Real.log_le_log (by positivity)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mpr
    nlinarith
  · rw [Nat.floor_of_nonpos (le_of_not_ge hz)]
    simpa using div_nonneg hlog h2.le

/-- LEAF. Unit U-1530. For `N ≥ 1` and `K ≥ 1`,
`L ≥ log N/log 2 - (1 + log(2K)/log 2)`; Section 2, the definition of `L`, as needed for
the exponent in Section 7. -/
theorem Lpar_ge_log {N K : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    Real.log N / Real.log 2 - (1 + Real.log (2 * K) / Real.log 2) ≤ Lpar N K := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hk : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh := Nat.lt_floor_add_one (Real.log ((N : ℝ) / (2 * K)) / Real.log 2)
  rw [Real.log_div hn.ne' (by positivity), sub_div] at hh
  unfold Lpar
  rw [Real.log_div hn.ne' (by positivity), sub_div]
  linarith

/-- LEAF. Unit U-1530. The diagonal scale: for `N > 1` and `0 ≤ L ≤ log N/log 2`,
`L · N/log N ≤ N/log 2`; Section 5, the source of the term `1/log 2` in Lemma 8. -/
theorem diag_scale {N L : ℝ} (hN : 1 < N) (hL0 : 0 ≤ L) (hL : L ≤ Real.log N / Real.log 2) :
    L * (N / Real.log N) ≤ N / Real.log 2 := by
  have hn : 0 < Real.log N := Real.log_pos hN
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    L * (N / Real.log N) ≤ (Real.log N / Real.log 2) * (N / Real.log N) :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    _ = N / Real.log 2 := by field_simp

/-! ### Leaves: the off diagonal -/

/-- LEAF. Unit U-1530. For `ν < μ`, `h(2^μ - 2^ν) = h(2^{μ-ν} - 1)`, since `h` sees only odd
primes; Section 5, proof of Lemma 8. -/
theorem h_pow_sub {μ ν : ℕ} (hνμ : ν < μ) : h (2 ^ μ - 2 ^ ν) = h (2 ^ (μ - ν) - 1) := by
  unfold h
  congr 1
  have hpow : 1 < (2 : ℕ) ^ (μ - ν) := one_lt_pow₀ (by norm_num) (by omega)
  have hn : 2 ^ (μ - ν) - 1 ≠ 0 := by omega
  have hfac : 2 ^ μ - 2 ^ ν = 2 ^ ν * (2 ^ (μ - ν) - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, ← pow_add, show ν + (μ - ν) = μ by omega]
  rw [hfac, Nat.primeFactors_mul (by positivity) hn]
  ext p
  simp only [mem_filter, mem_union]
  constructor
  · intro hh
    rcases hh.1 with hp | hp
    · have hprime := Nat.prime_of_mem_primeFactors hp
      have hd := Nat.dvd_of_mem_primeFactors hp
      have h2 := hprime.dvd_of_dvd_pow hd
      have heq := (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp h2
      rcases heq with heq | heq
      · exact False.elim (hprime.ne_one heq)
      · exact False.elim (hh.2 heq)
    · exact ⟨hp, hh.2⟩
  · exact fun hh => ⟨Or.inr hh.1, hh.2⟩

/-- LEAF. Unit U-1530. Grouping the off diagonal pairs by `l = |μ - ν|`: there are `2(L - l)`
ordered pairs in `[1, L]²` at distance `l`, so the sum of `f(|μ - ν|)` over `μ ≠ ν` is
`2 Σ_{1 ≤ l ≤ L} (L - l) f(l)`; Section 5, proof of Lemma 8. -/
theorem offdiag_grouping (f : ℕ → ℝ) (L : ℕ) :
    ∑ μ ∈ Icc 1 L, ∑ ν ∈ Icc 1 L, (if μ = ν then 0 else f (max μ ν - min μ ν)) =
      2 * ∑ l ∈ Icc 1 L, ((L : ℝ) - l) * f l := by
  induction L with
  | zero => simp
  | succ L ih =>
    have href : ∑ i ∈ Icc 1 L, f (L + 1 - i) = ∑ i ∈ Icc 1 L, f i := by
      apply sum_bij (fun i _ => L + 1 - i)
      · intro i hi
        simp only [mem_Icc] at hi ⊢
        omega
      · intro i hi j hj heq
        simp only [mem_Icc] at hi hj
        omega
      · intro j hj
        refine ⟨L + 1 - j, ?_, ?_⟩
        · simp only [mem_Icc] at hj ⊢; omega
        · simp only [mem_Icc] at hj; omega
      · intro i hi; rfl
    have hcol (i : ℕ) (hi : i ∈ Icc 1 L) :
        (if i = L + 1 then 0 else f (max i (L + 1) - min i (L + 1))) = f (L + 1 - i) := by
      have hl := (mem_Icc.mp hi).2
      simp [show i ≠ L + 1 by omega, max_eq_right (by omega : i ≤ L + 1),
        min_eq_left (by omega : i ≤ L + 1)]
    have hrow (i : ℕ) (hi : i ∈ Icc 1 L) :
        (if L + 1 = i then 0 else f (max (L + 1) i - min (L + 1) i)) = f (L + 1 - i) := by
      have hl := (mem_Icc.mp hi).2
      simp [show L + 1 ≠ i by omega, max_eq_left (by omega : i ≤ L + 1),
        min_eq_right (by omega : i ≤ L + 1)]
    rw [sum_Icc_succ_top (by omega)]
    have hold : ∑ μ ∈ Icc 1 L, ∑ ν ∈ Icc 1 (L + 1),
        (if μ = ν then 0 else f (max μ ν - min μ ν)) =
        (∑ μ ∈ Icc 1 L, ∑ ν ∈ Icc 1 L, (if μ = ν then 0 else f (max μ ν - min μ ν))) +
          ∑ i ∈ Icc 1 L, f (L + 1 - i) := by
      simp_rw [sum_Icc_succ_top (show 1 ≤ L + 1 by omega)]
      rw [sum_add_distrib]
      congr 1
      exact sum_congr rfl hcol
    rw [hold, sum_Icc_succ_top (by omega)]
    simp only [ite_true, add_zero]
    rw [sum_congr rfl hrow, href, ih, sum_Icc_succ_top (by omega)]
    simp only [Nat.cast_add, Nat.cast_one, sub_self, zero_mul, add_zero]
    rw [show (∑ l ∈ Icc 1 L, (((L : ℝ) + 1) - l) * f l) =
      (∑ l ∈ Icc 1 L, ((L : ℝ) - l) * f l) + ∑ l ∈ Icc 1 L, f l by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro l hl
        ring]
    ring

/-- LEAF. Unit U-1530. Swapping a divisor sum:
`Σ_{1 ≤ j ≤ J} Σ_{e ∣ j} κ(e) = Σ_{1 ≤ e ≤ J} κ(e) [J/e]`; Section 5, the step
`Σ_{j ≤ J} h(2^j - 1) = Σ_d k(d) [J/ε(d)]`. -/
theorem divisor_swap (κ : ℕ → ℝ) (J : ℕ) :
    ∑ j ∈ Icc 1 J, ∑ e ∈ j.divisors, κ e = ∑ e ∈ Icc 1 J, κ e * ((J / e : ℕ) : ℝ) := by
  let f : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else κ n, by simp⟩
  have hset : Icc 1 J = Ioc 0 J := by ext n; simp; omega
  rw [hset]
  have hh := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum f J
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at hh
  convert hh using 1
  · apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro d hd
    simp [f, (Nat.pos_of_mem_divisors hd).ne']
  · apply sum_congr rfl
    intro n hn
    simp [f, (mem_Ioc.mp hn).1.ne']

/-- LEAF. Unit U-1530. The series `Σ_{e ≥ 1} κ(e)/e`, which is `C₂` regrouped, converges;
Section 5, display 35. -/
theorem C2_summable : Summable fun e : ℕ => kappaTrue (e + 1) / ((e : ℝ) + 1) := by
  sorry

/-- LEAF. Unit U-1530. Given convergence, `Σ_{1 ≤ e ≤ J} κ(e) [J/e] ≤ C₂ J`, from `[J/e] ≤ J/e`,
`κ ≥ 0` and the lab's `grouping`; Section 5, the upper half of
`Σ_{j ≤ J} h(2^j - 1) = C₂ J + O(J^{1/2})`. -/
theorem kappa_floor_le (hs : Summable fun e : ℕ => kappaTrue (e + 1) / ((e : ℝ) + 1)) (J : ℕ) :
    ∑ e ∈ Icc 1 J, kappaTrue e * ((J / e : ℕ) : ℝ) ≤ C2 * J := by
  have hs' : Summable fun e : ℕ => kappaTrue e / (e : ℝ) := by
    apply (summable_nat_add_iff 1).mp
    simpa using hs
  have ht : ∑' e : ℕ, kappaTrue e / (e : ℝ) = C2 := by
    rw [grouping, tsum_eq_zero_add' (by simpa using hs)]
    simp
  have hp : ∑ e ∈ Icc 1 J, kappaTrue e / (e : ℝ) ≤ C2 := by
    rw [← ht]
    exact hs'.sum_le_tsum (Icc 1 J) (fun e he => div_nonneg (kappaTrue_nonneg e) (Nat.cast_nonneg e))
  calc
    _ ≤ ∑ e ∈ Icc 1 J, (kappaTrue e / (e : ℝ)) * J := by
      apply sum_le_sum
      intro e he
      calc
        _ ≤ kappaTrue e * ((J : ℝ) / e) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le (kappaTrue_nonneg e)
        _ = _ := by ring
    _ = (∑ e ∈ Icc 1 J, kappaTrue e / (e : ℝ)) * J := (sum_mul ..).symm
    _ ≤ C2 * J := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg J)

/-- LEAF. Unit U-1530. Partial summation:
`Σ_{1 ≤ l ≤ L} (L - l) a(l) = Σ_{1 ≤ J ≤ L-1} Σ_{1 ≤ j ≤ J} a(j)`; Section 5, proof of
Lemma 8. -/
theorem partial_summation (a : ℕ → ℝ) (L : ℕ) :
    ∑ l ∈ Icc 1 L, ((L : ℝ) - l) * a l = ∑ J ∈ Icc 1 (L - 1), ∑ j ∈ Icc 1 J, a j := by
  induction L with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ m =>
      rw [sum_Icc_succ_top (by omega)]
      simp only [Nat.cast_add, Nat.cast_one, sub_self, zero_mul, add_zero, Nat.add_sub_cancel]
      rw [sum_Icc_succ_top (by omega) (fun J => ∑ j ∈ Icc 1 J, a j)]
      have he : ∑ l ∈ Icc 1 (m + 1), (((m : ℝ) + 1 + 1) - l) * a l =
          (∑ l ∈ Icc 1 (m + 1), (((m : ℝ) + 1) - l) * a l) + ∑ l ∈ Icc 1 (m + 1), a l := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro l hl
        ring
      rw [he]
      simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using congrArg
        (fun x : ℝ => x + ∑ l ∈ Icc 1 (m + 1), a l) ih

/-- LEAF. Unit U-1530. `Σ_{1 ≤ J ≤ L-1} J ≤ L²/2`; Section 5, proof of Lemma 8. -/
theorem sum_id_le (L : ℕ) : ∑ J ∈ Icc 1 (L - 1), (J : ℝ) ≤ (L : ℝ) ^ 2 / 2 := by
  have hs : ∀ n : ℕ, (∑ J ∈ Icc 1 n, (J : ℝ)) * 2 = (n : ℝ) * (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_Icc_succ_top (by omega)]
      push_cast
      nlinarith
  cases L with
  | zero => simp
  | succ n =>
    have hh := hs n
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- LEAF. Unit U-1530. The off diagonal scale: for `C, D ≥ 0`, `N > 1`, `0 ≤ L ≤ log N/log 2`,
`2 C N/log² N · D L²/2 ≤ C D N/log² 2`; Section 5, the passage from `L²` to `1/log² 2`. -/
theorem offdiag_scale {C D N L : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hN : 1 < N) (hL0 : 0 ≤ L)
    (hL : L ≤ Real.log N / Real.log 2) :
    2 * C * N / Real.log N ^ 2 * (D * L ^ 2 / 2) ≤ C * D * N / Real.log 2 ^ 2 := by
  have hn : 0 < Real.log N := Real.log_pos hN
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : L * Real.log 2 ≤ Real.log N := (le_div_iff₀ h2).mp hL
  have hsq : L ^ 2 * Real.log 2 ^ 2 ≤ Real.log N ^ 2 := by
    nlinarith [mul_le_mul hb hb (by positivity : 0 ≤ L * Real.log 2) hn.le]
  have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ C * D * N by positivity)
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos hn 2) (pow_pos h2 2)]
  nlinarith

/-! ### Assemblies -/

theorem C2_nonneg' : 0 ≤ C2 :=
  tsum_nonneg fun d => div_nonneg (by exact_mod_cast k_nonneg d) (Nat.cast_nonneg _)

/-- ASSEMBLY, CONDITIONAL ON `partial_summation`, `divisor_swap`, `C2_summable`,
`kappa_floor_le` and `sum_id_le`, with the lab's proved `sum_kappaTrue_divisors`:
`Σ_{1 ≤ l ≤ L} (L - l) h(2^l - 1) ≤ C₂ L²/2`; Section 5, proof of Lemma 8. -/
theorem hsum_bound (L : ℕ) :
    ∑ l ∈ Icc 1 L, ((L : ℝ) - l) * (h (2 ^ l - 1) : ℝ) ≤ C2 * (L : ℝ) ^ 2 / 2 := by
  rw [partial_summation]
  have inner : ∀ J : ℕ, ∑ j ∈ Icc 1 J, (h (2 ^ j - 1) : ℝ) ≤ C2 * J := by
    intro J
    have e : ∑ j ∈ Icc 1 J, (h (2 ^ j - 1) : ℝ) = ∑ j ∈ Icc 1 J, ∑ e ∈ j.divisors, kappaTrue e :=
      sum_congr rfl fun j hj => by
        rw [Finset.mem_Icc] at hj
        exact (sum_kappaTrue_divisors j (by omega)).symm
    rw [e, divisor_swap]
    exact kappa_floor_le C2_summable J
  calc ∑ J ∈ Icc 1 (L - 1), ∑ j ∈ Icc 1 J, (h (2 ^ j - 1) : ℝ)
      ≤ ∑ J ∈ Icc 1 (L - 1), C2 * (J : ℝ) := sum_le_sum fun J _ => inner J
    _ = C2 * ∑ J ∈ Icc 1 (L - 1), (J : ℝ) := by rw [mul_sum]
    _ ≤ C2 * ((L : ℝ) ^ 2 / 2) := mul_le_mul_of_nonneg_left (sum_id_le L) C2_nonneg'
    _ = C2 * (L : ℝ) ^ 2 / 2 := by ring

/-- ASSEMBLY, CONDITIONAL ON `offdiag_grouping` and the leaves of `hsum_bound`: the off diagonal
sum `Σ_{μ ≠ ν} h(2^{|μ - ν|} - 1) ≤ C₂ L²`; Section 5, proof of Lemma 8. -/
theorem offdiag_total (L : ℕ) :
    ∑ μ ∈ Icc 1 L, ∑ ν ∈ Icc 1 L,
      (if μ = ν then 0 else (h (2 ^ (max μ ν - min μ ν) - 1) : ℝ)) ≤ C2 * (L : ℝ) ^ 2 := by
  rw [offdiag_grouping (fun l => (h (2 ^ l - 1) : ℝ))]
  have := hsum_bound L
  linarith

/-- ASSEMBLY, CONDITIONAL ON `offdiag_scale` and the leaves of `hsum_bound`: with Chen's factor
`C₀ C₁ ≥ 0` and `L ≤ log N/log 2`,
`2 C₀C₁ N/log² N · Σ_{l ≤ L} (L - l) h(2^l - 1) ≤ C₀ C₁ C₂ N/log² 2`, the main term of
Lemma 8, Section 5. -/
theorem offdiag_main_term {C N : ℝ} (hC : 0 ≤ C) (hN : 1 < N) {L : ℕ}
    (hL : (L : ℝ) ≤ Real.log N / Real.log 2) :
    2 * C * N / Real.log N ^ 2 * ∑ l ∈ Icc 1 L, ((L : ℝ) - l) * (h (2 ^ l - 1) : ℝ) ≤
      C * C2 * N / Real.log 2 ^ 2 := by
  have hpos : 0 ≤ 2 * C * N / Real.log N ^ 2 := by
    have : 0 ≤ N := by linarith
    positivity
  calc _ ≤ 2 * C * N / Real.log N ^ 2 * (C2 * (L : ℝ) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (hsum_bound L) hpos
    _ ≤ C * C2 * N / Real.log 2 ^ 2 :=
        offdiag_scale hC C2_nonneg' hN (Nat.cast_nonneg L) hL

end LeanLab.HeathBrownPuchta.Decomp1530b
