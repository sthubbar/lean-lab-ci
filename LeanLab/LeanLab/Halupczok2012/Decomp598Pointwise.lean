import LeanLab.Halupczok2012.U1496PP

/-!
Elementary pointwise estimates for the second display on Halupczok page 340.
https://doi.org/10.5802/jtnb.839
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp598Pointwise

open Finset
open scoped Classical

/-- The squarefree reciprocal Euler product is bounded by the harmonic sum.
This supplies an elementary logarithmic bound for the page 340 singular series. -/
theorem prime_reciprocal_product_le {r : ℕ} (hr : r ≠ 0) :
    ∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹) ≤ 1 + Real.log r := by
  have he : ∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹) =
      ∑ d ∈ r.divisors.filter Squarefree, (d : ℝ)⁻¹ := by
    rw [prod_one_add, Nat.sum_divisors_filter_squarefree hr]
    simp only [Nat.factors_eq, List.toFinset_coe, Nat.toFinset_factors]
    apply sum_congr rfl
    intro t _
    simp only [Finset.prod_inv_distrib, Nat.cast_prod, Finset.prod_val, Function.id_def]
  rw [he]
  calc
    _ ≤ ∑ d ∈ Icc 1 r, (d : ℝ)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        have hd' := Nat.mem_divisors.mp (mem_filter.mp hd).1
        exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd'.1 (Nat.pos_of_ne_zero hr),
          Nat.le_of_dvd (Nat.pos_of_ne_zero hr) hd'.1⟩
      · intro d _ _
        positivity
    _ ≤ _ := sum_inv_Icc_le r

/-- Each odd prime singular factor is at most a cube of a reciprocal factor.
This elementary loss replaces the sharper pointwise estimate on page 340. -/
theorem singular_factor_le_cube {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    0 ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) ∧
      ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ (1 + (p : ℝ)⁻¹) ^ 3 := by
  have h3 : (3 : ℝ) ≤ p := by
    exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
  have hp0 : (0 : ℝ) < p := by linarith
  have hp20 : (0 : ℝ) < p - 2 := by linarith
  refine ⟨div_nonneg (by linarith) hp20.le, ?_⟩
  rw [div_le_iff₀ hp20]
  have hn : 0 ≤ 2 * ((p : ℝ) - 3) ^ 3 + 15 * ((p : ℝ) - 3) ^ 2 +
      31 * ((p : ℝ) - 3) + 10 := by positivity
  have hmul : (p : ℝ) - 1 ≤ ((p : ℝ) + 1) ^ 3 / (p : ℝ) ^ 3 * ((p : ℝ) - 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < (p : ℝ) ^ 3)]
    nlinarith
  convert hmul using 1 <;> field_simp <;> ring

/-- A logarithmic bound for the binary singular series on page 340.
The cube loss suffices because display 2.4 permits every logarithmic saving. -/
theorem singular_series_log_bound {r : ℕ} (hr : r ≠ 0) :
    |S r| ≤ 2 * (1 + Real.log r) ^ 3 := by
  let F := r.primeFactors.filter (· ≠ 2)
  have hf0 : ∀ p ∈ F, 0 ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    intro p hp
    exact (singular_factor_le_cube (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)
      (mem_filter.mp hp).2).1
  have hprod : ∏ p ∈ F, (((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤
      (1 + Real.log r) ^ 3 := by
    calc
      _ ≤ ∏ p ∈ F, (1 + (p : ℝ)⁻¹) ^ 3 :=
        prod_le_prod₀ hf0 fun p hp =>
          (singular_factor_le_cube (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)
            (mem_filter.mp hp).2).2
      _ = (∏ p ∈ F, (1 + (p : ℝ)⁻¹)) ^ 3 := prod_pow _ _ _
      _ ≤ (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) ^ 3 := by
        apply pow_le_pow_left₀ (prod_nonneg (fun p _ => by positivity))
        exact prod_le_prod_of_subset_of_one_le₀ (filter_subset _ _)
          (fun p _ => by positivity) (fun p _ _ => le_add_of_nonneg_right (by positivity))
      _ ≤ _ := by
        gcongr
        exact prime_reciprocal_product_le hr
  obtain ⟨hC0, hC1⟩ := twinC_mem
  unfold S
  split_ifs
  · rw [abs_of_nonneg (by exact mul_nonneg (by positivity) (prod_nonneg hf0))]
    change 2 * twinC * (∏ p ∈ F, (((p : ℝ) - 1) / ((p : ℝ) - 2))) ≤ _
    exact mul_le_mul (by linarith) hprod (prod_nonneg hf0) (by norm_num)
  · rw [abs_zero]
    have := one_add_log_nonneg r
    positivity

/-- The reciprocal totient sum grows at most logarithmically.
This bounds the modulus sum in the page 340 pointwise step. -/
theorem reciprocal_totient_sum (N : ℕ) :
    ∑ q ∈ Icc 1 N, 1 / (q.totient : ℝ) ≤ Kc (1 / 4) * (1 + Real.log N) := by
  calc
    _ ≤ ∑ q ∈ Icc 1 N, Hs (1 / 4) q / (q.totient : ℝ) := by
      apply sum_le_sum
      intro q _
      apply div_le_div_of_nonneg_right _ (by positivity)
      unfold Hs
      apply one_le_prod₀
      intro p hp
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : 0 < (p : ℝ) - 1 := by linarith
      exact le_add_of_nonneg_right (by positivity)
    _ ≤ _ := sum_Hs_div_totient_le (by norm_num) (by norm_num) N

/-- A binary prime sum is nonnegative, as used on Halupczok page 340. -/
theorem binSumAP_nonneg (X2 Y : ℝ) (q : ℕ) (a : ℤ) (m : ℕ) :
    0 ≤ binSumAP X2 Y q a m := by
  unfold binSumAP
  apply sum_nonneg
  intro p hp
  obtain ⟨_, hpP, hmP, _⟩ := mem_filter.mp hp
  exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hpP.one_le))
    (Real.log_nonneg (by exact_mod_cast hmP.one_le))

/-- Trivial counting in one residue class bounds the binary prime sum.
This elementary bound is used for the page 340 pointwise step. -/
theorem binSumAP_le (X2 Y : ℝ) (q : ℕ) (a : ℤ) (m : ℕ)
    (hY : 0 ≤ Y) (hq : 0 < q) (hm : 1 ≤ m) :
    binSumAP X2 Y q a m ≤ (Y / q + 1) * Real.log m ^ 2 := by
  let P := (range (m + 1)).filter (fun p => p.Prime ∧ (m - p).Prime ∧
    X2 < p ∧ (p : ℝ) ≤ X2 + Y ∧ (p : ℤ) ≡ a [ZMOD q])
  have hcard : (P.card : ℝ) ≤ Y / q + 1 := by
    apply card_cong_le hq hY
    · intro p hp
      exact ⟨(mem_filter.mp hp).2.2.2.1, (mem_filter.mp hp).2.2.2.2.1⟩
    · intro p hp r hr
      exact ((mem_filter.mp hp).2.2.2.2.2).trans ((mem_filter.mp hr).2.2.2.2.2).symm
  calc
    _ ≤ ∑ _p ∈ P, Real.log m ^ 2 := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpm, hpP, hmP, _⟩ := mem_filter.mp hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
      have hm0 : (0 : ℝ) < ((m - p : ℕ) : ℝ) := by exact_mod_cast hmP.pos
      have hpm' : (p : ℝ) ≤ m := by exact_mod_cast (show p ≤ m by simpa using mem_range.mp hpm)
      have hmp' : ((m - p : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m p
      have hpL := Real.log_le_log hp0 hpm'
      have hmL := Real.log_le_log hm0 hmp'
      have hpL0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpP.one_le)
      have hmL0 : 0 ≤ Real.log ((m - p : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hmP.one_le)
      simpa [sq] using mul_le_mul hpL hmL hmL0 (hpL0.trans hpL)
    _ = (P.card : ℝ) * Real.log m ^ 2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)

/-- Sum the trivial residue bounds over the moduli on page 340. -/
theorem binary_modulus_sum_le (X2 Y : ℝ) (N m : ℕ) (a : ℤ)
    (hY : 0 ≤ Y) (hm : 1 ≤ m) :
    (∑ q ∈ Icc 1 N, binSumAP X2 Y q a m) ≤
      (Y * (1 + Real.log N) + N) * Real.log m ^ 2 := by
  calc
    _ ≤ ∑ q ∈ Icc 1 N, (Y / q + 1) * Real.log m ^ 2 :=
      sum_le_sum fun q hq => binSumAP_le X2 Y q a m hY (mem_Icc.mp hq).1 hm
    _ = (Y * (∑ q ∈ Icc 1 N, (q : ℝ)⁻¹) + N) * Real.log m ^ 2 := by
      simp_rw [← sum_mul, sum_add_distrib, div_eq_mul_inv, ← mul_sum]
      simp
    _ ≤ _ := by
      gcongr
      exact sum_inv_Icc_le N

/-- Sum the logarithmic singular series bound over the moduli on page 340. -/
theorem singular_modulus_sum_le (N m : ℕ) (a : ℤ) (hN : 1 ≤ N) (hm : 1 ≤ m) :
    (∑ q ∈ Icc 1 N, |Sqa m q a|) ≤
      2 * (1 + Real.log ((m * N : ℕ) : ℝ)) ^ 3 *
        (Kc (1 / 4) * (1 + Real.log N)) := by
  have hlog0 := one_add_log_nonneg (m * N)
  have heach (q : ℕ) (hq : q ∈ Icc 1 N) : |Sqa m q a| ≤
      2 * (1 + Real.log ((m * N : ℕ) : ℝ)) ^ 3 * (1 / (q.totient : ℝ)) := by
    have hq0 : 0 < q := (mem_Icc.mp hq).1
    have hmq0 : 0 < m * q := Nat.mul_pos hm hq0
    have hmq : (m * q : ℕ) ≤ m * N := Nat.mul_le_mul_left m (mem_Icc.mp hq).2
    have hs := singular_series_log_bound (Nat.ne_of_gt hmq0)
    have hlog : Real.log ((m * q : ℕ) : ℝ) ≤ Real.log ((m * N : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hmq0) (by exact_mod_cast hmq)
    have hbound : |S (m * q)| ≤ 2 * (1 + Real.log ((m * N : ℕ) : ℝ)) ^ 3 := by
      apply hs.trans
      gcongr
    unfold Sqa
    split_ifs
    · rw [abs_div, show |(q.totient : ℝ)| = q.totient from
        abs_of_nonneg (Nat.cast_nonneg q.totient), div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right hbound (by positivity)
    · rw [abs_zero]
      positivity
  calc
    _ ≤ ∑ q ∈ Icc 1 N,
        2 * (1 + Real.log ((m * N : ℕ) : ℝ)) ^ 3 * (1 / (q.totient : ℝ)) :=
      sum_le_sum heach
    _ = 2 * (1 + Real.log ((m * N : ℕ) : ℝ)) ^ 3 *
        ∑ q ∈ Icc 1 N, (1 / (q.totient : ℝ)) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_totient_sum N) (by positivity)

/-- An explicit elementary pointwise estimate for the error sum on page 340.
The logarithmic losses are retained rather than invoking a sieve estimate. -/
theorem inner_error_explicit (X2 Y : ℝ) (N m : ℕ) (a : ℤ)
    (hY : 0 ≤ Y) (hN : 1 ≤ N) (hm : 1 ≤ m) :
    (∑ q ∈ Icc 1 N, |binSumAP X2 Y q a m - Sqa m q a * Y|) ≤
      (Y * (1 + Real.log N) + N) * Real.log m ^ 2 +
      Y * (2 * (1 + Real.log ((m * N : ℕ) : ℝ)) ^ 3 *
        (Kc (1 / 4) * (1 + Real.log N))) := by
  calc
    _ ≤ ∑ q ∈ Icc 1 N, (binSumAP X2 Y q a m + Y * |Sqa m q a|) := by
      apply sum_le_sum
      intro q _
      have hh := abs_sub (binSumAP X2 Y q a m) (Sqa m q a * Y)
      rw [abs_of_nonneg (binSumAP_nonneg X2 Y q a m), abs_mul, abs_of_nonneg hY] at hh
      simpa [mul_comm] using hh
    _ = (∑ q ∈ Icc 1 N, binSumAP X2 Y q a m) + Y * ∑ q ∈ Icc 1 N, |Sqa m q a| := by
      rw [sum_add_distrib, mul_sum]
    _ ≤ _ := add_le_add (binary_modulus_sum_le X2 Y N m a hY hm)
      (mul_le_mul_of_nonneg_left (singular_modulus_sum_le N m a hN hm) hY)

/-- Compare a polynomially bounded logarithm with log Y on page 340. -/
theorem polynomial_log_bound {T D Y : ℝ} (d : ℕ) (hD : 0 < D)
    (hY : Real.exp 1 ≤ Y) (hT : 0 < T) (hTD : T ≤ D * Y ^ d) :
    1 + Real.log T ≤ (|Real.log D| + (d : ℝ) + 1) * Real.log Y := by
  have hY0 : 0 < Y := (Real.exp_pos 1).trans_le hY
  have hL : 1 ≤ Real.log Y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hY
  have hh := Real.log_le_log hT hTD
  rw [Real.log_mul hD.ne' (by positivity), Real.log_pow] at hh
  have ha := le_abs_self (Real.log D)
  have hb := le_mul_of_one_le_right (abs_nonneg (Real.log D)) hL
  nlinarith

/-- The second page 340 Cauchy Schwarz step with an elementary log fourth power loss.
All constants are uniform in the point k and the modulus cutoff. -/
theorem inner_error_polylog (K c : ℝ) (hK : 0 < K) (hc : 0 < c) :
    ∃ D : ℝ, 0 < D ∧ ∀ X1 X2 Y : ℝ, ∀ N : ℕ, ∀ a : ℤ,
      Real.exp 1 ≤ Y → Y ≤ X1 → X1 ≤ K * Y ^ 2 →
      1 ≤ N → (N : ℝ) ≤ c * Y →
      ∀ k ∈ kRange X1 Y,
        (∑ q ∈ Icc 1 N, |binSumAP X2 Y q a (2 * k) - Sqa (2 * k) q a * Y|) ≤
          D * Y * Real.log Y ^ 4 := by
  let LN := |Real.log c| + 2
  let LM := |Real.log (4 * K)| + 3
  let LP := |Real.log (4 * K * c)| + 4
  let D := (LN + c) * LM ^ 2 + 2 * LP ^ 3 * Kc (1 / 4) * LN
  have hLN : 0 < LN := by dsimp [LN]; positivity
  have hLM : 0 < LM := by dsimp [LM]; positivity
  have hLP : 0 < LP := by dsimp [LP]; positivity
  have hKC := Kc_pos (1 / 4)
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro X1 X2 Y N a hY hYX hX hN hNY k hk
  have hY0 : 0 < Y := (Real.exp_pos 1).trans_le hY
  have hL : 1 ≤ Real.log Y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hY
  have hY1 : 1 ≤ Y := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hY
  have hkR := (mem_filter.mp hk).2
  have hmk : (2 * k : ℝ) ≤ 4 * K * Y ^ 2 := by
    have : (k : ℝ) ≤ 2 * X1 := by linarith [hkR.2]
    nlinarith
  have hmk0 : (0 : ℝ) < 2 * k := by linarith [hkR.1]
  have hmk1 : 1 ≤ 2 * k := by
    have hk0 : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith [hkR.1])
    omega
  have hNN : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 1 + Real.log N ≤ LN * Real.log Y := by
    have hh := polynomial_log_bound 1 hc hY hNN (by simpa using hNY)
    norm_num at hh
    dsimp [LN]
    linarith
  have hlogM : 1 + Real.log ((2 * k : ℕ) : ℝ) ≤ LM * Real.log Y := by
    have hh := polynomial_log_bound (T := ((2 * k : ℕ) : ℝ)) 2
      (by positivity : 0 < 4 * K) hY
      (by exact_mod_cast hmk0) (by exact_mod_cast hmk)
    norm_num at hh
    dsimp [LM]
    push_cast
    linarith
  have hlogP : 1 + Real.log (((2 * k) * N : ℕ) : ℝ) ≤ LP * Real.log Y := by
    have hprod : (((2 * k) * N : ℕ) : ℝ) ≤ (4 * K * c) * Y ^ 3 := by
      push_cast
      have hh := mul_le_mul hmk hNY (by positivity) (by positivity)
      nlinarith
    have hh := polynomial_log_bound (T := (((2 * k) * N : ℕ) : ℝ)) 3
      (by positivity : 0 < 4 * K * c) hY (by positivity) hprod
    norm_num at hh
    dsimp [LP]
    push_cast
    linarith
  have hlogN0 := one_add_log_nonneg N
  have hlogP0 := one_add_log_nonneg ((2 * k) * N)
  have hlogM0 : 0 ≤ Real.log ((2 * k : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hmk1)
  have hthree : Real.log Y ^ 3 ≤ Real.log Y ^ 4 := pow_le_pow_right₀ hL (by omega)
  have hbin : (Y * (1 + Real.log N) + N) * Real.log ((2 * k : ℕ) : ℝ) ^ 2 ≤
      (LN + c) * LM ^ 2 * Y * Real.log Y ^ 4 := by
    calc
      _ ≤ (Y * (LN * Real.log Y) + c * Y) * (LM * Real.log Y) ^ 2 := by
        gcongr
        linarith
      _ ≤ ((LN + c) * Y * Real.log Y) * (LM * Real.log Y) ^ 2 := by
        gcongr
        nlinarith
      _ = (LN + c) * LM ^ 2 * Y * Real.log Y ^ 3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hthree (by positivity)
  have hsing : Y * (2 * (1 + Real.log (((2 * k) * N : ℕ) : ℝ)) ^ 3 *
      (Kc (1 / 4) * (1 + Real.log N))) ≤
      (2 * LP ^ 3 * Kc (1 / 4) * LN) * Y * Real.log Y ^ 4 := by
    calc
      _ ≤ Y * (2 * (LP * Real.log Y) ^ 3 * (Kc (1 / 4) * (LN * Real.log Y))) := by
        gcongr
      _ = _ := by ring
  have he := inner_error_explicit X2 Y N (2 * k) a hY0.le hN hmk1
  apply he.trans
  dsimp [D]
  nlinarith

/-- The short interval size needed in the page 339 major arc adaptation
follows from Theorem 2.2, with epsilon2 equal to epsilon plus one fifteenth. -/
theorem adapted_short_interval_size {c ε X1 X2 Y : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hX1 : 0 ≤ X1) (hX2 : 0 ≤ X2)
    (hupper : X2 ≤ 2 * X1) (hlower : c * X1 ^ (2 / 3 + ε) ≤ Y) :
    0 < ε + 1 / 15 ∧
      (c / (2 : ℝ) ^ (2 / 3 + ε)) * X2 ^ (3 / 5 + (ε + 1 / 15)) ≤ Y := by
  refine ⟨by linarith, ?_⟩
  have he : (3 / 5 + (ε + 1 / 15) : ℝ) = 2 / 3 + ε := by ring
  rw [he]
  have hh := Real.rpow_le_rpow hX2 hupper (by linarith : (0 : ℝ) ≤ 2 / 3 + ε)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hX1] at hh
  have hp : 0 < (2 : ℝ) ^ (2 / 3 + ε) := Real.rpow_pos_of_pos (by norm_num) _
  calc
    _ ≤ (c / (2 : ℝ) ^ (2 / 3 + ε)) *
        ((2 : ℝ) ^ (2 / 3 + ε) * X1 ^ (2 / 3 + ε)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = c * X1 ^ (2 / 3 + ε) := by field_simp
    _ ≤ Y := hlower

/-- The p3 window in the adaptation sketch on page 339 has length three Y.
Its left endpoint is nonnegative under the exact Theorem 2.2 upper bound. -/
theorem third_prime_window {X1 X2 Y : ℝ} {k p2 : ℕ}
    (hk : k ∈ kRange X1 Y) (hp : X2 < p2 ∧ (p2 : ℝ) ≤ X2 + Y)
    (hupper : X2 ≤ 2 * X1 - Y) :
    0 ≤ 2 * X1 - X2 - Y ∧
      2 * X1 - X2 - Y < ((2 * k - p2 : ℕ) : ℝ) ∧
      ((2 * k - p2 : ℕ) : ℝ) ≤ (2 * X1 - X2 - Y) + 3 * Y := by
  have hkR := mem_kRange' hk
  have hpk : p2 ≤ 2 * k := by
    exact_mod_cast (show (p2 : ℝ) ≤ 2 * k by linarith [hp.2, hkR.1])
  rw [Nat.cast_sub hpk]
  push_cast
  constructor
  · linarith
  constructor <;> linarith [hkR.1, hkR.2, hp.1, hp.2]

end LeanLab.Halupczok2012.Decomp598Pointwise
