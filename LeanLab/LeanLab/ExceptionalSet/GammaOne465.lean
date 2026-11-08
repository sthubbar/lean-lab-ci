import LeanLab.ExceptionalSet.Totient465
import LeanLab.ExceptionalSet.Gcd465

/-!
The finite divisor error in P0082 page359 display14 and page360 Lemma5.
The progression estimate is explicit. No prime major arc formula is used.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset

/-- P0082 page359 display14, the positive envelope for Gamma1. -/
noncomputable def gammaOne (r : ℕ) (P : ℝ) (m : ℤ) : ℝ :=
  (r : ℝ) / P * ∑ q ∈ (Icc 1 ⌊P⌋₊).filter (fun q => r ∣ q),
    (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ))

/-- P0082 page360, finite Gamma1 average with the two arithmetic
bounds explicit. CONDITIONAL ON the progression estimates. This retains
the finite length P and the exponential error scale E separately. -/
theorem gammaOne_mean_explicit (s : Finset ℕ) (m : ℕ → ℤ) (r : ℕ)
    (P E C L D : ℝ) (N : ℕ) (hr : 1 ≤ r) (hP : 1 ≤ P) (hE : 0 < E)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hφ : ∀ q : ℕ, 1 ≤ q → q ≤ ⌊P⌋₊ → (q : ℝ) / q.totient ≤ L)
    (hτ : ∀ q ∈ Icc 1 ⌊P⌋₊, (q.divisors.card : ℝ) ≤ D * P ^ (1 / 2 : ℝ))
    (hprog : ∀ d : ℕ, 1 ≤ d → d ≤ ⌊P⌋₊ →
      ((s.filter (fun n => (d : ℤ) ∣ m n)).card : ℝ) ≤ C * ((N : ℝ) / d + N / E)) :
    ∑ n ∈ s, gammaOne r P (m n) ≤
      C * N * L ^ 2 * (1 + Real.log P) * (D * P ^ (-(1 / 2 : ℝ)) + 1 / E) := by
  classical
  let Q := ⌊P⌋₊
  let t := (Icc 1 Q).filter (fun q => r ∣ q)
  let H := 1 + Real.log P
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hQ : 1 ≤ Q := Nat.le_floor (by simpa using hP)
  have hQP : (Q : ℝ) ≤ P := Nat.floor_le hP0.le
  have hrR : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hH : 0 ≤ H := by dsimp [H]; have := Real.log_nonneg hP; linarith
  have hcard : (t.card : ℝ) ≤ P / r := by
    have hi : Icc 1 Q = Ioc 0 Q := by ext q; simp only [mem_Icc, mem_Ioc]; omega
    have hc : t.card = Q / r := by dsimp [t]; rw [hi, Nat.Ioc_filter_dvd_card_eq_div]
    rw [hc]
    exact Nat.cast_div_le.trans (div_le_div_of_nonneg_right hQP hrR.le)
  have hinv : ∑ q ∈ t, (q : ℝ)⁻¹ ≤ H / r := by
    refine (sum_inverse_multiples Q r hQ hr).trans ?_
    apply div_le_div_of_nonneg_right _ hrR.le
    have hlog := Real.log_le_log (by exact_mod_cast (show 0 < Q by omega)) hQP
    dsimp [H]
    linarith
  have hmean (q : ℕ) (hq : q ∈ t) :
      (∑ n ∈ s, (Int.gcd (m n) q : ℝ)) / q ≤
        C * N * (D * P ^ (1 / 2 : ℝ) / q + H / E) := by
    have hqI := mem_Icc.mp (mem_filter.mp hq).1
    have hq0 : 0 < q := by omega
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
    have hp : ∀ d ∈ q.divisors,
        ((s.filter (fun n => (d : ℤ) ∣ m n)).card : ℝ) ≤ C * ((N : ℝ) / d + N / E) := by
      intro d hd
      exact hprog d (Nat.pos_of_mem_divisors hd)
        ((Nat.le_of_dvd hq0 (Nat.mem_divisors.mp hd).1).trans hqI.2)
    have hm := gcd_moment_of_progressions s m q hq0 C E N hE hp
    have hs : (∑ d ∈ q.divisors, (d : ℝ)) / q ≤ H := by
      apply (divisor_sum_ratio q hq0).trans
      have hlog := Real.log_le_log hqR ((by exact_mod_cast hqI.2 : (q : ℝ) ≤ Q).trans hQP)
      dsimp [H]
      linarith
    calc
      _ ≤ (C * N * q.divisors.card + C * N / E * ∑ d ∈ q.divisors, (d : ℝ)) / q :=
        div_le_div_of_nonneg_right hm hqR.le
      _ = C * N * ((q.divisors.card : ℝ) / q + ((∑ d ∈ q.divisors, (d : ℝ)) / q) / E) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add (div_le_div_of_nonneg_right (hτ q (mem_filter.mp hq).1) hqR.le)
          (div_le_div_of_nonneg_right hs hE.le)) (by positivity)
  have hterm (q : ℕ) (hq : q ∈ t) :
      ∑ n ∈ s, (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd (m n) q).totient : ℝ)) ≤
        L ^ 2 * (C * N * (D * P ^ (1 / 2 : ℝ) / q + H / E)) := by
    have hqI := mem_Icc.mp (mem_filter.mp hq).1
    calc
      _ ≤ ∑ n ∈ s, L ^ 2 * (Int.gcd (m n) q : ℝ) / q :=
        sum_le_sum (fun n _ => totient_kernel_le Q q hqI.1 hqI.2 (m n) L hL hφ)
      _ = L ^ 2 * ((∑ n ∈ s, (Int.gcd (m n) q : ℝ)) / q) := by rw [← sum_div, ← mul_sum]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmean q hq) (sq_nonneg L)
  have hsumid : (∑ q ∈ t, L ^ 2 * (C * N * (D * P ^ (1 / 2 : ℝ) / q + H / E))) =
      L ^ 2 * ((C * N * D * P ^ (1 / 2 : ℝ)) * (∑ q ∈ t, (q : ℝ)⁻¹) +
        (C * N * H / E) * (t.card : ℝ)) := by
    rw [← mul_sum]
    have hi : (∑ q ∈ t, C * N * (D * P ^ (1 / 2 : ℝ) / q + H / E)) =
        ∑ q ∈ t, ((C * N * D * P ^ (1 / 2 : ℝ)) * (q : ℝ)⁻¹ + C * N * H / E) :=
      sum_congr rfl (fun q _ => by ring)
    rw [hi, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    ring
  have hpowers : P ^ (1 / 2 : ℝ) / P = P ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_sub_one hP0.ne']
    norm_num
  calc
    _ = (r : ℝ) / P * ∑ q ∈ t,
        ∑ n ∈ s, (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd (m n) q).totient : ℝ)) := by
      unfold gammaOne
      rw [← mul_sum, sum_comm]
    _ ≤ (r : ℝ) / P * ∑ q ∈ t,
        L ^ 2 * (C * N * (D * P ^ (1 / 2 : ℝ) / q + H / E)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)
    _ = (r : ℝ) / P * (L ^ 2 * ((C * N * D * P ^ (1 / 2 : ℝ)) * (∑ q ∈ t, (q : ℝ)⁻¹) +
        (C * N * H / E) * (t.card : ℝ))) := by rw [hsumid]
    _ ≤ (r : ℝ) / P * (L ^ 2 * ((C * N * D * P ^ (1 / 2 : ℝ)) * (H / r) +
        (C * N * H / E) * (P / r))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg L)
      exact add_le_add (mul_le_mul_of_nonneg_left hinv (by positivity))
        (mul_le_mul_of_nonneg_left hcard (by positivity))
    _ = C * N * L ^ 2 * H * (D * (P ^ (1 / 2 : ℝ) / P) + 1 / E) := by
      field_simp
      <;> ring
    _ = _ := by rw [hpowers]

end LeanLab.ExceptionalSet.Supply465

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset

/-- P0082 page360 Lemma5, finite divisor averaging with the elementary
logarithmic totient envelope supplied. CONDITIONAL ON the explicit
progression counts. The constant K is uniform in P, r and E. -/
theorem gammaOne_mean_log :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : Finset ℕ) (m : ℕ → ℤ) (r : ℕ) (P E C : ℝ) (N : ℕ),
      1 ≤ r → 1 ≤ P → 0 < E → 0 ≤ C →
      (∀ d : ℕ, 1 ≤ d → d ≤ ⌊P⌋₊ →
        ((s.filter (fun n => (d : ℤ) ∣ m n)).card : ℝ) ≤ C * ((N : ℝ) / d + N / E)) →
      ∑ n ∈ s, gammaOne r P (m n) ≤
        K * C * N * (1 + Real.log P) ^ 3 * (P ^ (-(1 / 2 : ℝ)) + 1 / E) := by
  obtain ⟨A, hA, hφ⟩ := totient_ratio_log
  obtain ⟨D, hD, hτ⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow 2 (by norm_num)
  refine ⟨A ^ 2 * (D + 1), by positivity, fun s m r P E C N hr hP hE hC hp => ?_⟩
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  let H := 1 + Real.log P
  have hH : 0 < H := by dsimp [H]; have := Real.log_nonneg hP; linarith
  have hφP : ∀ q : ℕ, 1 ≤ q → q ≤ ⌊P⌋₊ → (q : ℝ) / q.totient ≤ A * H := by
    intro q hq hqP
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hqR : (q : ℝ) ≤ P := (by exact_mod_cast hqP : (q : ℝ) ≤ ⌊P⌋₊).trans (Nat.floor_le hP0.le)
    refine (hφ q hq).trans ?_
    apply mul_le_mul_of_nonneg_left _ hA.le
    dsimp [H]
    linarith [Real.log_le_log hq0 hqR]
  have hτP : ∀ q ∈ Icc 1 ⌊P⌋₊, (q.divisors.card : ℝ) ≤ D * P ^ (1 / 2 : ℝ) := by
    intro q hq
    obtain ⟨hq1, hqP⟩ := mem_Icc.mp hq
    have hqR : (q : ℝ) ≤ P := (by exact_mod_cast hqP : (q : ℝ) ≤ ⌊P⌋₊).trans (Nat.floor_le hP0.le)
    have ht := hτ q hq1
    norm_num at ht
    exact ht.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hqR (by norm_num)) hD.le)
  have hm := gammaOne_mean_explicit s m r P E C (A * H) D N hr hP hE hC
    (by positivity) hD.le hφP hτP hp
  have hbracket : D * P ^ (-(1 / 2 : ℝ)) + 1 / E ≤
      (D + 1) * (P ^ (-(1 / 2 : ℝ)) + 1 / E) := by
    have hpow : 0 ≤ P ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hP0.le _
    have hprod := mul_nonneg hD.le (show 0 ≤ 1 / E by positivity)
    nlinarith
  calc
    _ ≤ C * N * (A * H) ^ 2 * H * (D * P ^ (-(1 / 2 : ℝ)) + 1 / E) := hm
    _ = (C * N * A ^ 2 * H ^ 3) * (D * P ^ (-(1 / 2 : ℝ)) + 1 / E) := by ring
    _ ≤ (C * N * A ^ 2 * H ^ 3) * ((D + 1) * (P ^ (-(1 / 2 : ℝ)) + 1 / E)) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = _ := by ring

end LeanLab.ExceptionalSet.Supply465
