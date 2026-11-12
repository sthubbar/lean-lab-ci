/-
P0069 Baker Harman Pintz 1997, Section 3, page 12. The divisor moment bound behind
"using (3.1) to bound G(P^g) by 𝓛^B". Coefficients obey display 3.1, `|a_n| ≤ τ(n)^B`,
so the energy G of display 3.3 is at most a harmonic divisor moment
`Σ_{n ≤ c₂F} τ(n)^k / n`, and that moment is at most `(1 + log)^{2^k}` by the elementary
recursion `H_{k+1} ≤ H_k^2` coming from `τ(dm) ≤ τ(d) τ(m)`.
AI wrote the Lean code. ROUTE BURST session 2. Goldbach is open.
-/
import LeanLab.BHP1997.MeanSquareC165

namespace LeanLab.BHP1997.EnergyLogC165
open Finset

/-- P0069 Baker Harman Pintz 1997, Section 3, page 12, input to the bound for G via display
3.1. The divisor function is submultiplicative, `τ(mn) ≤ τ(m) τ(n)`. -/
theorem card_divisors_mul_le (m n : ℕ) :
    (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

/-- The harmonic divisor moment `H_k(N) = Σ_{1 ≤ n ≤ N} τ(n)^k / n`, page 12. -/
noncomputable def harmonicDivisorMoment (k N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ k / (n : ℝ)

theorem harmonicDivisorMoment_nonneg (k N : ℕ) : 0 ≤ harmonicDivisorMoment k N := by
  unfold harmonicDivisorMoment
  exact Finset.sum_nonneg (fun n _ => by positivity)

/-- P0069 Baker Harman Pintz 1997, Section 3, page 12. The base case of the divisor moment,
`H_0(N)` is the harmonic sum, at most `1 + log N`. -/
theorem harmonicDivisorMoment_zero_le (N : ℕ) :
    harmonicDivisorMoment 0 N ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  unfold harmonicDivisorMoment
  simpa [one_div] using h

/-- For `1 ≤ n ≤ N`, the divisors of `n` are the `d ∈ [1, N]` dividing `n`. -/
theorem divisors_eq_filter {n N : ℕ} (hn : n ∈ Icc 1 N) :
    n.divisors = (Icc 1 N).filter (· ∣ n) := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hd, -⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd h1, (Nat.le_of_dvd h1 hd).trans h2⟩, hd⟩
  · rintro ⟨-, hd⟩
    exact ⟨hd, by omega⟩

/-- P0069 Baker Harman Pintz 1997, Section 3, page 12. The moment recursion
`H_{k+1}(N) ≤ H_k(N)^2`: write `τ(n) = Σ_{d ∣ n} 1`, put `n = dm`, and use
`τ(dm)^k ≤ τ(d)^k τ(m)^k`. -/
theorem harmonicDivisorMoment_succ_le (k N : ℕ) :
    harmonicDivisorMoment (k + 1) N ≤ harmonicDivisorMoment k N ^ 2 := by
  classical
  set f : ℕ → ℝ := fun n => ((n.divisors.card : ℕ) : ℝ) ^ k / (n : ℝ) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  -- Step 1: τ(n)^{k+1}/n = Σ_{d ∈ [1,N], d ∣ n} f n.
  have step1 : harmonicDivisorMoment (k + 1) N =
      ∑ n ∈ Icc 1 N, ∑ d ∈ (Icc 1 N).filter (· ∣ n), f n := by
    unfold harmonicDivisorMoment
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.sum_const, nsmul_eq_mul, ← divisors_eq_filter hn, hf]
    simp only
    rw [pow_succ]
    ring
  -- Step 2: exchange the order of summation.
  have step2 : ∑ n ∈ Icc 1 N, ∑ d ∈ (Icc 1 N).filter (· ∣ n), f n =
      ∑ d ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).filter (d ∣ ·), f n := by
    simp only [Finset.sum_filter]
    exact Finset.sum_comm
  -- Step 3: for fixed d, the multiples n = d m with m ∈ [1, N].
  have step3 : ∀ d ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).filter (d ∣ ·), f n ≤
      ∑ m ∈ Icc 1 N, f d * f m := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hinj : Set.InjOn (fun m => d * m) (Icc 1 N : Set ℕ) := by
      intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left hd1 hxy
    have hsub : (Icc 1 N).filter (d ∣ ·) ⊆ (Icc 1 N).image (fun m => d * m) := by
      intro n hn
      obtain ⟨hnI, ⟨m, rfl⟩⟩ := Finset.mem_filter.mp hn
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hnI
      refine Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm; simp at h1
        · exact hm
      · exact (Nat.le_mul_of_pos_left m hd1).trans h2
    calc ∑ n ∈ (Icc 1 N).filter (d ∣ ·), f n
        ≤ ∑ n ∈ (Icc 1 N).image (fun m => d * m), f n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf0 n)
      _ = ∑ m ∈ Icc 1 N, f (d * m) := Finset.sum_image (fun x hx y hy h => hinj hx hy h)
      _ ≤ ∑ m ∈ Icc 1 N, f d * f m := by
          refine Finset.sum_le_sum (fun m _ => ?_)
          rw [hf]
          simp only
          have hc : (((d * m).divisors.card : ℕ) : ℝ) ≤
              ((d.divisors.card : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
            exact_mod_cast card_divisors_mul_le d m
          have hpow : (((d * m).divisors.card : ℕ) : ℝ) ^ k ≤
              ((d.divisors.card : ℕ) : ℝ) ^ k * ((m.divisors.card : ℕ) : ℝ) ^ k := by
            rw [← mul_pow]
            exact pow_le_pow_left₀ (by positivity) hc k
          rw [Nat.cast_mul, div_mul_div_comm]
          exact div_le_div_of_nonneg_right hpow (by positivity)
  calc harmonicDivisorMoment (k + 1) N
      = ∑ d ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).filter (d ∣ ·), f n := by rw [step1, step2]
    _ ≤ ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 N, f d * f m := Finset.sum_le_sum step3
    _ = harmonicDivisorMoment k N ^ 2 := by
        rw [sq, harmonicDivisorMoment, Finset.sum_mul_sum]

/-- P0069 Baker Harman Pintz 1997, Section 3, page 12. Iterating the recursion,
`H_k(N) ≤ (1 + log N)^{2^k}`. -/
theorem harmonicDivisorMoment_le (k N : ℕ) :
    harmonicDivisorMoment k N ≤ (1 + Real.log N) ^ (2 ^ k) := by
  induction k with
  | zero => simpa using harmonicDivisorMoment_zero_le N
  | succ k ih =>
    calc harmonicDivisorMoment (k + 1) N ≤ harmonicDivisorMoment k N ^ 2 :=
          harmonicDivisorMoment_succ_le k N
      _ ≤ ((1 + Real.log N) ^ (2 ^ k)) ^ 2 :=
          pow_le_pow_left₀ (harmonicDivisorMoment_nonneg k N) ih 2
      _ = (1 + Real.log N) ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]

/-- P0069 Baker Harman Pintz 1997, Section 3, page 12, display 3.1 applied to G of display 3.3.
For `n ≥ 1` the coefficient bound `|a_n| ≤ τ(n)^B` gives `|a_n|^2 ≤ τ(n)^k` with `k = ⌈2B⌉`. -/
theorem norm_sq_le_divisor_pow (a : ℕ → ℂ) (B : ℝ) (ha : Thm4.CoeffBound a B)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖a n‖ ^ 2 ≤ ((n.divisors.card : ℕ) : ℝ) ^ (⌈2 * B⌉₊) := by
  have hτ : (1 : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := by
    have : 0 < n.divisors.card := Finset.card_pos.mpr ⟨1, by simp; omega⟩
    exact_mod_cast this
  have hτ0 : (0 : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := by positivity
  calc ‖a n‖ ^ 2 ≤ ((((n.divisors.card : ℕ) : ℝ)) ^ B) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (ha n) 2
    _ = ((n.divisors.card : ℕ) : ℝ) ^ (2 * B) := by
        rw [mul_comm, Real.rpow_mul hτ0, Real.rpow_two]
    _ ≤ ((n.divisors.card : ℕ) : ℝ) ^ ((⌈2 * B⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hτ (Nat.le_ceil _)
    _ = ((n.divisors.card : ℕ) : ℝ) ^ (⌈2 * B⌉₊) := Real.rpow_natCast _ _

/-- P0069 Baker Harman Pintz 1997, Section 3, page 12. The energy G of display 3.3 is at most
the harmonic divisor moment up to `⌊c₂ F⌋`. -/
theorem energy_le_moment (a : ℕ → ℂ) (B c1 c2 F : ℝ) (hc1 : 0 < c1) (hF : 0 < F)
    (ha : Thm4.CoeffBound a B) :
    MeanSquareC165.energy a c1 c2 F ≤ harmonicDivisorMoment (⌈2 * B⌉₊) ⌊c2 * F⌋₊ := by
  classical
  unfold MeanSquareC165.energy harmonicDivisorMoment
  have hsub : (Finset.range (⌊c2 * F⌋₊ + 1)).filter
      (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F) ⊆ Icc 1 ⌊c2 * F⌋₊ := by
    intro n hn
    obtain ⟨hr, h1, _⟩ := Finset.mem_filter.mp hn
    have hpos : (0 : ℝ) < n := lt_trans (mul_pos hc1 hF) h1
    have : 1 ≤ n := by exact_mod_cast Nat.one_le_cast.mpr (by exact_mod_cast hpos)
    exact Finset.mem_Icc.mpr ⟨this, Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)⟩
  calc ∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
        (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F), ‖a n‖ ^ 2 / (n : ℝ)
      ≤ ∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
        (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F),
          ((n.divisors.card : ℕ) : ℝ) ^ (⌈2 * B⌉₊) / (n : ℝ) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hn1 := (Finset.mem_Icc.mp (hsub hn)).1
        exact div_le_div_of_nonneg_right (norm_sq_le_divisor_pow a B ha hn1) (by positivity)
    _ ≤ ∑ n ∈ Icc 1 ⌊c2 * F⌋₊, ((n.divisors.card : ℕ) : ℝ) ^ (⌈2 * B⌉₊) / (n : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)

/-- P0069 Baker Harman Pintz 1997, Section 3, page 12. For `F ≥ 2`, `1 + log ⌊c₂ F⌋` is
at most a constant multiple of `log F`, the constant depending only on `c₂`. -/
theorem one_add_log_floor_le (c2 F : ℝ) (hF : 2 ≤ F) :
    1 + Real.log (⌊c2 * F⌋₊ : ℝ) ≤
      ((1 + |Real.log c2|) / Real.log 2 + 1) * Real.log F := by
  have hF0 : 0 < F := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogF2 : Real.log 2 ≤ Real.log F := Real.log_le_log (by norm_num) hF
  have hlogF : 0 < Real.log F := lt_of_lt_of_le hlog2 hlogF2
  have hM : Real.log (⌊c2 * F⌋₊ : ℝ) ≤ |Real.log c2| + Real.log F := by
    rcases Nat.eq_zero_or_pos ⌊c2 * F⌋₊ with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; positivity
    · have hpos' : (0 : ℝ) < (⌊c2 * F⌋₊ : ℝ) := by exact_mod_cast hpos
      have hc2F : (⌊c2 * F⌋₊ : ℝ) ≤ c2 * F := Nat.floor_le (by
        by_contra h
        push_neg at h
        have : ⌊c2 * F⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        omega)
      have hc2 : 0 < c2 := by
        by_contra h
        push_neg at h
        have : c2 * F ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hF0.le
        linarith
      calc Real.log (⌊c2 * F⌋₊ : ℝ) ≤ Real.log (c2 * F) := Real.log_le_log hpos' hc2F
        _ = Real.log c2 + Real.log F := Real.log_mul hc2.ne' hF0.ne'
        _ ≤ |Real.log c2| + Real.log F := by linarith [le_abs_self (Real.log c2)]
  have hA : 1 + |Real.log c2| ≤ (1 + |Real.log c2|) / Real.log 2 * Real.log F := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlogF2 (by positivity)
  nlinarith

end LeanLab.BHP1997.EnergyLogC165
