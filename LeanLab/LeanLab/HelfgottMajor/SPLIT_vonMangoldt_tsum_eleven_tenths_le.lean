import Mathlib

/-!
# Split of `vonMangoldt_tsum_eleven_tenths_le` (`HelfgottMajor/SPLIT_border_logDeriv_le_of_one_le_re`)

The target, a leaf of the burst-20261124 split of `border_logDeriv_le_of_one_le_re`, is the
numerical bound `∑ Λ(n) n^{-11/10} ≤ 11.7`, that is `-ζ'/ζ(11/10) ≤ 11.7`; the true value is
`9.4410...`.  The statement is restated verbatim below and proved from one LEAF and
two proved lemmas:

* the explicit Chebyshev bound `ψ(x) ≤ 1.03883 x` for `x > 0`, Rosser and Schoenfeld,
  Approximate formulas for some functions of prime numbers, Illinois J. Math. 6, 1962,
  Theorem 12;
* Abel summation: if the partial sums of `a ≥ 0` up to `N` are at most `c N`, then
  `∑ a(n) n^{-σ} ≤ c ζ(σ)` for `σ > 1`, since
  `∑_{n ≤ N} a(n) n^{-σ} = A(N) N^{-σ} + ∑_{n < N} A(n) (n^{-σ} - (n+1)^{-σ})`;
* `ζ(11/10) ≤ 11`, from the integral comparison `ζ(σ) ≤ 1 + 1/(σ - 1)`; the true value is
  `10.5844...`.

Together `1.03883 · 11 = 11.427 ≤ 11.7`.

AI wrote this Lean code.  Binary Goldbach is OPEN.
-/

namespace LeanLab.HelfgottMajor.SplitVonMangoldtTsum

open Real Finset

/-- LEAF: Rosser and Schoenfeld 1962, Theorem 12, display 3.35 page 71, HARD, the explicit
Chebyshev bound `ψ(x) < 1.03883 x` for every `x > 0`; a cited theorem resting on the explicit
zeros of `ζ` and an explicit zero free region. -/
theorem psi_le_rosser_schoenfeld (x : ℝ) (hx : 0 < x) : Chebyshev.psi x ≤ 1.03883 * x := by
  sorry

/-- Abel summation step, proved, Rosser and Schoenfeld 1962 section 3 style: partial sums of a
nonnegative sequence at most `c N` give `∑ a(n) n^{-σ} ≤ c ∑ n^{-σ}` for `σ > 1`.  The finite
form is the induction `S_N + (c N - A(N)) N^{-σ} ≤ c Z_N` with `Z_N = ∑_{1 ≤ n ≤ N} n^{-σ}`, using
that `n^{-σ}` decreases.  MEDIUM. -/
theorem tsum_div_rpow_le_of_partial_sums_le (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (c σ : ℝ)
    (hσ : 1 < σ) (hA : ∀ N : ℕ, ∑ n ∈ Ioc 0 N, a n ≤ c * N) :
    ∑' n : ℕ, a n / (n : ℝ) ^ σ ≤ c * ∑' n : ℕ, 1 / (n : ℝ) ^ σ := by
  set b : ℕ → ℝ := fun i => a (i + 1) with hb
  set u : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 1) ^ σ with hu
  have hIoc : ∀ N : ℕ, ∑ n ∈ Ioc 0 N, a n = ∑ i ∈ range N, b i := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ih, Finset.sum_range_succ]
  have hB : ∀ N : ℕ, ∑ i ∈ range N, b i ≤ c * N := fun N => (hIoc N) ▸ hA N
  have hc : 0 ≤ c := by
    have h1 := hB 1
    simp only [Finset.sum_range_one, hb, Nat.cast_one, mul_one] at h1
    linarith [ha 1]
  have hupos : ∀ i, 0 < u i := fun i => by simp only [hu]; positivity
  have hudec : ∀ i, u (i + 1) ≤ u i := by
    intro i
    simp only [hu]
    apply one_div_le_one_div_of_le (by positivity)
    exact rpow_le_rpow (by positivity) (by push_cast; linarith) (by linarith)
  -- Abel summation invariant
  have hinv : ∀ N : ℕ, ∑ i ∈ range N, b i * u i + (c * N - ∑ i ∈ range N, b i) * u N
      ≤ c * ∑ i ∈ range N, u i := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      simp only [Finset.sum_range_succ, Nat.cast_succ]
      have hnn : 0 ≤ c * ((N : ℝ) + 1) - (∑ i ∈ range N, b i + b N) := by
        have := hB (N + 1); simp only [Finset.sum_range_succ, Nat.cast_succ] at this; linarith
      have := mul_le_mul_of_nonneg_left (hudec N) hnn
      nlinarith
  have hfin : ∀ N : ℕ, ∑ i ∈ range N, b i * u i ≤ c * ∑ i ∈ range N, u i := by
    intro N
    have h1 := hinv N
    have h2 : 0 ≤ (c * N - ∑ i ∈ range N, b i) * u N :=
      mul_nonneg (by linarith [hB N]) (hupos N).le
    linarith
  have husum : Summable u := by
    have := (Real.summable_one_div_nat_rpow (p := σ)).mpr hσ
    have := (summable_nat_add_iff 1).mpr this
    simpa [hu] using this
  have hUle : ∀ N, ∑ i ∈ range N, u i ≤ ∑' i, u i := fun N =>
    husum.sum_le_tsum _ (fun i _ => (hupos i).le)
  have hbunn : ∀ i, 0 ≤ b i * u i := fun i => mul_nonneg (ha _) (hupos i).le
  have hbound : ∀ N, ∑ i ∈ range N, b i * u i ≤ c * ∑' i, u i := fun N =>
    (hfin N).trans (mul_le_mul_of_nonneg_left (hUle N) hc)
  have hbsum : Summable (fun i => b i * u i) := summable_of_sum_range_le hbunn hbound
  have htb : ∑' i, b i * u i ≤ c * ∑' i, u i := Real.tsum_le_of_sum_range_le hbunn hbound
  have hL : ∑' n : ℕ, a n / (n : ℝ) ^ σ = ∑' i, b i * u i := by
    have hs : Summable (fun n : ℕ => a n / (n : ℝ) ^ σ) := by
      refine (summable_nat_add_iff 1).mp ?_
      refine hbsum.congr (fun i => ?_)
      simp only [hb, hu]; push_cast; ring
    rw [hs.tsum_eq_zero_add]
    simp only [CharP.cast_eq_zero]
    rw [zero_rpow (by linarith), div_zero, zero_add]
    congr 1; ext i; simp only [hb, hu]; push_cast; ring
  have hR : ∑' n : ℕ, 1 / (n : ℝ) ^ σ = ∑' i, u i := by
    have hs := (Real.summable_one_div_nat_rpow (p := σ)).mpr hσ
    rw [hs.tsum_eq_zero_add]
    simp only [CharP.cast_eq_zero]
    rw [zero_rpow (by linarith), div_zero, zero_add]
    congr 1; ext i; simp only [hu]; push_cast; ring
  rw [hL, hR]; exact htb

open Set MeasureTheory in
/-- `ζ(11/10) ≤ 11`, proved, from the integral comparison
`∑_{n ≥ 1} n^{-σ} ≤ 1 + ∫_1^∞ x^{-σ} dx = σ / (σ - 1)` at `σ = 11/10`, Mathlib `AntitoneOn.abs_tsum_sub_sum_range_le_integral`. -/
theorem tsum_one_div_rpow_eleven_tenths_le :
    ∑' n : ℕ, 1 / (n : ℝ) ^ (11 / 10 : ℝ) ≤ 11 := by
  set f : ℝ → ℝ := fun x => 1 / x ^ (11 / 10 : ℝ) with hf
  have hEq : EqOn f (fun x : ℝ => x ^ (-(11 / 10) : ℝ)) (Ioi ((2 : ℕ) - 1 : ℝ)) := by
    intro x hx
    simp only [hf, rpow_neg (le_of_lt (lt_trans one_pos (by norm_num at hx ⊢; linarith))),
      one_div]
  have hpos : (0 : ℝ) < ((2 : ℕ) - 1 : ℝ) := by norm_num
  have hint : IntegrableOn f (Ioi ((2 : ℕ) - 1 : ℝ)) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := -(11/10)) (by norm_num) hpos).congr_fun ?_
      measurableSet_Ioi
    exact fun x hx => (hEq hx).symm
  have hanti : AntitoneOn f (Ici ((2 : ℕ) - 1 : ℝ)) := by
    intro x hx y hy hxy
    have hx1 : (1 : ℝ) ≤ x := by norm_num at hx; linarith
    have hx0 : 0 < x := by linarith
    simp only [hf]
    apply one_div_le_one_div_of_le (rpow_pos_of_pos hx0 _)
    exact rpow_le_rpow hx0.le hxy (by norm_num)
  have hnn : ∀ t ∈ Ioi ((2 : ℕ) - 1 : ℝ), 0 ≤ f t := by
    intro t ht
    have : (0:ℝ) < t := lt_trans hpos ht
    simp only [hf]; positivity
  have h := hanti.abs_tsum_sub_sum_range_le_integral (N := 2) (by norm_num) hint hnn
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEq, integral_Ioi_rpow_of_lt (by norm_num) hpos]
    at h
  have hs : ∑ n ∈ Finset.range 2, f n = 1 := by
    simp [hf, Finset.sum_range_succ]
  rw [hs] at h
  have h3 : -((2 : ℕ) - 1 : ℝ) ^ (-(11 / 10) + 1 : ℝ) / (-(11 / 10) + 1) = 10 := by norm_num
  rw [h3] at h
  have := (abs_le.mp h).2
  simp only [hf] at this
  linarith

/-- The parent leaf `vonMangoldt_tsum_eleven_tenths_le`, verbatim, from the three leaves:
`∑ Λ(n) n^{-11/10} ≤ 1.03883 ζ(11/10) ≤ 1.03883 · 11 ≤ 11.7`. -/
theorem vonMangoldt_tsum_eleven_tenths_le_split :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (11 / 10 : ℝ) ≤ 11.7 := by
  have hA : ∀ N : ℕ, ∑ n ∈ Ioc 0 N, (ArithmeticFunction.vonMangoldt n : ℝ) ≤
      1.03883 * (N : ℝ) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have h := psi_le_rosser_schoenfeld N (by exact_mod_cast hN)
      rwa [Chebyshev.psi, Nat.floor_natCast] at h
  have h1 := tsum_div_rpow_le_of_partial_sums_le _
    (fun n => ArithmeticFunction.vonMangoldt_nonneg) 1.03883 (11 / 10) (by norm_num) hA
  have h2 := tsum_one_div_rpow_eleven_tenths_le
  linarith

end LeanLab.HelfgottMajor.SplitVonMangoldtTsum
