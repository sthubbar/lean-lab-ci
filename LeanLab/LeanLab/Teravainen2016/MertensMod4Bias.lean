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

/-- LEAF: page 15, second inequality of the display after display 4.3, the Mertens theorem for
the nonprincipal character chi_4: the sums over primes p at most x of chi_4 p log p / p are
bounded uniformly in x at least 2. Class HARD. Davenport, Multiplicative Number Theory,
Chapter 4, the proof of Dirichlet's theorem, where it follows from L 1 chi_4 = pi / 4 nonzero.
Here chi_4 p is 1 for p = 1 mod 4, -1 for p = 3 mod 4 and 0 for p = 2. -/
theorem leaf_mertens_chi4 :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊,
        (if p % 4 = 1 then (1 : ℝ) else if p % 4 = 3 then -1 else 0) * log p / p| ≤ B₀ := by
  exact?

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
