/-
P0069, Theorem 1, pages 1 to 4. The written deduction uses the
sandwich on page 2 and the sieve sequences described on page 4.
The analytic input and interval covering are named leaves.
The final statement is exactly the lab's cited Theorem1.
CONDITIONAL on every unproved leaf. Goldbach is open.
AI wrote the Lean code. CODEX task132, 2026-10-26.
-/
import LeanLab.BHP1997.Cover132

namespace LeanLab.BHP1997.Decomp132
open Classical Real Filter

/-- The prime indicator rho on page 1. -/
noncomputable def primeWeight (n : ℕ) : ℝ := if n.Prime then 1 else 0

/-- The restricted convolution S_ij on page 2, indexed by the even integer N. -/
noncomputable def convolution (I J : Finset ℕ) (a b : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ I, ∑ m ∈ J, if k + m = N then a k * b m else 0

/-- LEAF. Page 2, inequalities 1.3 and 1.4 imply the pointwise sandwich.
The upper weights are nonnegative because the prime indicators are. -/
theorem pointwise_sandwich {p q a0 a1 b0 b1 : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (ha0 : a0 ≤ p) (ha1 : p ≤ a1)
    (hb0 : b0 ≤ q) (hb1 : q ≤ b1) :
    a0 * b1 + a1 * b0 - a1 * b1 ≤ p * q := by
  have hb1pos : 0 ≤ b1 := le_trans hq hb1
  have h1 := mul_nonneg (sub_nonneg.mpr ha0) hb1pos
  have h2 := mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb0)
  nlinarith

/-- LEAF. Page 2, summing the sandwich gives S_01 + S_10 - S_11 ≤ S. -/
theorem convolution_sandwich {I J : Finset ℕ} {a0 a1 b0 b1 : ℕ → ℝ}
    (ha : ∀ k ∈ I, a0 k ≤ primeWeight k ∧ primeWeight k ≤ a1 k)
    (hb : ∀ m ∈ J, b0 m ≤ primeWeight m ∧ primeWeight m ≤ b1 m) (N : ℕ) :
    convolution I J a0 b1 N + convolution I J a1 b0 N - convolution I J a1 b1 N ≤
      convolution I J primeWeight primeWeight N := by
  unfold convolution
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k hk
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro m hm
  by_cases heq : k + m = N
  · simp only [heq, ite_true]
    exact pointwise_sandwich (by simp [primeWeight]; positivity)
      (by simp [primeWeight]; positivity) (ha k hk).1 (ha k hk).2 (hb m hm).1 (hb m hm).2
  · simp [heq]

/-- LEAF. Page 1, display 1.2: a non-Goldbach integer has zero prime convolution. -/
theorem prime_convolution_zero (I J : Finset ℕ) {N : ℕ} (hN : ¬ IsGoldbachSum N) :
    convolution I J primeWeight primeWeight N = 0 := by
  unfold convolution
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro m hm
  by_cases heq : k + m = N
  · by_cases hkprime : k.Prime
    · have hmnot : ¬ m.Prime := fun hmprime => hN ⟨k, m, hkprime, hmprime, heq⟩
      simp [heq, primeWeight, hmnot]
    · simp [heq, primeWeight, hkprime]
  · simp [heq]

/-- LEAF. Page 2, the three asymptotics before 1.5 have positive signed sum
once each absolute error is at most one sixth of the positive main margin. -/
theorem correlation_positive {s01 s10 s11 u0 u1 v0 v1 r : ℝ}
    (hm : 0 < u0 * v1 + u1 * v0 - u1 * v1) (hr : 0 < r)
    (h01 : |s01 - u0 * v1 * r| ≤ (u0 * v1 + u1 * v0 - u1 * v1) * r / 6)
    (h10 : |s10 - u1 * v0 * r| ≤ (u0 * v1 + u1 * v0 - u1 * v1) * r / 6)
    (h11 : |s11 - u1 * v1 * r| ≤ (u0 * v1 + u1 * v0 - u1 * v1) * r / 6) :
    0 < s01 + s10 - s11 := by
  obtain ⟨h01low, h01up⟩ := abs_le.mp h01
  obtain ⟨h10low, h10up⟩ := abs_le.mp h10
  obtain ⟨h11low, h11up⟩ := abs_le.mp h11
  have hp := mul_pos hm hr
  nlinarith

/-- LEAF. Pages 1 to 4, displays 1.3 to 1.6 and the constructions in
Sections 4 and 5. Choose sufficiently small epsilon and the four sieve
weights. Theorem 2 gives their three correlations outside a common small
exceptional set. The positive scale is Y times the singular series divided
by log x log Y. The asymptotic errors are absorbed by the fixed margin.
This leaf includes the analytic work of Sections 2 to 5, not a new input
from a different paper. It remains CONDITIONAL. -/
theorem sieve_data :
    ∃ ε u0 u1 v0 v1 : ℝ, 0 < ε ∧ ε < 8.8 / 10 ^ 5 ∧
      0.99 < u0 ∧ u0 ≤ u1 ∧ u1 < 1.01 ∧ 0.05 < v0 ∧ v0 ≤ v1 ∧ v1 < 2.2 ∧
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
        ∃ (I J : Finset ℕ) (a0 a1 b0 b1 : ℕ → ℝ) (E : Finset ℕ),
          (∀ k ∈ I, a0 k ≤ primeWeight k ∧ primeWeight k ≤ a1 k) ∧
          (∀ m ∈ J, b0 m ≤ primeWeight m ∧ primeWeight m ≤ b1 m) ∧
          (E.card : ℝ) < x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) /
            Real.log x ^ A ∧
          ∀ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊,
            Even N → N ∉ E → ∃ r : ℝ, 0 < r ∧
              |convolution I J a0 b1 N - u0 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b0 N - u1 * v0 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b1 N - u1 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 := by
  sorry

/-- LEAF. Page 2, the deduction of Theorem 1 from 1.2: estimates on
intervals of exponent delta imply the claimed estimates at every strictly
larger exponent. A finite covering and an extra logarithmic saving absorb
boundary overlaps and covering constants. This includes theta greater
than 1, as required by the sealed lab statement. -/
theorem cover_short_intervals {δ θ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hθ : δ < θ)
    (hshort : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      (exceptions x (x ^ δ) : ℝ) < x ^ δ / Real.log x ^ A) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      (exceptions x (x ^ θ) : ℝ) < x ^ θ / Real.log x ^ A := by
  intro A hA
  obtain ⟨C, hC⟩ := hshort (A + 1) (by linarith)
  refine ⟨max C (Real.exp 4), fun x hx => ?_⟩
  have hxC : C ≤ x := le_trans (le_max_left _ _) hx
  have hxexp : Real.exp 4 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) < Real.exp 4 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  have hx0 : 0 < x := by linarith
  have hlog4 : 4 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 4) hxexp
  have hlog0 : 0 < Real.log x := by linarith
  have hxpow : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  obtain ⟨y, K, hK, hy0, hstep, hbase, hend, hlast⟩ :=
    power_mesh hx1 (show x < x + x ^ θ by linarith) hδ.le
  have hcount : (exceptions x (x ^ θ) : ℝ) ≤
      ∑ i ∈ Finset.range K, (exceptions (y i) ((y i) ^ δ) : ℝ) := by
    have hc := exception_cover y hK (show 0 ≤ x + x ^ θ by positivity) hend
    have hcancel (a b : ℝ) : a + b - a = b := by ring
    have hc' : exceptions x (x ^ θ) ≤
        ∑ i ∈ Finset.range K, exceptions (y i) ((y i) ^ δ) := by
      simpa only [hy0, hstep, hcancel] using hc
    exact_mod_cast hc'
  have hlocal (i : ℕ) :
      (exceptions (y i) ((y i) ^ δ) : ℝ) ≤ (y i) ^ δ / Real.log x ^ (A + 1) := by
    have hy1 : 1 ≤ y i := le_trans hx1 (hbase i)
    have hy0' : 0 < y i := by linarith
    have hlog : Real.log x ≤ Real.log (y i) := Real.log_le_log hx0 (hbase i)
    apply le_trans (hC (y i) (le_trans hxC (hbase i))).le
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy0'.le _)
      (Real.rpow_pos_of_pos hlog0 _)
      (Real.rpow_le_rpow hlog0.le hlog (by linarith))
  have hsum : (∑ i ∈ Finset.range K, (y i) ^ δ / Real.log x ^ (A + 1)) =
      (y K - x) / Real.log x ^ (A + 1) := by
    rw [← Finset.sum_div, mesh_sum y δ hstep, hy0]
  have hendpow : (x + x ^ θ) ^ δ ≤ 2 * x ^ θ :=
    endpoint_rpow_le hx1 hδ.le hδ1.le hθ.le
  have htotal : y K - x ≤ 3 * x ^ θ := by linarith
  have hden : Real.log x ^ (A + 1) = Real.log x ^ A * Real.log x := by
    rw [Real.rpow_add hlog0, Real.rpow_one]
  calc
    (exceptions x (x ^ θ) : ℝ) ≤ ∑ i ∈ Finset.range K,
        (exceptions (y i) ((y i) ^ δ) : ℝ) := hcount
    _ ≤ ∑ i ∈ Finset.range K, (y i) ^ δ / Real.log x ^ (A + 1) :=
      Finset.sum_le_sum (fun i _ => hlocal i)
    _ = (y K - x) / Real.log x ^ (A + 1) := hsum
    _ ≤ (3 * x ^ θ) / Real.log x ^ (A + 1) :=
      div_le_div_of_nonneg_right htotal (Real.rpow_nonneg hlog0.le _)
    _ < x ^ θ / Real.log x ^ A := by
      rw [hden, div_lt_div_iff₀ (by positivity) (by positivity)]
      have hp : 0 < x ^ θ * Real.log x ^ A :=
        mul_pos hxpow (Real.rpow_pos_of_pos hlog0 A)
      nlinarith [mul_lt_mul_of_pos_left (show (3 : ℝ) < Real.log x by linarith) hp]


/-- Theorem 1, page 1, with the exact cited Prop as conclusion.
CONDITIONAL on sieve_data. The assembly has
no direct sorry. -/
theorem theorem1 : Theorem1 := by
  obtain ⟨ε, u0, u1, v0, v1, hε, hε1, hu0, hu, hu1, hv0, hv, hv1, hdata⟩ := sieve_data
  have hm := constants15 hu0 hu hu1 hv0 hv hv1
  have hδ := theta12 hε hε1
  intro θ hθ
  apply cover_short_intervals (by linarith : 0 < (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))
    (by linarith : (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) < 1)
    (lt_of_lt_of_le hδ.1 hθ)
  intro A hA
  obtain ⟨C, hC⟩ := hdata A hA
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨I, J, a0, a1, b0, b1, E, ha, hb, hE, hcorr⟩ := hC x hx
  have hsub : (Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
      (fun N => Even N ∧ ¬ IsGoldbachSum N) ⊆ E := by
    intro N hN
    obtain ⟨hNI, hEven, hnot⟩ := Finset.mem_filter.mp hN
    by_contra hNE
    obtain ⟨r, hr, h01, h10, h11⟩ := hcorr N hNI hEven hNE
    have hpos := correlation_positive hm hr h01 h10 h11
    have hle := convolution_sandwich ha hb N
    rw [prime_convolution_zero I J hnot] at hle
    linarith
  exact lt_of_le_of_lt (by exact_mod_cast Finset.card_le_card hsub) hE

end LeanLab.BHP1997.Decomp132
