/-
Baker, Harman and Pintz 1997, page 21, the first frequency branch.
A first derivative estimate from the proved Kusmin Landau inequality.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.LogPhase219
import LeanLab.BakerHarmanPintz1997.DerivativeTest219

namespace LeanLab.BakerHarmanPintz1997.LowFrequency219
open Finset PortedVanDerCorput LogPhase219 DerivativeTest219

/-- Page 21. At low frequency the logarithmic progression sum has inverse frequency decay. -/
theorem logarithmic_first_derivative (p q : ℤ) {a T r N : ℝ}
    (ha : 0 < a) (hT : 0 < T) (hN : 0 < N) (haN : a ≤ N) (hsmall : T * a ≤ N / 2)
    (hleft : N ≤ a * p + r) (hright : a * q + r ≤ 2 * N) :
    ‖∑ n ∈ Icc p q, eK (T * (-Real.log (a * n + r)))‖ ≤ 4 * N / (T * a) := by
  let δ : ℝ := T * a / (4 * N)
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ : δ ≤ 1 / 2 := by dsimp [δ]; apply (div_le_iff₀ (by positivity)).mpr; nlinarith
  have hTa : T * a / N ≤ 1 / 2 := (div_le_iff₀ hN).mpr (by linarith [hsmall])
  let g : ℤ → ℝ := fun n => T * (-Real.log (a * n + r))
  have hinc : ∀ n ∈ Icc p q, -1 + δ ≤ g (n + 1) - g n ∧ g (n + 1) - g n ≤ -δ := by
    intro n hn
    have hnp : (p : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnq : (n : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hn).2
    have hlo : N ≤ a * (n : ℝ) + r := by nlinarith
    have hhi : a * (n : ℝ) + r + [a].sum ≤ 4 * N := by simp; nlinarith
    have hb := log_backwardDifferences_bounds [a] (by simp [ha]) (k := 0) (by simp) hN hlo hhi
    simp only [List.prod_cons, List.prod_nil, mul_one, Nat.factorial_zero, Nat.cast_one,
      Nat.zero_add, pow_one] at hb
    have heq : g (n + 1) - g n = -T * backwardDifferences [a] (fun z => -Real.log z) (a * n + r) := by
      dsimp [g, backwardDifferences]
      push_cast
      rw [show a * ((n : ℝ) + 1) + r = a * n + r + a by ring]
      ring
    rw [heq]
    dsimp [δ] at hδ ⊢
    have hb1 : T * a / (4 * N) ≤ T * backwardDifferences [a] (fun z => -Real.log z) (a * n + r) := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hb.1 hT.le
    have hb2 : T * backwardDifferences [a] (fun z => -Real.log z) (a * n + r) ≤ T * a / N := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hb.2 hT.le
    constructor <;> nlinarith [hb1, hb2]
  have hm : ∀ n ∈ Ico p q, g (n + 1) - g n ≤ g (n + 1 + 1) - g (n + 1) := by
    intro n hn
    have hnp : (p : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
    have hnq : (n : ℝ) ≤ q := by exact_mod_cast (mem_Ico.mp hn).2.le
    have hlo : N ≤ a * (n : ℝ) + r := by nlinarith
    have hhi : a * ((n : ℝ) + 2 + ([] : List ℝ).sum) + r ≤ 4 * N := by simp; nlinarith
    have hb := log_phase_second_difference_bounds [] (by simp) ha hT.le hN hlo hhi
    simp only [backwardDifferences, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, List.length_nil, Nat.zero_add, Nat.factorial_one, Nat.cast_one] at hb
    have hh : 0 ≤ T * (a * a) / (4 * N) ^ 2 := by positivity
    dsimp [g]
    push_cast
    linarith [hb.1]
  by_cases hpq : p ≤ q
  · have hb := kusmin_landau_int g p q hpq (m := -1) hδ0 hδ
      (by intro n hn; simpa using (hinc n hn).1)
      (by intro n hn; simpa using (hinc n hn).2) hm
    have hid : 1 / δ = 4 * N / (T * a) := by dsimp [δ]; field_simp
    simpa only [g, hid] using hb
  · rw [Icc_eq_empty_of_lt (by omega), sum_empty, norm_zero]
    positivity

/-- Page 21. An explicit second derivative bound for the remaining frequency range. -/
theorem logarithmic_second_derivative (p q : ℤ) {a T r N : ℝ}
    (ha : 1 ≤ a) (hT : 0 < T) (hN : 1 ≤ N) (haN : a ≤ N)
    (hleft : N ≤ a * p + r) (hright : a * q + r ≤ 2 * N) :
    ‖∑ n ∈ Icc p q, eK (T * (-Real.log (a * n + r)))‖ ≤
      64 * a * Real.sqrt T + 32 * N / (a * Real.sqrt T) := by
  have ha0 : 0 < a := by linarith
  have hN0 : 0 < N := by linarith
  let lam : ℝ := T * a ^ 2 / (4 * N) ^ 2
  have hlam : 0 < lam := by dsimp [lam]; positivity
  let g : ℤ → ℝ := fun n => T * (-Real.log (a * n + r))
  have hdiff : ∀ n ∈ Ico p q,
      lam ≤ (g (n + 1 + 1) - g (n + 1)) - (g (n + 1) - g n) ∧
      (g (n + 1 + 1) - g (n + 1)) - (g (n + 1) - g n) ≤ 16 * lam := by
    intro n hn
    have hnp : (p : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
    have hnq : (n : ℝ) ≤ q := by exact_mod_cast (mem_Ico.mp hn).2.le
    have hlo : N ≤ a * (n : ℝ) + r := by nlinarith
    have hhi : a * ((n : ℝ) + 2 + ([] : List ℝ).sum) + r ≤ 4 * N := by simp; nlinarith
    have hb := log_phase_second_difference_bounds [] (by simp) ha0 hT.le hN0 hlo hhi
    simp only [backwardDifferences, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, List.length_nil, Nat.zero_add, Nat.factorial_one, Nat.cast_one] at hb
    have hid : 16 * lam = T * (a * a) / N ^ 2 := by dsimp [lam]; field_simp <;> ring
    dsimp [g]
    push_cast
    constructor
    · simpa only [lam, pow_two] using hb.1
    · rw [hid]
      exact hb.2
  have hsqrt : Real.sqrt lam = Real.sqrt T * a / (4 * N) := by
    dsimp [lam]
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul hT.le,
      Real.sqrt_sq ha0.le, Real.sqrt_sq (by positivity)]
  by_cases hpq : p ≤ q
  · have hb := second_derivative_int g p q hpq hlam (by norm_num : (1 : ℝ) ≤ 16)
      (fun n hn => (hdiff n hn).1) (fun n hn => (hdiff n hn).2)
    have hdiff0 : (0 : ℝ) ≤ (q : ℝ) - p := by exact_mod_cast sub_nonneg.mpr hpq
    have hlen : (q : ℝ) - p + 1 ≤ 2 * N := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) hdiff0]
    calc
      _ ≤ 8 * (16 * ((q : ℝ) - p + 1) * Real.sqrt lam + 1 / Real.sqrt lam) := hb
      _ ≤ 8 * (16 * (2 * N) * Real.sqrt lam + 1 / Real.sqrt lam) := by gcongr
      _ = _ := by rw [hsqrt]; field_simp <;> ring
  · rw [Icc_eq_empty_of_lt (by omega), sum_empty, norm_zero]
    positivity

#print axioms logarithmic_second_derivative
#print axioms logarithmic_first_derivative
end LeanLab.BakerHarmanPintz1997.LowFrequency219
