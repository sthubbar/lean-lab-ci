import LeanLab.ExceptionalSet.GammaOne465
import LeanLab.HeathBrown1985.SingularSeries

/-!
P0082 page361 displays17 and18, the finite section of the Gamma2 tail.
The progression bounds and arithmetic envelopes are explicit hypotheses.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset

/-- P0082 page361 displays17 and18. The finite tail average above R and
through Y is controlled by a divisor count envelope T and progression
counts. CONDITIONAL ON those explicit finite hypotheses. -/
theorem near_gammaTwo_mean_explicit (s : Finset ℕ) (m : ℕ → ℤ) (r R Y : ℕ)
    (E C L T : ℝ) (N : ℕ) (hr : 1 ≤ r) (hR : 1 ≤ R) (hRY : R ≤ Y)
    (hE : 0 < E) (hC : 0 ≤ C) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hφ : ∀ q : ℕ, 1 ≤ q → q ≤ Y → (q : ℝ) / q.totient ≤ L)
    (hτ : ∀ q ∈ Ioc R Y, (q.divisors.card : ℝ) ≤ T)
    (hprog : ∀ d : ℕ, 1 ≤ d → d ≤ Y →
      ((s.filter (fun n => (d : ℤ) ∣ m n)).card : ℝ) ≤ C * ((N : ℝ) / d + N / E)) :
    (r : ℝ) * ∑ q ∈ (Ioc R Y).filter (fun q => r ∣ q),
      ∑ n ∈ s, 1 / ((q.totient : ℝ) * ((q / Int.gcd (m n) q).totient : ℝ)) ≤
        C * N * L ^ 2 * (2 * T / R + (1 + Real.log Y) ^ 2 / E) := by
  classical
  let t := (Ioc R Y).filter (fun q => r ∣ q)
  let H := 1 + Real.log Y
  have hY : 1 ≤ Y := hR.trans hRY
  have hH : 0 ≤ H := by dsimp [H]; have := Real.log_nonneg (by exact_mod_cast hY : (1 : ℝ) ≤ Y); linarith
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hRR : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hsq : ∑ q ∈ t, ((q : ℝ) ^ 2)⁻¹ ≤ 2 / ((r : ℝ) * R) :=
    LeanLab.HeathBrown1985.sum_multiples_inv_sq_le_mul R Y r hr hR
  have hinv : ∑ q ∈ t, (q : ℝ)⁻¹ ≤ H / r := by
    have hsub : t ⊆ (Icc 1 Y).filter (fun q => r ∣ q) := by
      intro q hq
      obtain ⟨hqI, hqr⟩ := mem_filter.mp hq
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by have := (mem_Ioc.mp hqI).1; omega, (mem_Ioc.mp hqI).2⟩, hqr⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
      (sum_inverse_multiples Y r hY hr)
  have hmean (q : ℕ) (hq : q ∈ t) :
      (∑ n ∈ s, (Int.gcd (m n) q : ℝ)) / (q : ℝ) ^ 2 ≤
        C * N * (T / (q : ℝ) ^ 2 + H / E / q) := by
    have hqI := mem_Ioc.mp (mem_filter.mp hq).1
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
      have hlog := Real.log_le_log hqR (by exact_mod_cast hqI.2 : (q : ℝ) ≤ Y)
      dsimp [H]
      linarith
    have hsdiv := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hs hE.le) hqR.le
    have hτdiv := div_le_div_of_nonneg_right (hτ q (mem_filter.mp hq).1) (sq_nonneg (q : ℝ))
    calc
      _ ≤ (C * N * q.divisors.card + C * N / E * ∑ d ∈ q.divisors, (d : ℝ)) / (q : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hm (sq_nonneg _)
      _ = C * N * ((q.divisors.card : ℝ) / (q : ℝ) ^ 2 +
          ((∑ d ∈ q.divisors, (d : ℝ)) / q) / E / q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hτdiv hsdiv) (by positivity)
  have hterm (q : ℕ) (hq : q ∈ t) :
      ∑ n ∈ s, 1 / ((q.totient : ℝ) * ((q / Int.gcd (m n) q).totient : ℝ)) ≤
        L ^ 2 * (C * N * (T / (q : ℝ) ^ 2 + H / E / q)) := by
    have hqI := mem_Ioc.mp (mem_filter.mp hq).1
    have hq0 : 0 < q := by omega
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
    have hkernel (n : ℕ) :
        1 / ((q.totient : ℝ) * ((q / Int.gcd (m n) q).totient : ℝ)) ≤
          L ^ 2 * (Int.gcd (m n) q : ℝ) / (q : ℝ) ^ 2 := by
      have h := div_le_div_of_nonneg_right
        (totient_kernel_le Y q (by omega) hqI.2 (m n) L hL hφ) hqR.le
      convert h using 1 <;> field_simp <;> ring
    calc
      _ ≤ ∑ n ∈ s, L ^ 2 * (Int.gcd (m n) q : ℝ) / (q : ℝ) ^ 2 := sum_le_sum (fun n _ => hkernel n)
      _ = L ^ 2 * ((∑ n ∈ s, (Int.gcd (m n) q : ℝ)) / (q : ℝ) ^ 2) := by
        rw [← sum_div, ← mul_sum]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmean q hq) (sq_nonneg L)
  have hsumid : (∑ q ∈ t, L ^ 2 * (C * N * (T / (q : ℝ) ^ 2 + H / E / q))) =
      L ^ 2 * C * N * (T * (∑ q ∈ t, ((q : ℝ) ^ 2)⁻¹) +
        H / E * (∑ q ∈ t, (q : ℝ)⁻¹)) := by
    have hi : (∑ q ∈ t, L ^ 2 * (C * N * (T / (q : ℝ) ^ 2 + H / E / q))) =
        ∑ q ∈ t, ((L ^ 2 * C * N * T) * ((q : ℝ) ^ 2)⁻¹ +
          (L ^ 2 * C * N * H / E) * (q : ℝ)⁻¹) := sum_congr rfl (fun q _ => by ring)
    rw [hi, sum_add_distrib, ← mul_sum, ← mul_sum]
    ring
  calc
    _ ≤ (r : ℝ) * ∑ q ∈ t, L ^ 2 * (C * N * (T / (q : ℝ) ^ 2 + H / E / q)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hterm) (Nat.cast_nonneg _)
    _ = (r : ℝ) * (L ^ 2 * C * N * (T * (∑ q ∈ t, ((q : ℝ) ^ 2)⁻¹) +
        H / E * (∑ q ∈ t, (q : ℝ)⁻¹))) := by rw [hsumid]
    _ ≤ (r : ℝ) * (L ^ 2 * C * N * (T * (2 / ((r : ℝ) * R)) + H / E * (H / r))) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hsq hT)
        (mul_le_mul_of_nonneg_left hinv (by positivity))
    _ = _ := by field_simp
                <;> ring

end LeanLab.ExceptionalSet.Supply465
