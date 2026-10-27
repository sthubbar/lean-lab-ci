import Mathlib

/-!
# R-5031, the hyperbola switch for `τ` and for `Λ`

Lab proof, unit U-5309, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics,
the Dirichlet hyperbola method. Binary Goldbach is OPEN.

* `sum_divisors_switch`: `Σ_{d ∣ n} f(d, n/d) = Σ_{d ∣ n, d² ≤ n} f(d, n/d) + Σ_{e ∣ n, e² < n} f(n/e, e)`;
* `tau_switch`: `τ(n) = #{d ∣ n : d² ≤ n} + #{e ∣ n : e² < n}`, both halves are divisor counts at
  level `√n`, which is why `Σ_{p<N} τ(N - p)` is a level `√N` problem;
* `vonMangoldt_switch`: `Λ(n) = Σ_{d ∣ n, d² ≤ n} μ(d) log(n/d) + Σ_{e ∣ n, e² < n} μ(n/e) log e`,
  the second half carries `μ` of the divisor above `√n`, the parity sensitive part.
-/

namespace LeanLab.Routes.R5031

open Finset ArithmeticFunction

lemma sum_divisors_switch (n : ℕ) (hn : n ≠ 0) (f : ℕ → ℕ → ℝ) :
    ∑ d ∈ n.divisors, f d (n / d) =
      ∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), f d (n / d) +
        ∑ e ∈ n.divisors.filter (fun e => e * e < n), f (n / e) e := by
  rw [← sum_filter_add_sum_filter_not n.divisors (fun d => d * d ≤ n)]
  congr 1
  apply sum_nbij' (fun d => n / d) (fun e => n / e)
  · intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd ⊢
    refine ⟨⟨Nat.div_dvd_of_dvd hd.1.1, hn⟩, ?_⟩
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1.1 (Nat.pos_of_ne_zero hn)
    have hlt : n / d < d := (Nat.div_lt_iff_lt_mul hd0).mpr (by push Not at hd; exact hd.2)
    have hq : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd.1.1) hd0
    calc n / d * (n / d) < n / d * d := (Nat.mul_lt_mul_left hq).mpr hlt
      _ ≤ n := Nat.div_mul_le_self n d
  · intro e he
    simp only [mem_filter, Nat.mem_divisors] at he ⊢
    refine ⟨⟨Nat.div_dvd_of_dvd he.1.1, hn⟩, ?_⟩
    push Not
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos he.1.1 (Nat.pos_of_ne_zero hn)
    have hn' : e * (n / e) = n := Nat.mul_div_cancel' he.1.1
    have hlt : e < n / e := by
      by_contra h; push Not at h
      have : e * (n / e) ≤ e * e := Nat.mul_le_mul_left e h
      omega
    calc n = e * (n / e) := hn'.symm
      _ < n / e * (n / e) := Nat.mul_lt_mul_of_pos_right hlt (by omega)
  · intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    exact Nat.div_div_self hd.1.1 hn
  · intro e he
    simp only [mem_filter, Nat.mem_divisors] at he
    exact Nat.div_div_self he.1.1 hn
  · intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    simp only [Nat.div_div_self hd.1.1 hn]

/-- `τ(n) = #{d ∣ n : d² ≤ n} + #{e ∣ n : e² < n}`. -/
theorem tau_switch (n : ℕ) (hn : n ≠ 0) :
    (n.divisors.card : ℝ) = ((n.divisors.filter (fun d => d * d ≤ n)).card : ℝ) +
      ((n.divisors.filter (fun e => e * e < n)).card : ℝ) := by
  have h := sum_divisors_switch n hn (fun _ _ => (1 : ℝ))
  simp only [sum_const, nsmul_eq_mul, mul_one] at h
  exact h

/-- `Λ(n) = Σ_{d ∣ n, d² ≤ n} μ(d) log(n/d) + Σ_{e ∣ n, e² < n} μ(n/e) log e`. -/
theorem vonMangoldt_switch (n : ℕ) (hn : n ≠ 0) :
    vonMangoldt n =
      ∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), (moebius d : ℝ) * Real.log ((n / d : ℕ) : ℝ) +
        ∑ e ∈ n.divisors.filter (fun e => e * e < n), (moebius (n / e) : ℝ) * Real.log (e : ℝ) := by
  have h0 : vonMangoldt n = ∑ d ∈ n.divisors, (moebius d : ℝ) * Real.log ((n / d : ℕ) : ℝ) := by
    rw [← moebius_mul_log_eq_vonMangoldt, mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => ((moebius : ArithmeticFunction ℝ) a) * log b)]
    simp [log_apply]
  rw [h0]
  exact sum_divisors_switch n hn (fun a b => (moebius a : ℝ) * Real.log (b : ℝ))

end LeanLab.Routes.R5031
