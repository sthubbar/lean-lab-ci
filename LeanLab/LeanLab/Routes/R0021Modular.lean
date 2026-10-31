import Mathlib

/-!
# R-0021 The modular route: an exact Jacobi-type formula for r(N) needs a modular prime series

Route R-0021, unit U-1175, PC run 20261020T0603Z-352. AI wrote this Lean code.

For sums of two squares, θ(τ)² is a weight 1 modular form and Jacobi's identity
r₂(N) = 4 Σ_{d ∣ N} χ₄(d) is exact for every N, with no sieve and no parity issue.
The route asks whether the prime series P(q) = Σ_p q^p, or any modification of it with the
same coefficients up to sign, could be modular, so that r(N), the Goldbach count, would have
an exact divisor-sum formula in the same way.

Two facts about the coefficients 1_P(n) close the easy doors. Both are proved here,
unconditionally:

* `not_eventually_periodic`: 1_P is not eventually periodic, so P(q) is not a rational
  function of q, and is not a combination of weight 0 forms or of periodic Eisenstein-type
  coefficient sequences.
* `tendsto_pi_div_self` and `tendsto_pi_div_sqrt`: π(n)/n → 0 and π(n)/√n → ∞, so the
  mean square Σ_{n ≤ x} 1_P(n)² = π(x) is o(x) and grows faster than every constant times √x.

The cited side, NOT formalized here: by Rankin-Selberg, a cusp form of weight k has
Σ_{n ≤ x} |a_n|² ~ c x^k with c > 0; weight 1/2 forms are combinations of theta series, by
Serre-Stark, whose coefficient support up to x has size ≍ √x; Eisenstein parts give c x log x
in weight 1 and c x^{2k - 1} in weight k ≥ 3/2. A form with 0, 1 coefficients on the primes
would need a mean square π(x) ~ x/log x, strictly between √x and x. The proved lemmas below are
the prime side of that mismatch; the modular side is a citation, so the conclusion
"P(q) is not modular" is CONDITIONAL ON those cited mean-square laws in this file.

Binary Goldbach itself is OPEN; this file proves nothing about it.
-/

namespace LeanLab.Routes.R0021

open Real Filter Topology Chebyshev

/-- The prime indicator is not eventually periodic: no period `M ≥ 1` and start `n₀` make
`n + M` prime exactly when `n` is prime for all `n ≥ n₀`. -/
theorem not_eventually_periodic (M n₀ : ℕ) (hM : 1 ≤ M) :
    ¬ ∀ n ≥ n₀, ((n + M).Prime ↔ n.Prime) := by
  intro h
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (n₀ + 2)
  have key : ∀ k : ℕ, ((p + k * M).Prime ↔ p.Prime) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := h (p + k * M) (by omega)
      rw [show p + (k + 1) * M = p + k * M + M by ring, this, ih]
  have hcomp : ¬ (p + p * M).Prime := by
    rw [show p + p * M = p * (1 + M) by ring]
    exact Nat.not_prime_mul (by omega) (by omega)
  exact hcomp ((key p).2 hp)

/-- Weight 0 consequence in sequence form: the prime indicator is not a periodic function. -/
theorem not_periodic (M : ℕ) (hM : 1 ≤ M) : ¬ ∀ n, ((n + M).Prime ↔ n.Prime) :=
  fun h => not_eventually_periodic M 0 hM (fun n _ => h n)

/-- π(n)/n → 0. -/
theorem tendsto_pi_div_self :
    Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun n : ℕ => 2 * Real.log 4 * (Real.log n)⁻¹ + (√(n : ℝ))⁻¹)
      atTop (𝓝 0) := by
    have h1 := (hlog.inv_tendsto_atTop).const_mul (2 * Real.log 4)
    have h2 := hsq.inv_tendsto_atTop
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · exact Eventually.of_forall fun n => by positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hx : (1 : ℝ) < n := by exact_mod_cast hn
    have hb := Chebyshev.pi_le_log4_mul_div hx
    rw [Nat.floor_natCast] at hb
    have hn0 : (0 : ℝ) < n := by linarith
    have hl : 0 < Real.log n := Real.log_pos hx
    have hsqrt : Real.log √(n : ℝ) = Real.log n / 2 := by
      rw [Real.log_sqrt hn0.le]
    rw [hsqrt] at hb
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
    have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
    rw [div_le_iff₀ hn0]
    calc (Nat.primeCounting n : ℝ) ≤ Real.log 4 * n / (Real.log n / 2) + √(n : ℝ) := hb
      _ = (2 * Real.log 4 * (Real.log n)⁻¹ + (√(n : ℝ))⁻¹) * n := by
        field_simp
        nlinarith [hss]

/-- π(n)/√n → ∞. -/
theorem tendsto_pi_div_sqrt :
    Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / √(n : ℝ)) atTop atTop := by
  -- √x / log x → ∞ on the reals
  have hlo : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x / x ^ (1 / 2 : ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact div_pos (Real.log_pos hx) (Real.rpow_pos_of_pos (by linarith) _)
  have hinv : Tendsto (fun x : ℝ => (Real.log x / x ^ (1 / 2 : ℝ))⁻¹) atTop atTop :=
    (tendsto_nhdsWithin_iff.mpr ⟨hlo, hpos⟩).inv_tendsto_nhdsGT_zero
  have hR : Tendsto (fun x : ℝ => √x / Real.log x) atTop atTop := by
    refine hinv.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [inv_div, Real.sqrt_eq_rpow]
  have hN : Tendsto (fun n : ℕ => Real.log 2 * (√(n : ℝ) / Real.log n)) atTop atTop :=
    (hR.comp tendsto_natCast_atTop_atTop).const_mul_atTop (Real.log_pos one_lt_two)
  have hz : Tendsto (fun n : ℕ => -(2 * (√(n : ℝ))⁻¹)) atTop (𝓝 0) := by
    have := ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop).const_mul 2
    simpa using this.neg
  refine tendsto_atTop_mono' atTop ?_ (hN.atTop_add hz)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hx : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl : 0 < Real.log n := Real.log_pos hx
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
  have hge := Chebyshev.pi_ge n
  -- log (n + 1) ≤ 2 log n for n ≥ 2
  have hlog1 : Real.log (n + 1) ≤ 2 * Real.log n := by
    rw [← Real.log_rpow hn0]
    apply Real.log_le_log (by linarith)
    have : (n : ℝ) ^ (2 : ℝ) = n * n := by norm_num [sq]
    have h2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    rw [this]; nlinarith
  have hpi : (n : ℝ) * Real.log 2 / Real.log n - 2 ≤ Nat.primeCounting n := by
    refine le_trans ?_ hge
    rw [sub_div]
    have : Real.log (n + 1) / Real.log n ≤ 2 := by
      rw [div_le_iff₀ hl]; linarith
    linarith
  rw [le_div_iff₀ hs]
  calc (Real.log 2 * (√(n : ℝ) / Real.log n) + -(2 * (√(n : ℝ))⁻¹)) * √(n : ℝ)
      = (n : ℝ) * Real.log 2 / Real.log n - 2 := by
        field_simp
        rw [Real.sq_sqrt hn0.le]; ring
    _ ≤ _ := hpi

/-- Consequence used by the route: the prime mean square is not asymptotic to c·x for any c,
nor to c·√x for any c. -/
theorem pi_not_linear_nor_sqrt (c : ℝ) (hc : c ≠ 0) :
    ¬ Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / n) atTop (𝓝 c) ∧
    ¬ Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / √(n : ℝ)) atTop (𝓝 c) := by
  refine ⟨fun h => hc (tendsto_nhds_unique h tendsto_pi_div_self), fun h => ?_⟩
  exact not_tendsto_nhds_of_tendsto_atTop tendsto_pi_div_sqrt c h

/-- Vacuity: the hypotheses of `not_eventually_periodic` can hold, and the statement is
not about an empty case: `M = 1, n₀ = 0`. -/
example : ¬ ∀ n ≥ 0, ((n + 1).Prime ↔ n.Prime) := not_eventually_periodic 1 0 le_rfl

end LeanLab.Routes.R0021
