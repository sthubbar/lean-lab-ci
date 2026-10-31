/-
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5702, paper P0064.

# Chudakov 1938, Lemma 6, p. 30

`ν₂(x)` counts the `n` in `(1, x)` that are not a sum of two odd primes and have
`τ(n) ≥ ξ (lg x)^{-1}`, with `ξ = (lg x)^{M+6}` from Section I, p. 27. Lemma 6:
`ν₂(x) ≤ c₁₄ x (lg x)^{-M}`. The proof uses only `τ(1) + ... + τ(x) ≤ c₁₄ x lg x`, so condition 1°
plays no part; `lemma6` proves it with `c₁₄ = 2` for `x ≥ 3`, over `[1, x]`, which is stronger.

* `sum_card_divisors_le`: `Σ_{n ≤ x} τ(n) ≤ x (1 + log x)`, the "известно" step.
* `lemma6`: the lemma. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Tchudakov1938.Deduction

namespace LeanLab.Tchudakov1938
open Real Finset

attribute [local instance] Classical.propDecidable

/-- The multiples of `d` in `[1, x]` number at most `x / d`. -/
theorem card_multiples_Icc_le (x d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 x).filter (fun n => d ∣ n)).card ≤ x / d := by
  calc ((Finset.Icc 1 x).filter (fun n => d ∣ n)).card
      ≤ (Finset.Icc 1 (x / d)).card := by
        refine Finset.card_le_card_of_injOn (fun n => n / d) ?_ ?_
        · intro n hn
          simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hn
          obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hn
          simp only [Finset.coe_Icc, Set.mem_Icc]
          rw [Nat.mul_div_cancel_left _ hd]
          refine ⟨?_, (Nat.le_div_iff_mul_le hd).mpr (by rw [mul_comm]; exact h2)⟩
          rcases Nat.eq_zero_or_pos k with hk | hk
          · subst hk; omega
          · exact hk
        · intro a ha b hb hab
          simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at ha hb
          simp only at hab
          rw [← Nat.div_mul_cancel ha.2, ← Nat.div_mul_cancel hb.2, hab]
    _ = x / d := by simp

/-- `Σ_{n ≤ x} τ(n) ≤ x (1 + log x)`. -/
theorem sum_card_divisors_le (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, (n.divisors.card : ℝ)) ≤ x * (1 + Real.log x) := by
  have hswap : (∑ n ∈ Finset.Icc 1 x, (n.divisors.card : ℝ)) =
      ∑ d ∈ Finset.Icc 1 x, (((Finset.Icc 1 x).filter (fun n => d ∣ n)).card : ℝ) := by
    have : ∀ n ∈ Finset.Icc 1 x,
        (n.divisors.card : ℝ) = ∑ d ∈ Finset.Icc 1 x, if d ∣ n then (1 : ℝ) else 0 := by
      intro n hn
      simp only [Finset.mem_Icc] at hn
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_one]
      congr 1
      congr 1
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdn, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdn (by omega), (Nat.le_of_dvd (by omega) hdn).trans hn.2⟩, hdn⟩
      · rintro ⟨_, hdn⟩; exact ⟨hdn, by omega⟩
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_one]
  rw [hswap]
  calc (∑ d ∈ Finset.Icc 1 x, (((Finset.Icc 1 x).filter (fun n => d ∣ n)).card : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 x, (x : ℝ) * (d : ℝ)⁻¹ := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        simp only [Finset.mem_Icc] at hd
        have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        have h := card_multiples_Icc_le x d (by omega)
        calc (((Finset.Icc 1 x).filter (fun n => d ∣ n)).card : ℝ) ≤ ((x / d : ℕ) : ℝ) := by
              exact_mod_cast h
          _ ≤ (x : ℝ) / d := Nat.cast_div_le
          _ = _ := by rw [div_eq_mul_inv]
    _ = x * (harmonic x : ℝ) := by
        rw [← Finset.mul_sum, harmonic_eq_sum_Icc]; push_cast; rfl
    _ ≤ x * (1 + Real.log x) := by
        apply mul_le_mul_of_nonneg_left (harmonic_le_one_add_log x) (by positivity)

/-- Chudakov's `ν₂(x)` over `[1, x]`, with `ξ (lg x)^{-1} = (lg x)^{M+5}`. -/
noncomputable def nu2 (M : ℝ) (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun n => ¬ IsOddGoldbachSum n ∧
    Real.log x ^ (M + 6) / Real.log x ≤ (n.divisors.card : ℝ))).card

/-- Lemma 6, p. 30: `ν₂(x) ≤ 2 x (lg x)^{-M}` for `x ≥ 3` and every real `M`. -/
theorem lemma6 (M : ℝ) (x : ℕ) (hx : 3 ≤ x) :
    (nu2 M x : ℝ) ≤ 2 * x * Real.log x ^ (-M) := by
  have hx1 : Real.exp 1 ≤ x := by
    have := Real.exp_one_lt_d9; have : (3 : ℝ) ≤ x := by exact_mod_cast hx
    linarith
  have hl1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx1
  have hl0 : 0 < Real.log x := by linarith
  set T := Real.log x ^ (M + 6) / Real.log x with hT
  have hTpos : 0 < T := by positivity
  -- T ν₂ ≤ Σ τ ≤ x (1 + log x) ≤ 2 x log x
  have hsum : T * (nu2 M x : ℝ) ≤ 2 * x * Real.log x := by
    have h1 : T * (nu2 M x : ℝ) ≤
        ∑ n ∈ (Finset.Icc 1 x).filter (fun n => ¬ IsOddGoldbachSum n ∧
          T ≤ (n.divisors.card : ℝ)), (n.divisors.card : ℝ) := by
      rw [nu2, ← hT, mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum (fun n hn => (Finset.mem_filter.mp hn).2.2)
    have h2 : (∑ n ∈ (Finset.Icc 1 x).filter (fun n => ¬ IsOddGoldbachSum n ∧
          T ≤ (n.divisors.card : ℝ)), (n.divisors.card : ℝ)) ≤
        ∑ n ∈ Finset.Icc 1 x, (n.divisors.card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    have h3 := sum_card_divisors_le x
    have hx0 : (0 : ℝ) ≤ x := by positivity
    nlinarith
  -- T = (log x)^(M+5) ≥ (log x)^(M+1)
  have hTeq : T = Real.log x ^ (M + 5) := by
    rw [hT, Real.rpow_add hl0, Real.rpow_add hl0]
    rw [show (6 : ℝ) = 5 + 1 by norm_num, Real.rpow_add hl0, Real.rpow_one]
    field_simp
  have hTge : Real.log x ^ (M + 1) ≤ T := by
    rw [hTeq]; exact Real.rpow_le_rpow_of_exponent_le hl1 (by linarith)
  have hpow : Real.log x ^ (M + 1) = Real.log x ^ M * Real.log x := by
    rw [Real.rpow_add hl0, Real.rpow_one]
  have hpos : 0 < Real.log x ^ M := Real.rpow_pos_of_pos hl0 M
  -- ν₂ ≤ 2 x log x / T ≤ 2 x / (log x)^M
  rw [Real.rpow_neg hl0.le]
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  have hν0 : (0 : ℝ) ≤ nu2 M x := by positivity
  have : (nu2 M x : ℝ) * (Real.log x ^ M * Real.log x) ≤ 2 * x * Real.log x := by
    rw [← hpow]; nlinarith
  nlinarith

end LeanLab.Tchudakov1938
