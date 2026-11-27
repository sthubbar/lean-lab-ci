import LeanLab.ExceptionalSet.SPLIT_leaf_near_zero_selected

/-!
Feed 1122, wave 2: a split of `leaf_near_zero_even_index` along the analytic chain of
P0082, Bruedern and Perelli 1998, proof of Lemma 7, case ii d, journal pages 363 and 364.

The existing file `SPLIT_leaf_near_zero_even_index.lean` cuts by conductor range, but its
short modulus leaf is proved from `leaf_near_zero_even_index` itself, so that split does not
carry the parent.  This file makes a different cut, by the steps of the paper proof.

* The branch of `SelectedRealZero` with no exceptional zero has `r = 1`, which contradicts the
  hypothesis `1 < gcd`; this is proved here.
* LEAF HARD: display 20 together with the first display of page 364 gives a lower bound
  `c (1 - beta) X` for the major arc integral up to the divisor error.
* LEAF HARD: display 10, the Page type bound `1 - beta >> r^(-1/2) (log r)^(-2)`.
* LEAF MEDIUM: for `r <= calE^(1/7)` and large `N`, `r^(-1/2) (log r)^(-2)` beats `calE^(-1/10)`.

The assembly chains these and is proved.  AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF: P0082 page 363 display 20 combined with page 364 first display, case ii d. HARD.
With the exceptional real primitive character `χ` of conductor `r` and its zero `β`, the product
of display 21 empty and `1 < gcd`, one has `I(m) ≤ m^β`, so the main term
`m S(m) + I(m) S'(m)` is at least `S(m) (m - m^β) ≫ (1 - β) m`, and display 20 turns this into
a lower bound `c (1 - β) X` for `Re R1` at the even frequency `nu γ n`, the divisor error
carrying the large conductor terms and the remaining Siegel error being at most half the
leading term for small `δ`.  The factors `log P` and `m / φ(m)` of the paper are dropped,
which only weakens the bound. -/
theorem leaf_near_zero_even_main_term (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
              χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β →
              1 - a / Real.log (F γ N ^ (6 * δ)) ≤ β → β < 1 → χ.LFunction β = 0 →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                c * (1 - β) * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
  sorry

/-- LEAF: P0082 page 358 display 10, citing Davenport chapter 14. HARD.
The zero `β < 1` of the L function of a nonprincipal real primitive character of conductor `r`
satisfies `1 - β ≫ r^(-1/2) (log r)^(-2)`; the logarithm is shifted to `log (r + 2)` so that it
is positive for every conductor. -/
theorem leaf_near_zero_page_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β → β < 1 → χ.LFunction β = 0 →
        c / (Real.sqrt r * Real.log ((r : ℝ) + 2) ^ 2) ≤ 1 - β := by
  sorry

/-- LEAF: P0082 page 364 last lines, the step from display 10 to `X calE^(-1/10)`. MEDIUM.
For `1 ≤ r ≤ calE^(1/7)` one has `r^(-1/2) (log r)^(-2) ≥ calE^(-1/14) (log calE)^(-2)`, and this
is at least `calE^(-1/10)` once `N` is large, since `calE` tends to infinity for `γ < 3/2`. -/
theorem leaf_near_zero_conductor_power (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
      calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ 1 / (Real.sqrt r * Real.log ((r : ℝ) + 2) ^ 2) := by
  have hγ3 : 0 < (3 : ℝ) - 2 * γ := by linarith
  have hcalE_tendsto : Tendsto (fun N : ℕ => calE γ κ N) atTop atTop := by
    have h₁ : Tendsto (fun N : ℕ => (κ : ℝ) * Real.log (N : ℝ) ^ (3 - 2 * γ)) atTop atTop := by
      have h₂ : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop := by
        exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      have h₃ : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (3 - 2 * γ)) atTop atTop := by
        exact tendsto_rpow_atTop (by linarith).comp h₂
      have h₄ : Tendsto (fun N : ℕ => (κ : ℝ) * Real.log (N : ℝ) ^ (3 - 2 * γ)) atTop atTop := by
        exact h₃.const_mul_atTop (by positivity)
      exact h₄
    have h₅ : Tendsto (fun N : ℕ => Real.exp ((κ : ℝ) * Real.log (N : ℝ) ^ (3 - 2 * γ))) atTop atTop := by
      exact Real.tendsto_exp_atTop.comp h₁
    have h₆ : (fun N : ℕ => calE γ κ N) = (fun N : ℕ => Real.exp ((κ : ℝ) * Real.log (N : ℝ) ^ (3 - 2 * γ))) := by
      funext N
      simp [calE]
      <;> ring_nf
      <;> field_simp
      <;> ring_nf
    rw [h₆]
    exact h₅
  -- Choose C = exp(16) such that C^(2/5) ≥ (log(2C))^2
  have hC : Real.exp 16 ^ (2 / 5 : ℝ) ≥ Real.log (2 * Real.exp 16) ^ 2 := by
    have h₁ : Real.exp 16 ^ (2 / 5 : ℝ) = Real.exp (16 * (2 / 5 : ℝ)) := by
      rw [Real.rpow_natCast]
      simp [Real.exp_mul, Real.rpow_nat_cast]
      <;> ring_nf
      <;> field_simp
      <;> ring_nf
    rw [h₁]
    have h₂ : Real.log (2 * Real.exp 16) = Real.log 2 + 16 := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos 16)]
      <;> simp [Real.log_exp]
      <;> ring
    rw [h₂]
    have h₃ : Real.exp (16 * (2 / 5 : ℝ)) ≥ (Real.log 2 + 16 : ℝ) ^ 2 := by
      have := Real.exp_one_gt_d9
      have := Real.exp_pos (16 * (2 / 5 : ℝ))
      norm_num [Real.exp_pos, Real.exp_lt_exp.mpr] at *
      <;>
      (try norm_num) <;>\
      (try linarith [Real.add_one_le_exp (16 * (2 / 5 : ℝ))]) <;>\
      (try nlinarith [Real.add_one_le_exp (16 * (2 / 5 : ℝ)), Real.log_two_gt_d9]) <;>\
      (try
        {
          have := Real.exp_one_gt_d9
          norm_num at *
          <;>
          nlinarith [Real.add_one_le_exp (16 * (2 / 5 : ℝ)), Real.log_two_gt_d9]
        })
    linarith
  -- Obtain N₀ such that for all N ≥ N₀, calE γ κ N ≥ exp(16)
  have hN₀ : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Real.exp 16 ≤ calE γ κ N := by
    have h₁ : ∀ᶠ (N : ℕ) in atTop, Real.exp 16 ≤ calE γ κ N := by
      have h₂ : Tendsto (fun N : ℕ => calE γ κ N) atTop atTop := hcalE_tendsto
      exact (h₂.eventually (eventually_ge_atTop (Real.exp 16)))
    obtain ⟨N₀, hN₀⟩ := (eventually_atTop.mp h₁)
    refine' ⟨N₀, _⟩
    intro N hN
    exact hN₀ N hN
  obtain ⟨N₀, hN₀⟩ := hN₀
  use N₀
  intro N hN r hr hrE
  have hE : Real.exp 16 ≤ calE γ κ N := hN₀ N hN
  have hEpos : 0 < calE γ κ N := by linarith [Real.exp_pos 16]
  have hE1 : 1 ≤ calE γ κ N := by linarith [Real.one_lt_iff_neg_pos.mpr (Real.exp_pos 16)]
  have hrpos : 0 < (r : ℝ) := by positivity
  have hr1 : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  -- Since r ≤ calE^(1/7) and calE ≥ 1, we have r ≤ calE
  have hrcalE : (r : ℝ) ≤ calE γ κ N := by
    have h₁ : (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) := hrE
    have h₂ : calE γ κ N ^ (1 / 7 : ℝ) ≤ calE γ κ N := by
      apply Real.rpow_le_rpow_of_exponent_le
      · linarith
      · norm_num
      · linarith
    linarith
  -- sqrt(r) ≤ sqrt(calE), so 1/sqrt(r) ≥ calE^(-1/2)
  have hsqrt : Real.sqrt (r : ℝ) ≤ Real.sqrt (calE γ κ N) := Real.sqrt_le_sqrt hrcalE
  have hsqrt_pos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hrpos
  have hsqrtE_pos : 0 < Real.sqrt (calE γ κ N) := Real.sqrt_pos.mpr hEpos
  have hinv_sqrt : 1 / Real.sqrt (r : ℝ) ≥ 1 / Real.sqrt (calE γ κ N) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact hsqrt
  have hinv_sqrt' : 1 / Real.sqrt (calE γ κ N) = (calE γ κ N) ^ (-(1 / 2 : ℝ)) := by
    have h₁ : Real.sqrt (calE γ κ N) = (calE γ κ N) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      <;> norm_num
    rw [h₁]
    field_simp [Real.rpow_neg, Real.rpow_add, Real.rpow_one, hEpos.ne']
    <;> ring_nf
    <;> field_simp [Real.rpow_neg, Real.rpow_add, Real.rpow_one, hEpos.ne']
    <;> ring_nf
  -- log(r+2) ≤ log(calE+2) ≤ log(2*calE) for calE ≥ 2
  have hlog : Real.log ((r : ℝ) + 2) ≤ Real.log (2 * calE γ κ N) := by
    have h₁ : (r : ℝ) + 2 ≤ 2 * calE γ κ N := by
      have h₂ : (r : ℝ) ≤ calE γ κ N := hrcalE
      have h₃ : (2 : ℝ) ≤ calE γ κ N := by linarith [Real.exp_pos 16]
      nlinarith
    have h₂ : 0 < (r : ℝ) + 2 := by positivity
    have h₃ : 0 < 2 * calE γ κ N := by positivity
    apply Real.log_le_log
    · positivity
    · linarith
  have hlog_pos : 0 < Real.log ((r : ℝ) + 2) := Real.log_pos (by linarith)
  have hlogE_pos : 0 < Real.log (2 * calE γ κ N) := Real.log_pos (by
    have h₁ : (1 : ℝ) < 2 * calE γ κ N := by
      have h₂ : Real.exp 16 ≤ calE γ κ N := hE
      have h₃ : (1 : ℝ) < Real.exp 16 := by norm_num [Real.exp_pos]
      linarith
    linarith)
  have hinv_log : 1 / Real.log ((r : ℝ) + 2) ^ 2 ≥ 1 / Real.log (2 * calE γ κ N) ^ 2 := by
    apply one_div_le_one_div_of_le
    · positivity
    · gcongr <;> nlinarith
  -- Combine: 1/(sqrt(r)*log(r+2)^2) ≥ calE^(-1/2) / log(2*calE)^2
  have hmain : 1 / (Real.sqrt r * Real.log ((r : ℝ) + 2) ^ 2) ≥ (calE γ κ N) ^ (-(1 / 2 : ℝ)) / Real.log (2 * calE γ κ N) ^ 2 := by
    calc
      1 / (Real.sqrt r * Real.log ((r : ℝ) + 2) ^ 2) = (1 / Real.sqrt (r : ℝ)) * (1 / Real.log ((r : ℝ) + 2) ^ 2) := by
        field_simp [hsqrt_pos.ne', hlog_pos.ne']
        <;> ring_nf
      _ ≥ (1 / Real.sqrt (calE γ κ N)) * (1 / Real.log (2 * calE γ κ N) ^ 2) := by
        gcongr <;> try norm_num <;> try linarith
      _ = (calE γ κ N) ^ (-(1 / 2 : ℝ)) / Real.log (2 * calE γ κ N) ^ 2 := by
        rw [hinv_sqrt']
        <;> field_simp [hlogE_pos.ne']
        <;> ring_nf
  -- Show calE^(-1/2)/log(2*calE)^2 ≥ calE^(-1/10), i.e., calE^(2/5) ≥ log(2*calE)^2
  have hpow : (calE γ κ N) ^ (-(1 / 2 : ℝ)) / Real.log (2 * calE γ κ N) ^ 2 ≥ (calE γ κ N) ^ (-(1 / 10 : ℝ)) := by
    have h₁ : Real.exp 16 ≤ calE γ κ N := hE
    have h₂ : 0 < calE γ κ N := by positivity
    have h₃ : (calE γ κ N : ℝ) ^ (2 / 5 : ℝ) ≥ Real.log (2 * calE γ κ N) ^ 2 := by
      -- Use the fact that the function x ↦ x^(2/5) / log(2x)^2 is increasing for x ≥ exp(16)
      have h₄ : Real.log (calE γ κ N) ≥ 16 := by
        have h₅ : Real.log (Real.exp 16) ≤ Real.log (calE γ κ N) := Real.log_le_log (by positivity) h₁
        have h₆ : Real.log (Real.exp 16) = (16 : ℝ) := by norm_num [Real.log_exp]
        linarith
      have h₅ : (calE γ κ N : ℝ) ^ (2 / 5 : ℝ) ≥ Real.log (2 * calE γ κ N) ^ 2 := by
        -- Prove by showing the function is increasing
        have h₆ : ∀ (x : ℝ), x ≥ Real.exp 16 → x ^ (2 / 5 : ℝ) ≥ Real.log (2 * x) ^ 2 := by
          intro x hx
          have h₇ : Real.log x ≥ 16 := by
            have h₈ : Real.log (Real.exp 16) ≤ Real.log x := Real.log_le_log (by positivity) hx
            have h₉ : Real.log (Real.exp 16) = (16 : ℝ) := by norm_num [Real.log_exp]
            linarith
          have h₈ : 0 < x := by linarith [Real.exp_pos 16]
          have h₉ : 0 < Real.log x := by linarith
          have h₁₀ : 0 < Real.log (2 * x) := Real.log_pos (by linarith [Real.exp_pos 16])
          -- Use the fact that x^(2/5) / log(2x)^2 is increasing for x ≥ exp(16)
          have h₁₁ : x ^ (2 / 5 : ℝ) = Real.exp ((2 / 5 : ℝ) * Real.log x) := by
            rw [Real.rpow_def_of_pos h₈]
            <;> field_simp [Real.exp_mul, Real.exp_log h₈]
            <;> ring_nf
          rw [h₁₁]
          have h₁₂ : Real.log (2 * x) = Real.log 2 + Real.log x := by
            rw [Real.log_mul (by positivity) (by positivity)]
            <;> ring
          rw [h₁₂]
          have h₁₃ : Real.exp ((2 / 5 : ℝ) * Real.log x) ≥ (Real.log 2 + Real.log x) ^ 2 := by
            -- Prove this inequality for log x ≥ 16
            have h₁₄ : Real.log x ≥ 16 := h₇
            have h₁₅ : Real.exp ((2 / 5 : ℝ) * Real.log x) ≥ (Real.log 2 + Real.log x) ^ 2 := by
              have h₁₆ : (2 / 5 : ℝ) * Real.log x ≥ Real.log 2 + Real.log x + Real.log (Real.log 2 + Real.log x) := by
                -- This is a numerical inequality that holds for log x ≥ 16
                have h₁₇ : Real.log x ≥ 16 := h₇
                have h₁₈ : (2 / 5 : ℝ) * Real.log x ≥ Real.log 2 + Real.log x + Real.log (Real.log 2 + Real.log x) := by
                  have h₁₉ : Real.log x ≥ 16 := h₇
                  have h₂₀ : (2 / 5 : ℝ) * Real.log x = (2 / 5 : ℝ) * Real.log x := rfl
                  have h₂₁ : Real.log 2 + Real.log x + Real.log (Real.log 2 + Real.log x) ≤ (2 / 5 : ℝ) * Real.log x := by
                    have h₂₂ : Real.log x ≥ 16 := h₇
                    have h₂₃ : Real.log 2 ≥ 0 := Real.log_pos (by norm_num) |>.le
                    have h₂₄ : Real.log (Real.log 2 + Real.log x) ≤ Real.log (Real.log x + Real.log x) := by
                      apply Real.log_le_log
                      · linarith
                      · have : (Real.log 2 : ℝ) ≤ Real.log x := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
                        linarith
                    have h₂₅ : Real.log (Real.log x + Real.log x) = Real.log (2 * Real.log x) := by
                      ring_nf
                      <;> field_simp [Real.log_mul, Real.log_pow]
                      <;> ring_nf
                    have h₂₆ : Real.log (2 * Real.log x) = Real.log 2 + Real.log (Real.log x) := by
                      rw [Real.log_mul (by positivity) (by positivity)]
                      <;> ring
                    have h₂₇ : Real.log (Real.log 2 + Real.log x) ≤ Real.log 2 + Real.log (Real.log x) := by linarith
                    have h₂₈ : Real.log 2 + Real.log x + Real.log (Real.log 2 + Real.log x) ≤ Real.log 2 + Real.log x + Real.log 2 + Real.log (Real.log x) := by linarith
                    have h₂₉ : Real.log 2 + Real.log x + Real.log 2 + Real.log (Real.log x) = 2 * Real.log 2 + Real.log x + Real.log (Real.log x) := by ring
                    have h₃₀ : (2 : ℝ) * Real.log 2 + Real.log x + Real.log (Real.log x) ≤ (2 / 5 : ℝ) * Real.log x := by
                      have h₃₁ : Real.log x ≥ 16 := h₇
                      have h₃₂ : Real.log (Real.log x) ≤ Real.log x - 1 := by
                        have h₃₃ : Real.log x ≥ 16 := h₇
                        have h₃₄ : Real.log (Real.log x) ≤ Real.log x - 1 := by
                          have h₃₅ : Real.log (Real.log x) ≤ Real.log x - 1 := by
                            nlinarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < Real.log x)]
                          linarith
                        linarith
                      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
                    linarith
                  linarith
                linarith
              have h₁₉ : Real.exp ((2 / 5 : ℝ) * Real.log x) ≥ Real.exp (Real.log 2 + Real.log x + Real.log (Real.log 2 + Real.log x)) := by
                apply Real.exp_le_exp.mpr
                linarith
              have h₂₀ : Real.exp (Real.log 2 + Real.log x + Real.log (Real.log 2 + Real.log x)) = (2 : ℝ) * x * (Real.log 2 + Real.log x) := by
                have h₂₁ : Real.exp (Real.log 2 + Real.log x + Real.log (Real.log 2 + Real.log x)) = Real.exp (Real.log 2 + Real.log x) * Real.exp (Real.log (Real.log 2 + Real.log x)) := by
                  rw [Real.exp_add]
                rw [h₂₁]
                have h₂₂ : Real.exp (Real.log 2 + Real.log x) = (2 : ℝ) * x := by
                  rw [Real.exp_add, Real.exp_log (by positivity : (0 : ℝ) < (2 : ℝ)), Real.exp_log (by positivity : (0 : ℝ) < x)]
                  <;> ring_nf
                have h₂₃ : Real.exp (Real.log (Real.log 2 + Real.log x)) = Real.log 2 + Real.log x := by
                  rw [Real.exp_log (Real.log_pos (by linarith [Real.exp_pos 16]))]
                rw [h₂₂, h₂₃]
                <;> ring_nf
              have h₂₁ : (2 : ℝ) * x * (Real.log 2 + Real.log x) ≥ (Real.log 2 + Real.log x) ^ 2 := by
                have h₂₂ : (2 : ℝ) * x ≥ Real.log 2 + Real.log x := by
                  have h₂₃ : Real.log x ≥ 16 := h₇
                  have h₂₄ : (2 : ℝ) * x ≥ Real.log 2 + Real.log x := by
                    have h₂₅ : x ≥ Real.exp 16 := by linarith
                    have h₂₆ : (2 : ℝ) * x ≥ 2 * Real.exp 16 := by linarith
                    have h₂₇ : Real.log 2 + Real.log x ≤ Real.log 2 + Real.log x := le_refl _
                    have h₂₈ : Real.log 2 + Real.log x ≤ 2 * Real.exp 16 := by
                      have h₂₉ : Real.log x ≤ x := by
                        linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < x)]
                      have h₃₀ : Real.log 2 + Real.log x ≤ Real.log 2 + x := by linarith
                      have h₃₁ : (Real.log 2 : ℝ) + x ≤ 2 * Real.exp 16 := by
                        have h₃₂ : x ≥ Real.exp 16 := by linarith
                        nlinarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < Real.exp 16)]
                      linarith
                    linarith
                  linarith
                nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
              calc
                Real.exp ((2 / 5 : ℝ) * Real.log x) ≥ Real.exp (Real.log 2 + Real.log x + Real.log (Real.log 2 + Real.log x)) := h₁₉
                _ = (2 : ℝ) * x * (Real.log 2 + Real.log x) := by rw [h₂₀]
                _ ≥ (Real.log 2 + Real.log x) ^ 2 := h₂₁
            linarith
          linarith
        have h₉ : calE γ κ N ≥ Real.exp 16 := by linarith [h₁]
        have h₁₀ : (calE γ κ N : ℝ) ^ (2 / 5 : ℝ) ≥ Real.log (2 * calE γ κ N) ^ 2 := h₆ (calE γ κ N) h₉
        linarith
      linarith
    have h₄ : 0 < calE γ κ N := by positivity
    have h₅ : 0 < Real.log (2 * calE γ κ N) := Real.log_pos (by
      have h₆ : (1 : ℝ) < 2 * calE γ κ N := by
        have h₇ : Real.exp 16 ≤ calE γ κ N := hE
        have h₈ : (1 : ℝ) < Real.exp 16 := by norm_num [Real.exp_pos]
        linarith
      linarith)
    have h₆ : 0 < (calE γ κ N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos h₄ _
    have h₇ : 0 < (calE γ κ N : ℝ) ^ (-(1 / 10 : ℝ)) := Real.rpow_pos_of_pos h₄ _
    have h₈ : 0 < Real.log (2 * calE γ κ N) ^ 2 := by positivity
    -- Use the inequality (calE)^(2/5) ≥ log(2*calE)^2 to prove the desired result
    have h₉ : (calE γ κ N : ℝ) ^ (-(1 / 2 : ℝ)) / Real.log (2 * calE γ κ N) ^ 2 ≥ (calE γ κ N : ℝ) ^ (-(1 / 10 : ℝ)) := by
      have h₁₀ : (calE γ κ N : ℝ) ^ (2 / 5 : ℝ) ≥ Real.log (2 * calE γ κ N) ^ 2 := h₃
      have h₁₁ : (calE γ κ N : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / (calE γ κ N : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_neg (by positivity)]
        <;> field_simp
      have h₁₂ : (calE γ κ N : ℝ) ^ (-(1 / 10 : ℝ)) = 1 / (calE γ κ N : ℝ) ^ (1 / 10 : ℝ) := by
        rw [Real.rpow_neg (by positivity)]
        <;> field_simp
      rw [h₁₁, h₁₂]
      have h₁₃ : 1 / (calE γ κ N : ℝ) ^ (1 / 2 : ℝ) / Real.log (2 * calE γ κ N) ^ 2 ≥ 1 / (calE γ κ N : ℝ) ^ (1 / 10 : ℝ) := by
        -- Use the fact that (calE)^(2/5) ≥ log(2*calE)^2
        have h₁₄ : 0 < (calE γ κ N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos h₄ _
        have h₁₅ : 0 < (calE γ κ N : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos h₄ _
        have h₁₆ : 0 < (calE γ κ N : ℝ) ^ (1 / 2 : ℝ) * Real.log (2 * calE γ κ N) ^ 2 := by positivity
        have h₁₇ : 0 < (calE γ κ N : ℝ) ^ (1 / 10 : ℝ) * Real.log (2 * calE γ κ N) ^ 2 := by positivity
        have h₁₈ : (calE γ κ N : ℝ) ^ (1 / 2 : ℝ) * Real.log (2 * calE γ κ N) ^ 2 ≤ (calE γ κ N : ℝ) ^ (1 / 10 : ℝ) * (calE γ κ N : ℝ) ^ (2 / 5 : ℝ) := by
          have h₁₉ : Real.log (2 * calE γ κ N) ^ 2 ≤ (calE γ κ N : ℝ) ^ (2 / 5 : ℝ) := by linarith
          have h₂₀ : 0 < (calE γ κ N : ℝ) ^ (1 / 2 : ℝ) := by positivity
          nlinarith
        have h₂₁ : (calE γ κ N : ℝ) ^ (1 / 10 : ℝ) * (calE γ κ N : ℝ) ^ (2 / 5 : ℝ) = (calE γ κ N : ℝ) ^ (1 / 2 : ℝ) := by
          have h₂₂ : (1 / 10 : ℝ) + (2 / 5 : ℝ) = (1 / 2 : ℝ) := by norm_num
          have h₂₃ : (calE γ κ N : ℝ) ^ (1 / 10 : ℝ) * (calE γ κ N : ℝ) ^ (2 / 5 : ℝ) = (calE γ κ N : ℝ) ^ ((1 / 10 : ℝ) + (2 / 5 : ℝ)) := by
            rw [← Real.rpow_add (by positivity : (0 : ℝ) < calE γ κ N)]
          rw [h₂₃, h₂₂]
          <;> norm_num
        have h₂₂ : (calE γ κ N : ℝ) ^ (1 / 2 : ℝ) * Real.log (2 * calE γ κ N) ^ 2 ≤ (calE γ κ N : ℝ) ^ (1 / 2 : ℝ) := by linarith
        have h₂₃ : 1 / (calE γ κ N : ℝ) ^ (1 / 2 : ℝ) / Real.log (2 * calE γ κ N) ^ 2 ≥ 1 / (calE γ κ N : ℝ) ^ (1 / 10 : ℝ) := by
          calc
            1 / (calE γ κ N : ℝ) ^ (1 / 2 : ℝ) / Real.log (2 * calE γ κ N) ^ 2 = 1 / ((calE γ κ N : ℝ) ^ (1 / 2 : ℝ) * Real.log (2 * calE γ κ N) ^ 2) := by
              field_simp
              <;> ring_nf
            _ ≥ 1 / (calE γ κ N : ℝ) ^ (1 / 2 : ℝ) := by
              apply one_div_le_one_div_of_le
              · positivity
              · linarith
            _ = (calE γ κ N : ℝ) ^ (-(1 / 2 : ℝ)) := by
              rw [Real.rpow_neg (by positivity)]
              <;> field_simp
            _ ≥ 1 / (calE γ κ N : ℝ) ^ (1 / 10 : ℝ) := by
              have h₂₄ : (calE γ κ N : ℝ) ^ (-(1 / 2 : ℝ)) ≥ 1 / (calE γ κ N : ℝ) ^ (1 / 10 : ℝ) := by
                have h₂₅ : (calE γ κ N : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / (calE γ κ N : ℝ) ^ (1 / 2 : ℝ) := by
                  rw [Real.rpow_neg (by positivity)]
                  <;> field_simp
                rw [h₂₅]
                have h₂₆ : 1 / (calE γ κ N : ℝ) ^ (1 / 2 : ℝ) ≥ 1 / (calE γ κ N : ℝ) ^ (1 / 10 : ℝ) := by
                  apply one_div_le_one_div_of_le
                  · positivity
                  · have h₂₇ : (calE γ κ N : ℝ) ^ (1 / 2 : ℝ) ≤ (calE γ κ N : ℝ) ^ (1 / 10 : ℝ) := by
                      apply Real.rpow_le_rpow_of_exponent_le
                      · linarith
                      · norm_num
                      · linarith
                    linarith
                linarith
              linarith
            _ = 1 / (calE γ κ N : ℝ) ^ (1 / 10 : ℝ) := by rfl
        linarith
      linarith
    linarith
  -- Final step
  calc
    (calE γ κ N) ^ (-(1 / 10 : ℝ)) ≤ (calE γ κ N) ^ (-(1 / 2 : ℝ)) / Real.log (2 * calE γ κ N) ^ 2 := by
      linarith
    _ ≤ 1 / (Real.sqrt r * Real.log ((r : ℝ) + 2) ^ 2) := by
      linarith

/-- Proved helper: the branch of `SelectedRealZero` without an exceptional zero has `r = 1`,
which is incompatible with a nontrivial common divisor. -/
theorem near_zero_selected_exceptional (a P : ℝ) (r : ℕ) (m : ℤ)
    (hs : SelectedRealZero a P r) (hg : 1 < Int.gcd m r) :
    ∃ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
      0 < β ∧ 1 - a / Real.log P ≤ β ∧ β < 1 ∧ χ.LFunction β = 0 := by
  rcases hs with ⟨hr, _⟩ | ⟨i, χ, β, h1, h2, h3, h4, h5, h6, h7, _⟩
  · subst hr
    exfalso
    have : Int.gcd m ((1 : ℕ) : ℤ) = 1 := by simp
    omega
  · exact ⟨i, χ, β, h1, h2, h3, h4, h5, h6, h7⟩

/-- Assembly: verbatim statement of `leaf_near_zero_even_index`, proved from the leaves. -/
theorem leaf_near_zero_even_index_feed (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
  obtain ⟨δ₀, hδ₀, H⟩ := leaf_near_zero_even_main_term γ h1 h2 a ha
  obtain ⟨c₂, hc₂, hpage⟩ := leaf_near_zero_page_bound
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδlt
  obtain ⟨κ₀, hκ₀, K⟩ := H δ hδ hδlt
  refine ⟨κ₀, hκ₀, ?_⟩
  intro κ hκ hκle
  obtain ⟨c₁, A, hc₁, hA, N₁, L⟩ := K κ hκ hκle
  obtain ⟨N₂, hpow⟩ := leaf_near_zero_conductor_power γ h1 h2 κ hκ
  refine ⟨c₁ * c₂, A, mul_pos hc₁ hc₂, hA, max N₁ N₂, ?_⟩
  intro N hN r hr hrP hs n hn heven hm hgcd hnop hrE
  obtain ⟨hN₁, hN₂⟩ := max_le_iff.mp hN
  obtain ⟨i, χ, β, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ :=
    near_zero_selected_exceptional a _ r _ hs hgcd
  have hmain := L N hN₁ r hr hrP hs i χ β hp1 hp2 hp3 hp4 hp5 hp6 hp7 n hn heven hm hgcd hnop hrE
  have hβ := hpage r i χ β hp1 hp2 hp3 hp4 hp6 hp7
  have hE := hpow N hN₂ r hr hrE
  set D := Real.sqrt r * Real.log ((r : ℝ) + 2) ^ 2
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hβ' : c₂ * (1 / D) ≤ 1 - β := by rw [mul_one_div]; exact hβ
  have k1 : c₁ * c₂ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
      c₁ * c₂ * F γ N * (1 / D) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have k2 : c₁ * F γ N * (c₂ * (1 / D)) ≤ c₁ * F γ N * (1 - β) :=
    mul_le_mul_of_nonneg_left hβ' (by positivity)
  calc c₁ * c₂ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))
      ≤ c₁ * c₂ * F γ N * (1 / D) := k1
    _ = c₁ * F γ N * (c₂ * (1 / D)) := by ring
    _ ≤ c₁ * F γ N * (1 - β) := k2
    _ = c₁ * (1 - β) * F γ N := by ring
    _ ≤ _ := hmain

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
