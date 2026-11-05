/-
P0093 pages 157 to 159. Near and far decomposition of the Mellin square bound.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357k

namespace LeanLab.Linnik1951

/-- P0093 page 159 before equation 5.1. Character weighting preserves the
uniform geometric majorant of the damped prime series. -/
theorem continuous_character_prime357 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 1 ≤ N) : Continuous (characterPrime280 χ N) := by
  unfold characterPrime280
  apply continuous_tsum
    (u := fun p : Nat.Primes => Real.exp (-((p : ℕ) : ℝ) / N))
  · intro p
    fun_prop
  · exact (damping_summable111 N hN).comp_injective Nat.Primes.coe_nat_injective
  · intro p α
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (χ.norm_le_one _)

/-- LEAF. P0093 page 158 equation 4.8 on both sides of zero, applied to
A_chi using page 159 equation 5.1. The central interval has radius 4 over N.
This is the local square bound, not the whole arc estimate. -/
theorem mellin_near357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in -(4 / (N : ℝ))..(4 / (N : ℝ)),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 := by
  sorry

/-- LEAF. P0093 page 158 equation 4.7 and N0 equal to N over q tau times
log cubed N, applied through page 159 equation 5.1. This is the positive
outer interval estimate with logarithmic exponent 10. -/
theorem mellin_positive_far357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in (4 / (N : ℝ))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 10 := by
  sorry

/-- LEAF. P0093 page 158 last sentence after equation 4.8. The negative
outer interval is treated analogously to equation 4.7. This estimate is
restricted to that interval and retains logarithmic exponent 10. -/
theorem mellin_negative_far357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..-(4 / (N : ℝ)),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 10 := by
  obtain ⟨B, hB, N0, hpos⟩ := mellin_positive_far357 hG
  refine ⟨B, hB, N0, ?_⟩
  intro N hN q hq hqt χ hχ
  have hstar : star χ ≠ 1 := by
    intro h
    apply hχ
    simpa only [star_star, star_one] using congrArg star h
  rw [← intervalIntegral.integral_comp_neg]
  simp_rw [character_norm_reflect357]
  exact hpos N hN q hq hqt (star χ) hstar

/-- P0093 page 159 equation 5.2. The exact mellin_bound280 conclusion
follows by interval additivity and enlargement of logarithmic powers.
CONDITIONAL on the three local Mellin leaves. -/
theorem mellin_bound_decomposed357 (hG : LeanLab.DERZ1997.GRH) : MellinBound280 := by
  obtain ⟨B0, hB0, N0, h0⟩ := mellin_near357 hG
  obtain ⟨Bp, hBp, Np, hp⟩ := mellin_positive_far357 hG
  obtain ⟨Bm, hBm, Nm, hm⟩ := mellin_negative_far357 hG
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨Bm + B0 + Bp, by positivity, max 1 (max L (max N0 (max Np Nm))), ?_⟩
  intro N hN q hq hqt χ hχ
  have h1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hLN : L < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have h0N : N0 < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hpN : Np < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hN
  have hmN : Nm < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hN
  have hlog : 1 ≤ Real.log N := by
    have hLNreal : (L : ℝ) < (N : ℝ) := by exact_mod_cast hLN
    have hh := Real.log_le_log (Real.exp_pos 1) (hL.trans hLNreal).le
    simpa only [Real.log_exp] using hh
  have h6 : Real.log N ^ 6 ≤ Real.log N ^ 13 :=
    pow_le_pow_right₀ hlog (by norm_num)
  have h10 : Real.log N ^ 10 ≤ Real.log N ^ 13 :=
    pow_le_pow_right₀ hlog (by norm_num)
  have hcont : Continuous (fun α : ℝ => ‖characterPrime280 χ N α‖ ^ 2) :=
    (continuous_character_prime357 χ N (by omega)).norm.pow 2
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (-(4 / (N : ℝ))))
    (hcont.intervalIntegrable (-(4 / (N : ℝ))) (4 / (N : ℝ)))
  have hadd' := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (4 / (N : ℝ)))
    (hcont.intervalIntegrable (4 / (N : ℝ)) (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))))
  rw [← hadd', ← hadd]
  have b0 := (h0 N h0N q hq hqt χ hχ).trans
    (mul_le_mul_of_nonneg_left h6 (by positivity))
  have bp := (hp N hpN q hq hqt χ hχ).trans
    (mul_le_mul_of_nonneg_left h10 (by positivity))
  have bm := (hm N hmN q hq hqt χ hχ).trans
    (mul_le_mul_of_nonneg_left h10 (by positivity))
  calc
    _ ≤ Bm * N / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 +
        B0 * N / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 +
        Bp * N / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 :=
      add_le_add (add_le_add bm b0) bp
    _ = _ := by ring

end LeanLab.Linnik1951
