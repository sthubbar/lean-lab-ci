/-
ROUTE for `oscillatory_zero_modes508`, part four: one zero mode at large frequency, with the
height of the zero retained, and the assembly of the sealed estimate.
Source: P0029 page 15 display 4.6 and pages 11 and 12 displays 3.5 through 3.7.
The existing leaf `zero_mode_large_frequency508` has no height restriction and the constant 8;
the route notes record why it is SUSPECTED FALSE. This file does not use it.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.RouteTwist508
import LeanLab.BhowmikGrimmelt2026.SPLIT_oscillatory_zero_modes508

namespace LeanLab.BhowmikGrimmelt2026

/-- The additive exponential of `n * (β - k)` equals that of `n * β` for natural `n` and
integer `k`. -/
theorem ee_nat_mul_sub_int_aux508 (n : ℕ) (β : ℝ) (k : ℤ) :
    ee ((n : ℝ) * (β - (k : ℝ))) = ee ((n : ℝ) * β) := by
  have h1 : ee (((n : ℤ) * k : ℤ) : ℝ) = 1 := by
    unfold ee
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((((n : ℤ) * k : ℤ) : ℝ) : ℂ) =
      (((n : ℤ) * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
  have h2 : (n : ℝ) * β = (n : ℝ) * (β - (k : ℝ)) + (((n : ℤ) * k : ℤ) : ℝ) := by
    push_cast; ring
  rw [h2, ee_add150, h1, mul_one]

/-- The norm of a natural number raised to a complex power of positive real part. -/
theorem norm_natCast_cpow_aux508 {ρ : ℂ} (hρ0 : 0 < ρ.re) (n : ℕ) :
    ‖(n : ℂ) ^ ρ‖ = (n : ℝ) ^ ρ.re := by
  have hρne : ρ ≠ 0 := by
    intro h
    rw [h] at hρ0
    simp at hρ0
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Nat.cast_zero, Complex.zero_cpow hρne]
    simpa using (Real.zero_rpow (ne_of_gt hρ0)).symm
  · rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]

/-- P0029 page 15 display 4.6, the Abel expression of one zero mode with the phase
increment `e(β) - 1` factored out. -/
theorem zero_mode_abel_form508 {ρ : ℂ} (hρ : ρ ≠ 0) (X : ℕ) (β : ℝ) :
    (X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)) =
      ((X : ℂ) ^ ρ * ee ((X : ℝ) * β) -
        (ee β - 1) * ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β)) / ρ := by
  have hsum : ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
        (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)) =
      (ee β - 1) * (∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β)) / ρ := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (((n + 1 : ℕ) : ℝ) * β) = (n : ℝ) * β + β by push_cast; ring, ee_add150]
    ring
  rw [hsum]
  ring

/-- P0029 page 15 display 4.6, one retained zero mode in the large frequency regime
`1 ≤ |β| X`, for a zero of height `|Im ρ| ≤ 2X`. The frequency is reduced modulo one to
`|β'| ≤ 1 / 2`; if `|β'| X ≤ 1` the trivial bound is used, otherwise
`log_power_twist_sum508`. -/
theorem zero_mode_large_frequency_height508 {Θ : ℝ} (hΘ1 : 1 / 2 ≤ Θ) {X : ℕ} (hX : 1 ≤ X)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρΘ : ρ.re ≤ Θ) (hρT : |ρ.im| ≤ 2 * (X : ℝ)) {β : ℝ}
    (hβ : 1 ≤ |β| * (X : ℝ)) :
    ‖(X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ ≤
      4000 * (X : ℝ) ^ Θ / ‖ρ‖ * Real.sqrt (|β| * (X : ℝ)) := by
  have hρne : ρ ≠ 0 := by
    intro h
    rw [h] at hρ0
    simp at hρ0
  have hd : (0 : ℝ) < ‖ρ‖ := norm_pos_iff.mpr hρne
  have hXr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXσΘ : (X : ℝ) ^ ρ.re ≤ (X : ℝ) ^ Θ := Real.rpow_le_rpow_of_exponent_le hXr hρΘ
  have hXσ0 : 0 ≤ (X : ℝ) ^ ρ.re := Real.rpow_nonneg (by linarith) _
  have hXΘ0 : 0 ≤ (X : ℝ) ^ Θ := Real.rpow_nonneg (by linarith) _
  obtain ⟨S, hSd⟩ : ∃ S : ℝ, S = Real.sqrt (|β| * (X : ℝ)) := ⟨_, rfl⟩
  have hS1 : 1 ≤ S := by
    rw [hSd]; exact Real.le_sqrt_of_sq_le (by linarith)
  obtain ⟨k, hkd⟩ : ∃ k : ℤ, k = round β := ⟨_, rfl⟩
  obtain ⟨β', hβ'd⟩ : ∃ β' : ℝ, β' = β - (k : ℝ) := ⟨_, rfl⟩
  have hb2 : |β'| ≤ 1 / 2 := by rw [hβ'd, hkd]; exact abs_sub_round β
  have hbβ : |β'| ≤ |β| := by
    have := round_le β 0
    rw [hβ'd, hkd]
    simpa using this
  have hee : ee β = ee β' := by
    have := ee_nat_mul_sub_int_aux508 1 β k
    simp only [Nat.cast_one, one_mul] at this
    rw [hβ'd, this]
  have hA : ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β) =
      ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β') := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hβ'd, ee_nat_mul_sub_int_aux508]
  have hstep : ‖ee β - 1‖ ≤ 2 * Real.pi * |β'| := by
    rw [hee]; exact norm_ee_sub_one_le502 β'
  have hπ : Real.pi < 3.15 := Real.pi_lt_d2
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have hb0 : 0 ≤ |β'| := abs_nonneg _
  have hprod : ‖ee β - 1‖ * ‖∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β)‖ ≤
      3200 * (X : ℝ) ^ Θ * S := by
    rcases le_or_gt (|β'| * (X : ℝ)) 1 with hs | hl
    · have hAle : ‖∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β)‖ ≤
          (X : ℝ) * (X : ℝ) ^ ρ.re := by
        refine (norm_sum_le _ _).trans ?_
        have : ∀ n ∈ Finset.range X, ‖(n : ℂ) ^ ρ * ee ((n : ℝ) * β)‖ ≤ (X : ℝ) ^ ρ.re := by
          intro n hn
          rw [norm_mul, norm_ee150, mul_one, norm_natCast_cpow_aux508 hρ0]
          exact Real.rpow_le_rpow (Nat.cast_nonneg n)
            (by exact_mod_cast (Finset.mem_range.mp hn).le) hρ0.le
        refine (Finset.sum_le_sum this).trans ?_
        simp
      calc _ ≤ 2 * Real.pi * |β'| * ((X : ℝ) * (X : ℝ) ^ ρ.re) :=
            mul_le_mul hstep hAle (norm_nonneg _) (by positivity)
        _ = 2 * Real.pi * (|β'| * (X : ℝ)) * (X : ℝ) ^ ρ.re := by ring
        _ ≤ 2 * Real.pi * 1 * (X : ℝ) ^ Θ :=
            mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) hXσΘ hXσ0
              (by positivity)
        _ ≤ 3200 * (X : ℝ) ^ Θ * 1 := by nlinarith
        _ ≤ 3200 * (X : ℝ) ^ Θ * S := mul_le_mul_of_nonneg_left hS1 (by positivity)
    · have hbpos : 0 < |β'| := by
        rcases hb0.lt_or_eq with h | h
        · exact h
        · rw [← h] at hl; linarith
      have hT := log_power_twist_sum508 hΘ1 hX hρ0 hρΘ hρT (β := β') hl.le hb2
      rw [← hA] at hT
      have hsq : |β'| * Real.sqrt ((X : ℝ) / |β'|) ≤ S := by
        rw [hSd]
        apply Real.le_sqrt_of_sq_le
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        have : |β'| ^ 2 * ((X : ℝ) / |β'|) = |β'| * (X : ℝ) := by field_simp
        rw [this]
        exact mul_le_mul_of_nonneg_right hbβ (by linarith)
      calc _ ≤ 2 * Real.pi * |β'| * (500 * (X : ℝ) ^ Θ * Real.sqrt ((X : ℝ) / |β'|)) :=
            mul_le_mul hstep hT (norm_nonneg _) (by positivity)
        _ = 1000 * Real.pi * (X : ℝ) ^ Θ * (|β'| * Real.sqrt ((X : ℝ) / |β'|)) := by ring
        _ ≤ 1000 * Real.pi * (X : ℝ) ^ Θ * S :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ ≤ 3200 * (X : ℝ) ^ Θ * S := by
            have : 0 ≤ (X : ℝ) ^ Θ * S := mul_nonneg hXΘ0 (by linarith)
            nlinarith
  have hnum : ‖(X : ℂ) ^ ρ * ee ((X : ℝ) * β) -
      (ee β - 1) * ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β)‖ ≤
      4000 * (X : ℝ) ^ Θ * S := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_ee150, mul_one, norm_natCast_cpow_aux508 hρ0, norm_mul]
    have : (X : ℝ) ^ Θ ≤ (X : ℝ) ^ Θ * S := le_mul_of_one_le_right hXΘ0 hS1
    linarith
  rw [zero_mode_abel_form508 hρne, norm_div, ← hSd]
  calc _ ≤ 4000 * (X : ℝ) ^ Θ * S / ‖ρ‖ := (div_le_div_iff_of_pos_right hd).mpr hnum
    _ = 4000 * (X : ℝ) ^ Θ / ‖ρ‖ * S := by ring

/-- P0029 pages 11 and 12 displays 3.5 through 3.7 and page 15 display 4.6, the sealed sharp
oscillatory zero mode estimate assembled along the route: the small frequency mode bound, the
large frequency mode bound with the height of the zero retained, and the reciprocal zero count.
CONDITIONAL on `zero_reciprocal_multiplicity508`, which stays a cited count, and on the leaves
of the route files still open. It does not use `zero_mode_large_frequency508`. -/
theorem oscillatory_zero_modes508_route (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∀ (q : ℕ) [NeZero q], q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q,
      ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∀ β : ℝ, |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X) →
          ‖zeroTwist508 χ Z X β‖ ≤
            C * (X : ℝ) ^ (Θ + ε) * Real.sqrt (1 + |β| * X) := by
  intro ε hε
  obtain ⟨K, hK0, hK⟩ := zero_reciprocal_multiplicity508 ε hε
  refine ⟨4000 * K, by positivity, ?_⟩
  intro X hX2 q _ hqQ χ T hT Z hZset β hβ
  have hX1 : 1 ≤ X := by omega
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hΘ1 : 1 / 2 ≤ Θ := zeroBound_lower150 hZ
  have hS1 : (1 : ℝ) ≤ Real.sqrt (1 + |β| * (X : ℝ)) :=
    Real.le_sqrt_of_sq_le (by nlinarith [mul_nonneg (abs_nonneg β) (Nat.cast_nonneg X)])
  have hKsum := hK X hX2 q hqQ χ T hT Z hZset
  have hterm : ∀ ρ ∈ Z,
      ‖(mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)))‖ ≤
      (mult χ ρ : ℝ) *
        (4000 * (X : ℝ) ^ Θ / ‖ρ‖ * Real.sqrt (1 + |β| * (X : ℝ))) := by
    intro ρ hρ
    obtain ⟨hz, h0, h1, him⟩ := (hZset ρ).mp hρ
    have hρT : |ρ.im| ≤ 2 * (X : ℝ) := him.trans hT.2
    have hρΘ : ρ.re ≤ Θ := hZ q χ ρ hz h0 h1
    have hnn : (0 : ℝ) ≤ 4000 * (X : ℝ) ^ Θ / ‖ρ‖ := by positivity
    have hmode : ‖(X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ ≤
        4000 * (X : ℝ) ^ Θ / ‖ρ‖ * Real.sqrt (1 + |β| * (X : ℝ)) := by
      rcases le_total (|β| * (X : ℝ)) 1 with hs | hl
      · refine (zero_mode_small_frequency508 hΘ1 hX1 h0 hρΘ hs).trans ?_
        have h8 : 8 * (X : ℝ) ^ Θ / ‖ρ‖ ≤ 4000 * (X : ℝ) ^ Θ / ‖ρ‖ := by
          have hp : (0 : ℝ) ≤ (X : ℝ) ^ Θ / ‖ρ‖ := by positivity
          have e1 : 8 * (X : ℝ) ^ Θ / ‖ρ‖ = 8 * ((X : ℝ) ^ Θ / ‖ρ‖) := by ring
          have e2 : 4000 * (X : ℝ) ^ Θ / ‖ρ‖ = 4000 * ((X : ℝ) ^ Θ / ‖ρ‖) := by ring
          rw [e1, e2]; linarith
        nlinarith [hnn, hS1, h8]
      · refine (zero_mode_large_frequency_height508 hΘ1 hX1 h0 hρΘ hρT hl).trans ?_
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (by linarith)) hnn
    calc ‖(mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
          ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
            (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)))‖
        = (mult χ ρ : ℝ) * ‖(X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
            ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
              (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ := by
          rw [norm_mul, Complex.norm_natCast]
      _ ≤ (mult χ ρ : ℝ) *
            (4000 * (X : ℝ) ^ Θ / ‖ρ‖ * Real.sqrt (1 + |β| * (X : ℝ))) :=
          mul_le_mul_of_nonneg_left hmode (by positivity)
  unfold zeroTwist508
  calc ‖∑ ρ ∈ Z, (mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)))‖
      ≤ ∑ ρ ∈ Z, ‖(mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
          ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
            (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)))‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ Z, (mult χ ρ : ℝ) *
          (4000 * (X : ℝ) ^ Θ / ‖ρ‖ * Real.sqrt (1 + |β| * (X : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = 4000 * (X : ℝ) ^ Θ * Real.sqrt (1 + |β| * (X : ℝ)) *
          ∑ ρ ∈ Z, (mult χ ρ : ℝ) / ‖ρ‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ hρ
        ring
    _ ≤ 4000 * (X : ℝ) ^ Θ * Real.sqrt (1 + |β| * (X : ℝ)) * (K * (X : ℝ) ^ ε) :=
        mul_le_mul_of_nonneg_left hKsum (by positivity)
    _ = 4000 * K * (X : ℝ) ^ (Θ + ε) * Real.sqrt (1 + |β| * (X : ℝ)) := by
        rw [Real.rpow_add hXp]
        ring

end LeanLab.BhowmikGrimmelt2026
