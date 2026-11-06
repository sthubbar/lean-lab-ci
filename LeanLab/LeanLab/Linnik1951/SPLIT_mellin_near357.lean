/-
Split of the central-interval Mellin square estimate `mellin_near357` into four
steps. Nothing here changes the statement: `mellin_near357_split` states it
character for character and proves it from the four OPEN leaves below, which
record, in order, (1) the interval-length reduction, (2) the pointwise bound on
the positive side of zero, (3) the pointwise bound on the negative side of zero
and (4) the choice of the constant together with the logarithmic bookkeeping.
-/
import LeanLab.Linnik1951.Decomp357a

namespace LeanLab.Linnik1951

/-- LEAF. Step 1 of 4: interval arithmetic only. The square norm of the damped
character prime sum is continuous for positive N, so if it is at most M at every
point of the interval from u to v with u at most v, its integral over that
interval is at most M times the length v minus u. This is the step that turns an
integral estimate into a pointwise estimate and back; it carries no character
information. -/
theorem near_half_integral_le_sup357 {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ)
    (M u v : ℝ) (hN : 1 ≤ N) (huv : u ≤ v)
    (hM : ∀ α : ℝ, α ∈ Set.Icc u v → ‖characterPrime280 χ N α‖ ^ 2 ≤ M) :
    (∫ α in u..v, ‖characterPrime280 χ N α‖ ^ 2) ≤ M * (v - u) := by
  have hcont : Continuous (fun α : ℝ => ‖characterPrime280 χ N α‖ ^ 2) :=
    (continuous_character_prime357 χ N hN).norm.pow 2
  calc (∫ α in u..v, ‖characterPrime280 χ N α‖ ^ 2)
      ≤ (∫ _ in u..v, M) :=
        intervalIntegral.integral_mono_on huv (hcont.intervalIntegrable _ _)
          (intervalIntegrable_const) (fun α hα => hM α hα)
    _ = M * (v - u) := by rw [intervalIntegral.integral_const]; ring

/-- LEAF. Step 2 of 4: the pointwise bound on the positive side of zero. There
is a fixed positive constant C such that for every large N, every modulus q with
1 at most q at most N to the one seventh, and every nonprincipal character mod q,
the square norm of the damped character prime sum at a phase between 0 and 4 over
N is at most C times N over q times log N to the fifth. This is the local
uniform bound; the integral over the short interval comes later, from step 1. -/
theorem near_positive_sup357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ α : ℝ, 0 ≤ α → α ≤ 4 / (N : ℝ) →
          ‖characterPrime280 χ N α‖ ^ 2 ≤ C * (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := by
  sorry

/-- LEAF. Step 3 of 4: the pointwise bound on the negative side of zero. Same
exponent and same shape as step 2, on the reflected interval from minus 4 over N
to 0. The reflection of the phase conjugates the character and replaces it by its
conjugate character, which is again nonprincipal, so this side has its own
constant; it is kept as a separate leaf because it is a separate interval. -/
theorem near_negative_sup357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ α : ℝ, -(4 / (N : ℝ)) ≤ α →
          α ≤ 0 →
          ‖characterPrime280 χ N α‖ ^ 2 ≤ C * (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := by
  obtain ⟨C, hC, N0, h⟩ := near_positive_sup357 hG
  refine ⟨C, hC, N0, ?_⟩
  intro N hN q hq hqt χ hχ α hα1 hα2
  have hstar : star χ ≠ 1 := by
    intro hs
    apply hχ
    ext x
    have hx : star (χ x) = 1 := by
      rw [← MulChar.star_apply, hs]
      simp
    rw [← star_star (χ x), hx]
    simp
  have hb := h N hN q hq hqt (star χ) hstar (-α) (by linarith) (by linarith)
  have hrefl := character_norm_reflect357 χ N (-α)
  rw [neg_neg] at hrefl
  rw [hrefl]
  exact hb

/-- LEAF. Step 4 of 4: the constant and the logarithmic bookkeeping. For every
positive C there is N0 such that for every N beyond N0 and every modulus q at
least one with q at most N to the one seventh, eight C times log N to the fifth
divided by q is at most eight C times N over q times N to the one seventh times
log N to the sixth. The content is the single real inequality: for N at least
two, N to the six sevenths times log N is at least one. -/
theorem near_constant_selection357 (C : ℝ) (hC : 0 < C) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        (8 : ℝ) * C * Real.log N ^ 5 / (q : ℝ) ≤
          (8 * C) * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 := by
  refine ⟨2, ?_⟩
  intro N hN q hq hqt
  have hN3 : 3 ≤ N := by omega
  have hN3r : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h8C : (0 : ℝ) < 8 * C := by positivity
  have hlog1 : (1 : ℝ) < Real.log N := by
    refine lt_of_lt_of_le ?_ (Real.log_le_log (by norm_num) hN3r)
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    linarith [Real.exp_one_lt_d9]
  have hpow1 : (1 : ℝ) ≤ (N : ℝ) ^ (6 / 7 : ℝ) := by
    have h : (1 : ℝ) ^ (6 / 7 : ℝ) ≤ (N : ℝ) ^ (6 / 7 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hN1 (by norm_num)
    simpa using h
  have hkey : (1 : ℝ) ≤ (N : ℝ) ^ (6 / 7 : ℝ) * Real.log N := by
    have := mul_le_mul hpow1 hlog1.le (by norm_num : (0 : ℝ) ≤ 1)
      (Real.rpow_nonneg hNpos.le _)
    linarith
  have hlogpos : (0 : ℝ) < Real.log N := lt_trans (by norm_num) hlog1
  have hlog5 : (0 : ℝ) ≤ Real.log N ^ 5 := pow_nonneg hlogpos.le 5
  have hexp : (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) = (N : ℝ) ^ (6 / 7 : ℝ) := by
    have e1 : (1 : ℝ) - 1 / 7 = 6 / 7 := by norm_num
    calc (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ)
        = (N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) - 1 / 7) := (Real.rpow_sub hNpos 1 (1 / 7)).symm
      _ = (N : ℝ) ^ (6 / 7 : ℝ) := by rw [e1]
  have hmain : Real.log N ^ 5 ≤ (N : ℝ) ^ (6 / 7 : ℝ) * Real.log N ^ 6 := by
    have h6 : Real.log N ^ 6 = Real.log N * Real.log N ^ 5 := by ring
    rw [h6, ← mul_assoc]
    exact le_mul_of_one_le_left hlog5 hkey
  have hdiv : (8 : ℝ) * C * Real.log N ^ 5 / (q : ℝ) ≤
      (8 * C) * ((N : ℝ) ^ (6 / 7 : ℝ) * Real.log N ^ 6) / (q : ℝ) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hqpos)
    nlinarith [hmain]
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hpw : (N : ℝ) ^ (1 / 7 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hNpos _)
  calc (8 : ℝ) * C * Real.log N ^ 5 / (q : ℝ)
      ≤ (8 * C) * ((N : ℝ) ^ (6 / 7 : ℝ) * Real.log N ^ 6) / (q : ℝ) := hdiv
    _ = (8 * C) * ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 6) / (q : ℝ) := by
        rw [← hexp]
    _ = (8 * C) * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 := by
        field_simp [hqne, hpw]

/-- Assembly of `mellin_near357` from the four leaves above: split the central
interval at zero, bound each half through the two pointwise leaves and the
interval-length leaf, and absorb the factor N to the six sevenths through the
constant leaf. No step uses `mellin_near357` itself. -/
theorem mellin_near357_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in -(4 / (N : ℝ))..(4 / (N : ℝ)),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 := by
  obtain ⟨C, hC, Np, hp⟩ := near_positive_sup357 hG
  obtain ⟨C', hC', Nm, hm⟩ := near_negative_sup357 hG
  have hCmax : 0 < max C C' := lt_of_lt_of_le hC (le_max_left _ _)
  obtain ⟨Nc, hc⟩ := near_constant_selection357 (max C C') hCmax
  refine ⟨8 * max C C', by positivity, max 1 (max Np (max Nm Nc)), ?_⟩
  intro N hN q hq hqt χ hχ
  have h1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNpN : Np < N :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNmN : Nm < N :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _))) hN
  have hNcN : Nc < N :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _))) hN
  have hN1 : 1 ≤ N := le_of_lt h1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt h1)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hfac : (0 : ℝ) ≤ (N : ℝ) / (q : ℝ) * Real.log N ^ 5 :=
    mul_nonneg (div_nonneg (le_of_lt hNpos) (le_of_lt hqpos)) (pow_nonneg hlogN 5)
  have hcont : Continuous (fun α : ℝ => ‖characterPrime280 χ N α‖ ^ 2) :=
    (continuous_character_prime357 χ N hN1).norm.pow 2
  have h4 : (0 : ℝ) < 4 / (N : ℝ) := by positivity
  have hposHalf :
      (∫ α in (0 : ℝ)..(4 / (N : ℝ)), ‖characterPrime280 χ N α‖ ^ 2) ≤
        max C C' * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) * (4 / (N : ℝ) - 0) := by
    refine near_half_integral_le_sup357 χ N
      (max C C' * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5)) 0 (4 / (N : ℝ)) hN1
      (le_of_lt h4) ?_
    intro α hα
    have hb := hp N hNpN q hq hqt χ hχ α hα.1 hα.2
    calc ‖characterPrime280 χ N α‖ ^ 2 ≤ C * (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := hb
      _ = C * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by ring
      _ ≤ max C C' * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hfac
  have hnegHalf :
      (∫ α in (-(4 / (N : ℝ)))..(0 : ℝ), ‖characterPrime280 χ N α‖ ^ 2) ≤
        max C C' * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) * (0 - -(4 / (N : ℝ))) := by
    refine near_half_integral_le_sup357 χ N
      (max C C' * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5)) (-(4 / (N : ℝ))) 0 hN1
      (by linarith) ?_
    intro α hα
    have hb := hm N hNmN q hq hqt χ hχ α hα.1 hα.2
    calc ‖characterPrime280 χ N α‖ ^ 2 ≤ C' * (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := hb
      _ = C' * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by ring
      _ ≤ max C C' * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hfac
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable (-(4 / (N : ℝ))) 0)
    (hcont.intervalIntegrable (0 : ℝ) (4 / (N : ℝ)))
  rw [← hadd]
  have harith : max C C' * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) * (0 - -(4 / (N : ℝ))) +
      max C C' * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) * (4 / (N : ℝ) - 0) =
      (8 : ℝ) * max C C' * Real.log N ^ 5 / (q : ℝ) := by
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
    field_simp
    ring
  calc (∫ α in (-(4 / (N : ℝ)))..(0 : ℝ), ‖characterPrime280 χ N α‖ ^ 2) +
        (∫ α in (0 : ℝ)..(4 / (N : ℝ)), ‖characterPrime280 χ N α‖ ^ 2)
      ≤ max C C' * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) * (0 - -(4 / (N : ℝ))) +
          max C C' * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) * (4 / (N : ℝ) - 0) :=
        add_le_add hnegHalf hposHalf
    _ = (8 : ℝ) * max C C' * Real.log N ^ 5 / (q : ℝ) := harith
    _ ≤ (8 * max C C') * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 :=
        hc N hNcN q hq hqt

end LeanLab.Linnik1951
