/-
Unit U-1622. Source faithful re-cut of the doubled system mass of P0093.
Replaces the false step in SPLIT_exceptional_prime_mass357. The denominator range of
equation 9.1 stays q at least Q equal to N to one tenth, so the major arc mass stays out.
The original scan of pages 155, 159, 160 and 166 controls the statements.
AI wrote the Lean code. Binary Goldbach is open.

Derives the exact type of doubled_system_mass376 from the character expansion of one
system, the trivial principal mass, a totient bound, and the Mellin bound at radius
2 over q tau from SPLIT1622_mellin.
-/
import LeanLab.Linnik1951.Decomp376c
import LeanLab.Linnik1951.SPLIT1622_mellin

namespace LeanLab.Linnik1951

open MeasureTheory Filter Asymptotics

/-- LEAF. P0093 page 155 equation 2.3, page 156 Lemma 1, and the orthogonality
chain on page 160 before equation 5.4, for the square norm. Fix q at least 2. The
square integral of S over F_q clipped to the unit interval is at most B over phi of q
times the principal integral plus q times the sum of the nonprincipal integrals
over the interval of radius r equal to 2 over q tau, plus the error of size
phi of q times r times ln squared q from equation 2.3. Unconditional, for any tau
at least 4 and any N at least 1. -/
theorem doubled_system_characters1622 :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q] (τ : ℝ), 1 ≤ N → 2 ≤ q → 4 ≤ τ →
      (∫ α in arcSystem111 q τ ∩ Set.Icc 0 1, ‖primeFourier111 N α‖ ^ 2) ≤
        B / (q.totient : ℝ) *
          ((∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
              ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
            (q : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
                ‖characterPrime280 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * (2 / ((q : ℝ) * τ)) * Real.log q ^ 2 := by
  sorry

/-- LEAF. P0093 page 159 trivial estimate before equation 5.3. The square integral
of the principal character sum over an interval of radius r at most 1/2 is at most
B N, by the full period. Unconditional. -/
theorem principal_mass1622 :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) (r : ℝ), 1 ≤ N → 0 ≤ r → r ≤ 1 / 2 →
      (∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) ≤ B * (N : ℝ) := by
  sorry

/-- LEAF. P0093 page 166 equation 9.3, the factor 1 over Q to the 0.99 uses a lower
bound for phi of q on the range q above Q. The weaker classical form suffices. -/
theorem totient_sqrt_lower1622 (q : ℕ) (hq : 1 ≤ q) :
    Real.sqrt q ≤ 2 * (q.totient : ℝ) := by
  sorry

/-- Eventual comparison of the three terms with N to ninety eight hundredths. -/
theorem doubled_eventual1622 :
    ∀ᶠ N : ℕ in atTop, Real.log N ^ 13 ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
      Real.log N ^ 2 ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧ 1 ≤ Real.log N ∧
      (2 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hk : ∀ k : ℕ, ∀ᶠ N : ℕ in atTop, Real.log N ^ k ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
    intro k
    have hlo := isLittleO_log_rpow_rpow_atTop (k : ℝ) (by norm_num : (0 : ℝ) < 1 / 10)
    have hb := hlo.bound (show (0 : ℝ) < 1 by norm_num)
    filter_upwards [hcast.eventually hb, hcast.eventually (eventually_gt_atTop (1 : ℝ))] with N hN hN1
    have hl : 0 < Real.log N := Real.log_pos hN1
    rw [Real.rpow_natCast, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < Real.log N ^ k),
      abs_of_pos (by positivity : 0 < (N : ℝ) ^ (1 / 10 : ℝ)), one_mul] at hN
    exact hN
  have h1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1
  have h2 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hcast).eventually_ge_atTop 2
  exact (hk 13).and ((hk 2).and (h1.and h2))

set_option maxHeartbeats 1600000 in
/-- P0093 page 166 equation 9.1, in the weakened form used by equation 9.3.
Exact doubled_system_mass376 statement. CONDITIONAL on the three leaves above and
the three leaves of SPLIT1622_mellin. -/
theorem doubled_system_mass_recut1622 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, (N : ℝ) ^ (1 / 10 : ℝ) ≤ (q : ℝ) →
        (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
          (∫ α in arcSystem111 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1,
            ‖primeFourier111 N α‖ ^ 2) ≤ C * (N : ℝ) ^ (98 / 100 : ℝ) := by
  classical
  obtain ⟨B, hB, hchar⟩ := doubled_system_characters1622
  obtain ⟨P, hP, hprin⟩ := principal_mass1622
  obtain ⟨X, hX, Nx, hmel⟩ := mellin_radius1622 hG
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp doubled_eventual1622
  refine ⟨4 * B * P + 8 * B * X + 4 * B, by positivity, max 1 (max Nx (max N1 (2 ^ 21))), ?_⟩
  intro N hN q hqQ hqτ
  have h1N : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hxN : Nx < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have h1N1 : N1 < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hbig : 2 ^ 21 < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  obtain ⟨hl13, hl2, hl1, hQ2⟩ := hN1 N h1N1.le
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast h1N.le
  set τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ) with hτ
  set Q : ℝ := (N : ℝ) ^ (1 / 10 : ℝ) with hQ
  have hτpos : 0 < τ := by positivity
  have hQτ : Q ≤ τ := Real.rpow_le_rpow_of_exponent_le hN1r (by norm_num)
  have hτ4 : 4 ≤ τ := by
    have hbigr : ((2 : ℝ) ^ 21) ≤ N := by exact_mod_cast hbig.le
    have h7 : ((2 : ℝ) ^ 21) ^ (1 / 7 : ℝ) ≤ τ :=
      Real.rpow_le_rpow (by positivity) hbigr (by norm_num)
    have he : ((2 : ℝ) ^ 21) ^ (1 / 7 : ℝ) = 8 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have hq2R : (2 : ℝ) ≤ q := hQ2.trans hqQ
  have hq2 : 2 ≤ q := by exact_mod_cast hq2R
  have hqpos : (0 : ℝ) < q := by linarith
  haveI : NeZero q := ⟨by omega⟩
  have htot : 0 < q.totient := Nat.totient_pos.mpr (by omega)
  have htotR : (0 : ℝ) < q.totient := by exact_mod_cast htot
  have hsqrt := totient_sqrt_lower1622 q (by omega)
  set R : ℝ := (q : ℝ) * τ / 2 with hRdef
  have hRpos : 0 < R := by positivity
  have hR1 : 1 ≤ R := by
    rw [hRdef]
    nlinarith
  have hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by
    have hh := (qtau_range1622 N q h1N.le (by omega) hqτ).2
    have hpos : 0 ≤ (q : ℝ) * τ := by positivity
    rw [hRdef]
    linarith
  have hr : 2 / ((q : ℝ) * τ) = 1 / R := by
    rw [hRdef]
    field_simp
  have hr12 : 1 / R ≤ 1 / 2 := by
    rw [← hr]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hprinN := hprin N q (1 / R) h1N.le (by positivity) hr12
  have hnon : ∀ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      (∫ z in -(1 / R)..(1 / R), ‖characterPrime280 χ N z‖ ^ 2) ≤
        X * (N : ℝ) / R * Real.log N ^ 13 := by
    intro χ hχ
    exact hmel N hxN q (by omega) hqτ χ (Finset.mem_filter.mp hχ).2 R hR1 hR2
  have hsum : (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      ∫ z in -(1 / R)..(1 / R), ‖characterPrime280 χ N z‖ ^ 2) ≤
      (q.totient : ℝ) * (X * (N : ℝ) / R * Real.log N ^ 13) := by
    have hcard : ((Finset.univ.filter
        (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) ≤ q.totient := by
      have h1 := Finset.card_filter_le (Finset.univ : Finset (DirichletCharacter ℂ q))
        (fun χ => χ ≠ 1)
      have h2 : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      exact_mod_cast h2 ▸ h1
    calc _ ≤ ∑ _χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          (X * (N : ℝ) / R * Real.log N ^ 13) := Finset.sum_le_sum hnon
      _ = _ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hmain := hchar N q τ h1N.le hq2 hτ4
  rw [hr] at hmain
  have hlogq : Real.log q ≤ Real.log N := by
    apply Real.log_le_log hqpos
    have : τ ≤ N := by
      have h := Real.rpow_le_rpow_of_exponent_le hN1r (by norm_num : (1 / 7 : ℝ) ≤ 1)
      rw [Real.rpow_one] at h
      exact h
    linarith
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  -- first term
  have hN98 : (N : ℝ) * (N : ℝ) ^ (-(1 / 20 : ℝ)) = (N : ℝ) ^ (19 / 20 : ℝ) := by
    nth_rewrite 1 [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hNr]
    norm_num
  have hsqrtQ : (N : ℝ) ^ (1 / 20 : ℝ) ≤ Real.sqrt q := by
    rw [show (1 / 20 : ℝ) = (1 / 10) * (1 / 2) by norm_num, Real.rpow_mul hNr.le, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow (by positivity) hqQ (by norm_num)
  have h20pos : 0 < (N : ℝ) ^ (1 / 20 : ℝ) := by positivity
  have htotinv : 1 / (q.totient : ℝ) ≤ 2 * (N : ℝ) ^ (-(1 / 20 : ℝ)) := by
    rw [Real.rpow_neg hNr.le, ← one_div, ← mul_div_assoc, mul_one,
      div_le_div_iff₀ htotR h20pos]
    linarith
  have hp1 : (N : ℝ) ^ (19 / 20 : ℝ) ≤ (N : ℝ) ^ (98 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1r (by norm_num)
  have hp2 : τ⁻¹ * (N : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) ^ (98 / 100 : ℝ) := by
    have h : τ⁻¹ * (N : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) = (N : ℝ) ^ (1 - 1 / 7 + 1 / 10 : ℝ) := by
      rw [hτ, ← Real.rpow_neg hNr.le]
      nth_rewrite 2 [← Real.rpow_one (N : ℝ)]
      rw [← Real.rpow_add hNr, ← Real.rpow_add hNr]
      norm_num
    rw [h]
    exact Real.rpow_le_rpow_of_exponent_le hN1r (by norm_num)
  have hp3 : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) ^ (98 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1r (by norm_num)
  set W : ℝ := (N : ℝ) ^ (98 / 100 : ℝ) with hW
  have hWpos : 0 < W := by positivity
  -- bound the three pieces
  have term1 : B / (q.totient : ℝ) *
      (∫ z in -(1 / R)..(1 / R), ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) ≤
      2 * B * P * W := by
    have h0 : B / (q.totient : ℝ) ≤ 2 * B * (N : ℝ) ^ (-(1 / 20 : ℝ)) := by
      have := mul_le_mul_of_nonneg_left htotinv hB.le
      calc _ = B * (1 / (q.totient : ℝ)) := by ring
        _ ≤ _ := this
        _ = _ := by ring
    calc _ ≤ (2 * B * (N : ℝ) ^ (-(1 / 20 : ℝ))) * (P * (N : ℝ)) :=
          mul_le_mul h0 hprinN (intervalIntegral.integral_nonneg_of_forall
            (by have : 0 < 1 / R := by positivity
                linarith) (fun z => by positivity)) (by positivity)
      _ = 2 * B * P * ((N : ℝ) * (N : ℝ) ^ (-(1 / 20 : ℝ))) := by ring
      _ = 2 * B * P * (N : ℝ) ^ (19 / 20 : ℝ) := by rw [hN98]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp1 (by positivity)
  have term2 : B / (q.totient : ℝ) * ((q : ℝ) *
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ∫ z in -(1 / R)..(1 / R), ‖characterPrime280 χ N z‖ ^ 2) ≤ 2 * B * X * W := by
    have h0 : 0 ≤ B / (q.totient : ℝ) * (q : ℝ) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hsum h0
    have h2 : B / (q.totient : ℝ) * (q : ℝ) * ((q.totient : ℝ) * (X * (N : ℝ) / R *
        Real.log N ^ 13)) = 2 * B * X * (τ⁻¹ * (N : ℝ) * Real.log N ^ 13) := by
      rw [hRdef]
      field_simp
    calc _ = B / (q.totient : ℝ) * (q : ℝ) * (∑ χ ∈ Finset.univ.filter
          (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ∫ z in -(1 / R)..(1 / R), ‖characterPrime280 χ N z‖ ^ 2) := by ring
      _ ≤ _ := h1
      _ = _ := h2
      _ ≤ 2 * B * X * (τ⁻¹ * (N : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ)) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hp2 (by positivity)
  have term3 : B * (q.totient : ℝ) * (1 / R) * Real.log q ^ 2 ≤ 4 * B * W := by
    have htle : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    have h1 : (q.totient : ℝ) * (1 / R) ≤ 1 := by
      rw [hRdef]
      have : (q.totient : ℝ) * (1 / ((q : ℝ) * τ / 2)) = (q.totient : ℝ) * 2 / ((q : ℝ) * τ) := by
        field_simp
      rw [this, div_le_one (by positivity)]
      nlinarith
    have h2 : Real.log q ^ 2 ≤ Real.log N ^ 2 := pow_le_pow_left₀ hlogq0 hlogq 2
    have h3 : Real.log q ^ 2 ≤ W := (h2.trans hl2).trans hp3
    have h4 : 0 ≤ Real.log q ^ 2 := by positivity
    calc _ = B * ((q.totient : ℝ) * (1 / R)) * Real.log q ^ 2 := by ring
      _ ≤ B * 1 * W := by gcongr
      _ ≤ _ := by nlinarith
  calc _ ≤ _ := hmain
    _ = B / (q.totient : ℝ) * (∫ z in -(1 / R)..(1 / R),
          ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
        B / (q.totient : ℝ) * ((q : ℝ) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ∫ z in -(1 / R)..(1 / R), ‖characterPrime280 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * (1 / R) * Real.log q ^ 2 := by ring
    _ ≤ 2 * B * P * W + 2 * B * X * W + 4 * B * W := add_le_add (add_le_add term1 term2) term3
    _ ≤ _ := by nlinarith [mul_pos (mul_pos hB hP) hWpos, mul_pos (mul_pos hB hX) hWpos]

end LeanLab.Linnik1951
