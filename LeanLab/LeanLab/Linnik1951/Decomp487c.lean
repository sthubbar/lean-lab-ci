/-
P0093 route supplies for Assembly376.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_logConv_excess1622
import LeanLab.Linnik1951.Relative442
import LeanLab.Linnik1951.Principal442
import LeanLab.Linnik1951.Decomp487b
import LeanLab.Linnik1951.SPLIT_rational_pointwise_characters442
import LeanLab.Linnik1951.Cover435

namespace LeanLab.Linnik1951

open MeasureTheory Filter Asymptotics Finset

/-- P0093 page 161 after equation 6.3. Exact relative convolution estimate from the corrected bounded majorant. No use of the refuted unbounded majorant. -/
theorem log_convolution_estimate487 :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n → |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤ B * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by
  obtain ⟨C, hCpos, hC⟩ := logConv_excess_corrected474
  obtain ⟨B1, hB1pos, hB1⟩ := logConv_small_range1622
  refine ⟨max B1 C, lt_of_lt_of_le hB1pos (le_max_left B1 C), ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hsqrtpos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlogpos
  have hA : 0 ≤ (n : ℝ) / Real.log (n : ℝ) ^ 2 :=
    div_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
  have hS : 0 ≤ 1 / Real.sqrt (Real.log (n : ℝ)) :=
    div_nonneg zero_le_one hsqrtpos.le
  have hX : 0 ≤ ((n : ℝ) / Real.log (n : ℝ) ^ 2) * (1 / Real.sqrt (Real.log (n : ℝ))) :=
    mul_nonneg hA hS
  rcases le_total n 1000 with hsmall | hlarge
  · have h := hB1 n hn hsmall
    calc
      |logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2|
          ≤ B1 * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ))) := h
      _ ≤ max B1 C * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ))) := by
            refine mul_le_mul_of_nonneg_right ?_ hS
            exact mul_le_mul_of_nonneg_right (le_max_left B1 C) hA
  · have h1000 : 1000 ≤ n := hlarge
    have h4 : 4 ≤ n := by omega
    have hmain : (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤ logConvolution1622 n :=
      logConv_main_le1622 n h4
    have hexc : logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤
        C * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := hC n h1000
    have habs : |logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2|
        = logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 :=
      abs_of_nonneg (by linarith)
    have hid : (n : ℝ) / Real.log (n : ℝ) ^ 3 =
        ((n : ℝ) / Real.log (n : ℝ) ^ 2) * (1 / Real.log (n : ℝ)) :=
      logConv_log_cube_split1622 n hn
    have hrec : 1 / Real.log (n : ℝ) ≤ 1 / Real.sqrt (Real.log (n : ℝ)) :=
      logConv_recip_log_le_sqrt1622 n h1000
    calc
      |logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2|
          = logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 := habs
      _ ≤ C * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := hexc
      _ = C * (((n : ℝ) / Real.log (n : ℝ) ^ 2) * (1 / Real.log (n : ℝ))) := by
            rw [hid]
      _ ≤ C * (((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ)))) := by
            refine mul_le_mul_of_nonneg_left ?_ hCpos.le
            exact mul_le_mul_of_nonneg_left hrec hA
      _ ≤ max B1 C * (((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ)))) := by
            refine mul_le_mul_of_nonneg_right ?_ hX
            exact le_max_right B1 C
      _ = max B1 C * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ))) := by ring

/-- P0093 pages 165 and 166 equations 8.1 and 8.2. Exact major_expansion_remainder376 statement. CONDITIONAL on arc_local_expansion1622, major_bookkeeping1622, GRH and MellinBound280. -/
theorem major_expansion487 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280)
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| ≤
        A * majorRelative376 k N +
          A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) := by
  obtain ⟨B, hB, N0, hL⟩ := arc_local_expansion1622 hG hM
  obtain ⟨B', hB', hC⟩ := log_convolution_estimate487
  exact major_bookkeeping1622 k hk B hB N0 hL B' hB' hC

/-- P0093 page 168 equation 10.7. Exact major_to_truncated357 statement with the arithmetic correction proved. CONDITIONAL on the local expansion and tuple bookkeeping, GRH and MellinBound280. -/
theorem major_to_truncated487 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280)
    (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| ≤
        ε * scale111 k N := by
  obtain ⟨A, hA, Na, ha⟩ := major_expansion487 hG hM k hk
  obtain ⟨Nr, hr⟩ := major_relative_negligible_proved442 k hk (ε / (2 * A)) (by positivity)
  obtain ⟨Np, hp⟩ := power_saving_negligible357 A (1 / 1000) hA
    (by norm_num) (k + 13) (ε / 2) (by positivity)
  refine ⟨max 2 (max Na (max Nr Np)), ?_⟩
  intro N hev hN
  have h2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNa : Na < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNr : Nr < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNp : Np < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hscale : (N : ℝ) ≤ scale111 k N := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl : Real.log 2 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast h2.le)
    have hr : 1 ≤ Real.log N / Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa using hl)
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ hr)
  have hrel : A * majorRelative376 k N ≤ (ε / 2) * scale111 k N := by
    calc
      _ ≤ A * (ε / (2 * A) * scale111 k N) :=
        mul_le_mul_of_nonneg_left (hr N hev hNr) hA.le
      _ = _ := by field_simp [hA.ne']
  have hpower : A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) ≤
      (ε / 2) * scale111 k N :=
    (hp N hNp).trans (mul_le_mul_of_nonneg_left hscale (by positivity))
  calc
    _ ≤ A * majorRelative376 k N +
        A * (N : ℝ) ^ (1 - (1 / 1000 : ℝ)) * Real.log N ^ (k + 13) := ha N hev hNa
    _ ≤ (ε / 2) * scale111 k N + (ε / 2) * scale111 k N := add_le_add hrel hpower
    _ = _ := by ring

/-- P0093 pages 155, 160 and 166. Exact doubled_system_characters1622 statement from the proved finite character bound and clipped rational integration. This retains the explicit q factor. -/
theorem doubled_system_characters487 :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q] (τ : ℝ), 1 ≤ N → 2 ≤ q → 4 ≤ τ →
      (∫ α in arcSystem111 q τ ∩ Set.Icc 0 1, ‖primeFourier111 N α‖ ^ 2) ≤
        B / (q.totient : ℝ) *
          ((∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
              ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
            (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
                ‖characterPrime280 χ N z‖ ^ 2) +
        B * (q.totient : ℝ) * (2 / ((q : ℝ) * τ)) * Real.log q ^ 2 := by
  classical
  obtain ⟨B, hB, hb⟩ := rational_pointwise_characters442_split
  refine ⟨2 * B, by positivity, ?_⟩
  intro N q _ τ hN hq hτ
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hτp : 0 < τ := by linarith
  set r := 2 / ((q : ℝ) * τ) with hrdef
  have hr : 0 < r := by positivity
  let F : Finset (DirichletCharacter ℂ q) := univ.filter (fun χ => χ ≠ 1)
  let J : ℝ → ℝ := fun z => ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 +
    (q : ℝ) * ∑ χ ∈ F, ‖characterPrime280 χ N z‖ ^ 2
  have hp : Continuous (fun z : ℝ => ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) :=
    (continuous_character_prime357 (1 : DirichletCharacter ℂ q) N hN).norm.pow 2
  have hc (χ : DirichletCharacter ℂ q) : Continuous (fun z : ℝ => ‖characterPrime280 χ N z‖ ^ 2) :=
    (continuous_character_prime357 χ N hN).norm.pow 2
  have hJ : Continuous J := hp.add ((continuous_finset_sum F (fun χ _ => hc χ)).const_mul _)
  have hJ0 : ∀ z, 0 ≤ J z := by intro z; dsimp [J]; positivity
  have hS : Continuous (fun z => ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) :=
    continuous_finset_sum _ (fun a _ =>
      ((continuous_prime_fourier111 N hN).norm.pow 2).comp (continuous_const.add continuous_id))
  have hgeo := rational_system_integral442 q τ hq hτ
    (fun α => ‖primeFourier111 N α‖ ^ 2) ((continuous_prime_fourier111 N hN).norm.pow 2)
    (fun α => sq_nonneg _)
  have hmono : (∫ z in -r..r, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2) ≤
      ∫ z in -r..r, B / (q.totient : ℝ) * J z + B * (q.totient : ℝ) * Real.log q ^ 2 :=
    intervalIntegral.integral_mono_on (by linarith) (hS.intervalIntegrable _ _)
      (((hJ.const_mul _).add continuous_const).intervalIntegrable _ _)
      (fun z _ => hb N q hN hq z)
  have hsplit : (∫ z in -r..r, J z) =
      (∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
        (q : ℝ) * ∑ χ ∈ F, ∫ z in -r..r, ‖characterPrime280 χ N z‖ ^ 2 := by
    dsimp [J]
    rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _)
      (((continuous_finset_sum F (fun χ _ => hc χ)).const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finset_sum (fun χ _ => (hc χ).intervalIntegrable _ _)]
  have hpos : 0 ≤ B / (q.totient : ℝ) * (∫ z in -r..r, J z) :=
    mul_nonneg (div_nonneg hB.le (Nat.cast_nonneg _))
      (intervalIntegral.integral_nonneg_of_forall (by linarith) hJ0)
  rw [intervalIntegral.integral_add ((hJ.const_mul _).intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hfinal : B / (q.totient : ℝ) * (∫ z in -r..r, J z) +
      (r - -r) * (B * (q.totient : ℝ) * Real.log q ^ 2) ≤
      (2 * B) / (q.totient : ℝ) * (∫ z in -r..r, J z) +
        (2 * B) * (q.totient : ℝ) * r * Real.log q ^ 2 := by
    calc
      _ ≤ 2 * (B / (q.totient : ℝ) * (∫ z in -r..r, J z)) +
          (r - -r) * (B * (q.totient : ℝ) * Real.log q ^ 2) := by linarith
      _ = _ := by ring
  have hh := hgeo.trans (hmono.trans hfinal)
  rw [hsplit] at hh
  exact hh

set_option maxHeartbeats 1600000 in
/-- P0093 page 166 equations 9.1 and 9.3. Exact doubled_system_mass376 statement from the weaker proved character bound. CONDITIONAL only on mellin_transfer1622, the finite signed contour and its tail, and GRH. -/
theorem doubled_system_mass487 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, (N : ℝ) ^ (1 / 10 : ℝ) ≤ (q : ℝ) →
        (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
          (∫ α in arcSystem111 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1,
            ‖primeFourier111 N α‖ ^ 2) ≤ C * (N : ℝ) ^ (98 / 100 : ℝ) := by
  classical
  obtain ⟨B, hB, hchar⟩ := doubled_system_characters487
  obtain ⟨P, hP, hprin⟩ := principal_mass_proved442
  obtain ⟨X, hX, Nx, hmel⟩ := mellin_radius487 hG
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
  have hsqrt := totient_sqrt_lower_proved442 q (by omega)
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

/-- P0093 page 166 Lemmas 6 and 7. Exact exceptional prime mass supply from the proved finite cover. CONDITIONAL on mellin_transfer1622, the finite signed contour and its tail, and GRH. -/
theorem exceptional_prime_mass487 (hG : LeanLab.DERZ1997.GRH) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N →
        (∫ α in exceptionalArcs280 N η, ‖primeFourier111 N α‖ ^ 2) ≤
          C * (N : ℝ) ^ (1 - (1 / 100 : ℝ)) := by
  obtain ⟨η, hη, hη1, A, hA, Na, ha⟩ := exceptional_system_cover435
  obtain ⟨C, hC, Nc, hc⟩ := doubled_system_mass487 hG
  refine ⟨η, hη, hη1, A * C, mul_pos hA hC, max 1 (max Na Nc), ?_⟩
  intro N hN
  have hNa : Na < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNc : Nc < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨S, hS, hq, hcover⟩ := ha N hNa
  have hInt : IntegrableOn (fun α : ℝ => ‖primeFourier111 N α‖ ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    ((continuous_prime_fourier111 N (by omega)).norm.pow 2).integrableOn_Icc
  have hb := finite_cover_integral376 (fun α => ‖primeFourier111 N α‖ ^ 2)
    (fun α => sq_nonneg _) (exceptionalArcs280 N η) S
    (fun q => arcSystem111 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1)
    (fun q _ => hInt.mono_set Set.inter_subset_right) hcover
  calc
    _ ≤ ∑ q ∈ S, ∫ α in arcSystem111 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1,
        ‖primeFourier111 N α‖ ^ 2 := hb
    _ ≤ ∑ _q ∈ S, C * (N : ℝ) ^ (98 / 100 : ℝ) :=
      Finset.sum_le_sum (fun q hmem => hc N hNc q (hq q hmem).1 (hq q hmem).2)
    _ = (S.card : ℝ) * (C * (N : ℝ) ^ (98 / 100 : ℝ)) := by simp
    _ ≤ (A * (N : ℝ) ^ (1 / 100 : ℝ)) * (C * (N : ℝ) ^ (98 / 100 : ℝ)) :=
      mul_le_mul_of_nonneg_right hS (by positivity)
    _ = A * C * ((N : ℝ) ^ (1 / 100 : ℝ) * (N : ℝ) ^ (98 / 100 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hNp]; congr 2; norm_num

/-- P0093 page 166 uses positive tau. The sealed rational_cover_integral1622 annotation omits that condition. Its exact universal statement is false at q two, tau negative one and the constant function one. This is an annotation QUESTION and not a paper error. -/
theorem not_rational_cover_integral487 :
    ¬ (∀ (q : ℕ) [NeZero q] (τ : ℝ) (f : ℝ → ℝ),
      Continuous f → (∀ x : ℝ, 0 ≤ f x) →
      (arcSystem111 q τ ∩ Set.Icc 0 1 ⊆
        ⋃ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          Set.Icc ((a : ℝ) / q - 2 / ((q : ℝ) * τ))
            ((a : ℝ) / q + 2 / ((q : ℝ) * τ))) →
      (∫ α in arcSystem111 q τ ∩ Set.Icc 0 1, f α) ≤
        ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            f ((a : ℝ) / q + z)) := by
  intro h
  have hempty : arcSystem111 2 (-1) = ∅ := by
    ext x
    simp only [arcSystem111, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨r, _hr, hx⟩
    norm_num at hx
    linarith [abs_nonneg (x - (r : ℝ))]
  have hcover : arcSystem111 2 (-1) ∩ Set.Icc 0 1 ⊆
      ⋃ a ∈ (Finset.range 2).filter (fun a => Nat.Coprime a 2),
        Set.Icc ((a : ℝ) / 2 - 2 / ((2 : ℝ) * (-1)))
          ((a : ℝ) / 2 + 2 / ((2 : ℝ) * (-1))) := by simp [hempty]
  have hfilt : (Finset.range 2).filter (fun a => Nat.Coprime a 2) = {1} := by decide
  have hbad := h 2 (-1) (fun _ => 1) continuous_const (fun _ => by norm_num) hcover
  rw [hfilt] at hbad
  norm_num [hempty] at hbad

end LeanLab.Linnik1951
