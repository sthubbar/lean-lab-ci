import LeanLab.ChenDoubleSieve.Decomp349c

/-!
Elementary finite level preparation for the upper sieve sums in Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, page 39 equations 10.3 and 10.4.
No prime distribution estimate is asserted here.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set Asymptotics
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The upper sieve values are uniformly bounded on the full divisor range
below N to one third. CONDITIONAL ON IsLinearSieve only. -/
theorem upper_values_bounded (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) : ∃ M : ℝ, 0 ≤ M ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) → |F (lowerLevel B N d)| ≤ M := by
  have hc : ContinuousOn F (Icc (1 : ℝ) 6) := h.1.mono (by
    intro u hu
    change 0 < u
    linarith [hu.1])
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  obtain ⟨N0, hN0⟩ := lowerLevel_window B hB
  refine ⟨max M 0, le_max_right _ _, N0, ?_⟩
  intro N hN d hd hb
  have he := hM _ (hN0 N hN d hd hb)
  rw [Real.norm_eq_abs] at he
  exact he.trans (le_max_left _ _)

/-- Removing the finite logarithmic level loss changes the upper sieve values
uniformly by an arbitrarily small amount on the actual divisor range.
CONDITIONAL ON IsLinearSieve only. -/
theorem upper_values_shift_small (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
      |F (lowerLevel B N d) - F (lowerLevel 0 N d)| ≤ ε := by
  have hc : ContinuousOn F (Icc (1 : ℝ) 6) := h.1.mono (by
    intro u hu
    change 0 < u
    linarith [hu.1])
  obtain ⟨δ, hδ, hcont⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) ε hε
  have hs : ∀ᶠ N : ℕ in atTop, |lowerLevel B N 1 - 6| < δ := by
    have he := (lowerLevel_one_tendsto B).sub_const 6
    have hz : Tendsto (fun N : ℕ => |lowerLevel B N 1 - 6|) atTop (𝓝 0) := by
      simpa only [sub_self, abs_zero] using he.abs
    exact hz.eventually (eventually_lt_nhds hδ)
  obtain ⟨M, hM⟩ := eventually_atTop.1 hs
  obtain ⟨J, hJ⟩ := lowerLevel_window B hB
  refine ⟨max 2 (max M J), ?_⟩
  intro N hN d hd hb
  have hnear : dist (lowerLevel B N d) (lowerLevel 0 N d) < δ := by
    rw [Real.dist_eq, Task367.lowerLevel_shift B (by omega) hd]
    exact hM N (by omega)
  simpa only [Real.dist_eq] using
    (hcont _ (hJ N (by omega) d hd hb) _
      (Task367.lowerLevel_zero_window (by omega) hd hb) hnear).le

/-- The fixed sifting coordinates use the already defined residual level. -/
theorem basicSifting_fixed (N p : ℕ) (i : Fin 12)
    (hi : i ∈ ({2, 3} : Finset (Fin 12))) :
    basicSifting N p i = (N : ℝ) ^ kappa1 := by
  have hi1 : i ≠ 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> decide
  simp only [basicSifting, if_neg hi1]

/-- Every prime in either fixed upper band lies below N to one third. -/
theorem basic_fixed_prime_range {N p : ℕ} (hN : 2 ≤ N) {i : Fin 12}
    (hi : i ∈ ({2, 3} : Finset (Fin 12)))
    (hp : p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i)) :
    1 ≤ p ∧ (p : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
  have hs := Wu41.mem_PS.mp hp
  refine ⟨hs.1.one_lt.le, hs.2.2.1.le.trans ?_⟩
  apply rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> norm_num [basicEndpoint, sigma1, sigma2]

/-- The finite upper sieve value perturbation is uniform over both actual bands.
CONDITIONAL ON IsLinearSieve only. -/
theorem basic_fixed_values_shift_small (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ i : Fin 12,
      i ∈ ({2, 3} : Finset (Fin 12)) → ∀ p : ℕ,
        p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i) →
        |F (lowerLevel B N p) - F (lowerLevel 0 N p)| ≤ ε := by
  obtain ⟨M, hM⟩ := upper_values_shift_small F f h B hB ε hε
  refine ⟨max 2 M, ?_⟩
  intro N hN i hi p hp
  obtain ⟨hp1, hbound⟩ := basic_fixed_prime_range (by omega) hi hp
  exact hM N (by omega) p hp1 hbound

/-- Both actual four prime domains have nonempty concrete even instances. -/
theorem refinedQuads_instance :
    (37, 41, 43, 47) ∈ refinedQuads (2 ^ 60) 10 ∧
      (37, 41, 43, 131) ∈ refinedQuads (2 ^ 60) 11 := by
  have he (r : ℝ) : (((2 ^ 60 : ℕ) : ℝ) ^ r) = (2 : ℝ) ^ (60 * r) := by
    rw [rpow_mul (by norm_num)]
    norm_num
  have hlo : (((2 ^ 60 : ℕ) : ℝ) ^ kappa1) = 32 := by
    rw [he]
    norm_num [kappa1]
  have h64 : (64 : ℝ) ≤ ((2 ^ 60 : ℕ) : ℝ) ^ kappa2 := by
    rw [he]
    have h := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num [kappa2] : (6 : ℝ) ≤ 60 * kappa2)
    norm_num at h
    exact h
  have h128 : (((2 ^ 60 : ℕ) : ℝ) ^ kappa2) ≤ 128 := by
    rw [he]
    have h := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num [kappa2] : 60 * kappa2 ≤ (7 : ℝ))
    norm_num at h
    exact h
  have h37 : Nat.Coprime 37 (2 ^ 60) := (by decide : Nat.Coprime 37 2).pow_right 60
  have h41 : Nat.Coprime 41 (2 ^ 60) := (by decide : Nat.Coprime 41 2).pow_right 60
  have h43 : Nat.Coprime 43 (2 ^ 60) := (by decide : Nat.Coprime 43 2).pow_right 60
  have h47 : Nat.Coprime 47 (2 ^ 60) := (by decide : Nat.Coprime 47 2).pow_right 60
  have h131 : Nat.Coprime 131 (2 ^ 60) := (by decide : Nat.Coprime 131 2).pow_right 60
  constructor
  · simp only [refinedQuads, Wu08Sum.P4, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      show (10 : Fin 12) = 10 from rfl, ↓reduceIte]
    refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
      by norm_num, by norm_num, by norm_num, by norm_num,
      h37, h41, h43, h47, ?_, by norm_num, by norm_num, by norm_num, ?_⟩
    · rw [hlo]; norm_num
    · exact lt_of_lt_of_le (by norm_num : (47 : ℝ) < 64) h64
  · simp only [refinedQuads, Wu08Sum.P4, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      show (11 : Fin 12) ≠ 10 by decide, ↓reduceIte]
    refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
      by norm_num, by norm_num, by norm_num, by norm_num,
      h37, h41, h43, h131, ?_, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · rw [hlo]; norm_num
    · exact lt_of_lt_of_le (by norm_num : (43 : ℝ) < 64) h64
    · exact h128.trans (by norm_num)
    · rw [he]
      norm_num [kappa1]

/-- Each fixed power saving with any fixed logarithmic weight fits into
an arbitrary positive budget of the exact singular series normalizer. -/
theorem log_weighted_power_absorbed {δ : ℝ} (hδ : 0 < δ) (k : ℕ)
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      C * (N : ℝ) ^ (1 - δ) * log N ^ k ≤ ε * Θ N := by
  have hlo : (fun x : ℝ => log x ^ (k + 2)) =o[atTop] (fun x : ℝ => x ^ δ) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop ((k + 2 : ℕ) : ℝ) hδ)
  have hb := (hlo.const_mul_left C).bound (mul_pos hε LeanLab.ChenExplicit.twinC_pos)
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually hb)
  refine ⟨max M 2, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hbound := hM N (by omega)
  rw [Real.norm_of_nonneg (mul_nonneg hC (pow_nonneg hl.le _)),
    Real.norm_of_nonneg (rpow_nonneg hn.le _)] at hbound
  have hp : (N : ℝ) ^ δ * (N : ℝ) ^ (1 - δ) = N := by
    rw [← rpow_add hn, show δ + (1 - δ) = 1 by ring, rpow_one]
  have hc : LeanLab.ChenExplicit.twinC ≤ CN N := by
    unfold CN
    nlinarith [oddFactor_one_le N, LeanLab.ChenExplicit.twinC_pos]
  unfold Θ
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hl)).2
  calc
    C * (N : ℝ) ^ (1 - δ) * log N ^ k * log N ^ 2 =
        (C * log N ^ (k + 2)) * (N : ℝ) ^ (1 - δ) := by rw [pow_add]; ring
    _ ≤ ((ε * LeanLab.ChenExplicit.twinC) * (N : ℝ) ^ δ) *
        (N : ℝ) ^ (1 - δ) :=
      mul_le_mul_of_nonneg_right hbound (rpow_nonneg hn.le _)
    _ = ε * LeanLab.ChenExplicit.twinC * N := by rw [mul_assoc, hp]
    _ ≤ ε * CN N * N := by gcongr
    _ = ε * (CN N * N) := by ring

/-- The square root, progression and common factor error scales in
10.6 to 10.8 all vanish relative to the exact normalizer. -/
theorem switched_errors_absorbed (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      C * ((N : ℝ) ^ (1 / 2 : ℝ) + (N : ℝ) / log N ^ 3 +
        (N : ℝ) ^ (1 - sigma1) * log N ^ 2) ≤ ε * Θ N := by
  obtain ⟨A, hA⟩ := log_weighted_power_absorbed (δ := 1 / 2) (by norm_num) 0
    C (ε / 3) hC (by positivity)
  obtain ⟨B, hB⟩ := Task363.log_cubic_absorbed C (ε / 3) hC (by positivity)
  obtain ⟨D, hD⟩ := log_weighted_power_absorbed (δ := sigma1)
    (by norm_num [sigma1]) 2 C (ε / 3) hC (by positivity)
  refine ⟨max A (max B D), ?_⟩
  intro N hN
  have ha := hA N (by omega)
  have hb := hB N (by omega)
  have hd := hD N (by omega)
  norm_num only [pow_zero, mul_one, show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] at ha
  calc
    C * ((N : ℝ) ^ (1 / 2 : ℝ) + (N : ℝ) / log N ^ 3 +
        (N : ℝ) ^ (1 - sigma1) * log N ^ 2) =
      (C * (N : ℝ) ^ (1 / 2 : ℝ) + C * (N : ℝ) / log N ^ 3) +
        C * (N : ℝ) ^ (1 - sigma1) * log N ^ 2 := by ring
    _ ≤ (ε / 3) * Θ N + (ε / 3) * Θ N + (ε / 3) * Θ N :=
      add_le_add (add_le_add ha hb) hd
    _ = ε * Θ N := by ring

/-- The remaining prime logarithm is uniformly above one third of log N
on every actual switched pair domain. -/
theorem switched_remaining_log_lower {N : ℕ} (hN : 2 ≤ N) {i : Fin 12}
    {p : ℕ × ℕ} (hp : p ∈ switchedPairs N i) :
    (1 / 3 : ℝ) * log N < log ((N : ℝ) / ((p.1 : ℝ) * p.2)) := by
  have hs := switchedPairs_properties hp
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0 : ℝ) < p.1 := by exact_mod_cast hs.1.pos
  have hq0 : (0 : ℝ) < p.2 := by exact_mod_cast hs.2.1.pos
  have hsq : (p.2 : ℝ) ^ 2 < (N : ℝ) / p.1 :=
    (Real.lt_sqrt hq0.le).mp hs.2.2.2.2.2
  have hprod : (p.2 : ℝ) ^ 2 * p.1 < N := (lt_div_iff₀ hp0).mp hsq
  have hlog := log_lt_log (mul_pos (sq_pos_of_pos hq0) hp0) hprod
  rw [log_mul (sq_pos_of_pos hq0).ne' hp0.ne', log_pow] at hlog
  have horder : log (p.1 : ℝ) < log (p.2 : ℝ) :=
    log_lt_log hp0 (by exact_mod_cast hs.2.2.2.2.1)
  rw [log_div hn.ne' (mul_pos hp0 hq0).ne', log_mul hp0.ne' hq0.ne']
  norm_num at hlog
  linarith

/-- The refined weight is continuous, including at the one tenth cutoff. -/
theorem refinedCoordinateWeight_continuous : Continuous refinedCoordinateWeight := by
  unfold refinedCoordinateWeight
  apply continuous_if
  · intro t ht
    change t ∈ frontier (Iic (1 / 10 : ℝ)) at ht
    have ht' : t = (1 / 10 : ℝ) :=
      mem_singleton_iff.mp (frontier_Iic_subset _ ht)
    subst t
    norm_num
  · change ContinuousOn (fun t : ℝ => (36 / 5 : ℝ) / (1 - t))
      (closure (Iic (1 / 10 : ℝ)))
    rw [isClosed_Iic.closure_eq]
    apply ContinuousOn.div continuousOn_const (continuousOn_const.sub continuousOn_id)
    intro t ht
    have ht' : t ≤ (1 / 10 : ℝ) := ht
    change (1 : ℝ) - t ≠ 0
    linarith
  · exact continuousOn_const

end LeanLab.ChenDoubleSieve.Task349
