/-
Burst S10 step mm525c, BhowmikGrimmelt2026, stacked on step mm525b. Source: Bhowmik and
Grimmelt 2026, arXiv 2607.27282, pages 26 and 27, the varying family step before display
7.8 and display 7.8 itself.

* `prime_family_S10c` PROVES the statement of the open MEDIUM leaf
  `leaf_prime_family_feed1122`, by the weighted variation argument of the PROVED
  `supported_family_sharp261`, redone for the prime restricted smoothed sum: Parseval for
  one cutoff increment, `finite_parseval261`, the Lipschitz increment of phi,
  `phi_scale_increment261`, the von Mangoldt energy, `mangoldt_energy84`, and the family
  bound `family_inverse_energy261`. This is how the N dependence of phi of n over N is
  handled, where the single function Bessel step of page 16 does not apply.
* `prime_minor_multi_525_full_S10c` repeats the assembly of
  `prime_minor_multi_451_from_leaves` with both MEDIUM leaves replaced by proofs, so the
  range leaves `prime_minor_multi_525_mid` and `prime_minor_multi_525_long` follow with
  their exact statements, CONDITIONAL ON `split_leaf_ssum_minor_log2` alone, the pointwise
  minor arc bound at log power two that leaves the paper, QUESTION 2.

No new sorry. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.SPLIT_mm525b_S10
import LeanLab.BhowmikGrimmelt2026.SharpSupported261

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction NNReal

attribute [local instance] Classical.propDecidable

/-- The prime restricted smoothed sum of length X at cutoff N, written with an indicator. -/
theorem prime_sum_ite_S10c (ϕ : ℝ → ℝ) (X N : ℕ) (α : ℝ) :
    (∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
        ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) * ee (α * k)) =
      ∑ k ∈ Finset.range (X + 1),
        (if k.Prime then ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) else 0) * ee (α * k) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-- Continuity of the prime restricted smoothed sum in alpha. -/
theorem continuous_prime_sum_S10c (ϕ : ℝ → ℝ) (X N : ℕ) :
    Continuous (fun α : ℝ => ∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
        ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) * ee (α * k)) := by
  refine continuous_finset_sum _ fun k _ => ?_
  exact continuous_const.mul (ee_contDiff.continuous.comp (continuous_id.mul continuous_const))

/-- A uniform bound in alpha for the prime restricted smoothed sum. -/
theorem prime_sum_norm_le_S10c (ϕ : ℝ → ℝ) (X N : ℕ) (α : ℝ) :
    ‖∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
        ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) * ee (α * k)‖ ≤
      ∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
        ‖((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ)‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_ee_S10b, mul_one]

/-- The smoothing vanishes at zero. -/
theorem phi_zero_S10c {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) : ϕ 0 = 0 := by
  by_contra h
  have hs := hϕ.supp (subset_tsupport ϕ h)
  linarith [hs.1]

/-- The smoothing vanishes at every natural number. -/
theorem phi_nat_S10c {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (k : ℕ) : ϕ k = 0 := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simpa using phi_zero_S10c hϕ
  · exact phi_zero_ge_one261 hϕ (by exact_mod_cast h)

/-- Increment energy for the prime restricted smoothed sum, the prime analogue of
`Sphi_increment_energy261`, P0029 pages 26 and 27. -/
theorem prime_increment_energy_S10c {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    {L : ℝ≥0} (hL : LipschitzWith L ϕ) {X N : ℕ} (hN : 2 ≤ N) (hNX : N ≤ X) :
    (∫ α in (0 : ℝ)..1,
      ‖(∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
          ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) * ee (α * k)) -
        (∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
          ((vonMangoldt k * ϕ (k / (N - 1 : ℕ)) : ℝ) : ℂ) * ee (α * k))‖ ^ 2) ≤
      6 * (L : ℝ) ^ 2 * Real.log N / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hprev : (0 : ℝ) < (N - 1 : ℕ) := by exact_mod_cast (by omega : 0 < N - 1)
  set a : ℕ → ℂ := fun k => if k.Prime then
    ((vonMangoldt k * (ϕ (k / N) - ϕ (k / (N - 1 : ℕ))) : ℝ) : ℂ) else 0 with ha
  have hdiff (α : ℝ) :
      (∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
          ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) * ee (α * k)) -
        (∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
          ((vonMangoldt k * ϕ (k / (N - 1 : ℕ)) : ℝ) : ℂ) * ee (α * k)) =
      ∑ k ∈ Finset.range (X + 1), a k * ee (α * k) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : k.Prime
    · simp only [ha, hp, if_true]; push_cast; ring
    · simp [ha, hp]
  simp_rw [hdiff]
  rw [finite_parseval261]
  have hcut (k : ℕ) : ‖a k‖ ^ 2 ≤
      (if k ≤ N then vonMangoldt k ^ 2 * ((L : ℝ) / N) ^ 2 else 0) := by
    by_cases hp : k.Prime
    · simp only [ha, hp, if_true]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, mul_pow, sq_abs]
      by_cases hkN : k ≤ N
      · rw [if_pos hkN]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        by_cases hk' : k ≤ N - 1
        · exact phi_scale_increment261 hL hN hk'
        · have heq : k = N := by omega
          subst k
          rw [div_self hNpos.ne', phi_zero_ge_one261 hϕ le_rfl,
            phi_zero_ge_one261 hϕ ((le_div_iff₀ hprev).mpr (by
              have hh : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N - 1 ≤ N)
              simpa using hh))]
          simp only [sub_self, abs_zero]
          positivity
      · rw [if_neg hkN]
        have hk1 : (N : ℝ) < k := by exact_mod_cast (by omega : N < k)
        have hk2 : ((N - 1 : ℕ) : ℝ) < k := by exact_mod_cast (by omega : N - 1 < k)
        rw [phi_zero_ge_one261 hϕ ((le_div_iff₀ hNpos).mpr (by linarith)),
          phi_zero_ge_one261 hϕ ((le_div_iff₀ hprev).mpr (by linarith))]
        simp
    · simp only [ha, hp, if_false, norm_zero]
      have h0 : (0 : ℝ) ≤ vonMangoldt k ^ 2 * ((L : ℝ) / N) ^ 2 := by positivity
      split_ifs <;> simp [h0]
  have henergy : (∑ n ∈ Finset.range (N + 1), vonMangoldt n ^ 2) ≤
      6 * N * Real.log N := by
    have heq : (∑ n ∈ Finset.range (N + 1), vonMangoldt n ^ 2) =
        ∑ n ∈ Finset.Icc 1 N, vonMangoldt n ^ 2 := by
      rw [Nat.range_succ_eq_Icc_zero]
      symm
      apply Finset.sum_subset (Finset.Icc_subset_Icc (by omega) le_rfl)
      intro n hn hn'
      have hz : n = 0 := by simp only [Finset.mem_Icc] at hn hn'; omega
      simp [hz]
    rw [heq]
    exact mangoldt_energy84 N
  have hrestrict : (∑ k ∈ Finset.range (X + 1),
      (if k ≤ N then vonMangoldt k ^ 2 * ((L : ℝ) / N) ^ 2 else 0)) =
      ∑ k ∈ Finset.range (N + 1), vonMangoldt k ^ 2 * ((L : ℝ) / N) ^ 2 := by
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    _ ≤ ∑ k ∈ Finset.range (X + 1),
        (if k ≤ N then vonMangoldt k ^ 2 * ((L : ℝ) / N) ^ 2 else 0) :=
      Finset.sum_le_sum fun k _ => hcut k
    _ = ((L : ℝ) / N) ^ 2 * ∑ n ∈ Finset.range (N + 1), vonMangoldt n ^ 2 := by
      rw [hrestrict, ← Finset.sum_mul, mul_comm]
    _ ≤ ((L : ℝ) / N) ^ 2 * (6 * N * Real.log N) :=
      mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
    _ = _ := by field_simp

/-- P0029 pages 26 and 27, the varying family step before display 7.8, for the prime
restricted smoothed sum: the statement of `leaf_prime_family_feed1122`, PROVED by the weighted
variation argument of `supported_family_sharp261`. -/
theorem prime_family_S10c {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (X : ℕ), 2 ≤ X → ∀ (W : ℝ → ℂ), Measurable W →
      ∀ (B U : ℝ), 0 ≤ B → 0 ≤ U → (∀ α, ‖W α‖ ≤ B) →
      (∀ n ≤ X, ∀ α, W α ≠ 0 →
        ‖∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
          ((vonMangoldt k * ϕ (k / n) : ℝ) : ℂ) * ee (α * k)‖ ≤ U) →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1,
          (∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
            ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) * ee (α * k)) ^ 2 * W α *
            ee (-(N * α))‖ ^ 2 ≤
        K * B ^ 2 * U ^ 2 * X * Real.log X := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hϕ.compact hϕ.smooth (by simp)
  refine ⟨96 * (L : ℝ) ^ 2, by positivity, ?_⟩
  intro X hX W hW B U hB hU hWB hsup
  set P : ℕ → ℝ → ℂ := fun N α => ∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
      ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) * ee (α * k) with hP
  let F : ℕ → ℝ → ℂ := fun N α => P N α ^ 2 * W α
  have hP0 : P 0 = 0 := by
    funext α
    simp [hP, phi_zero_S10c hϕ]
  have hP1 : P 1 = 0 := by
    funext α
    simp [hP, phi_nat_S10c hϕ]
  have hLp (j : ℕ) : MemLp (F j) 2 (volume.restrict (Set.Ioc 0 1)) := by
    apply MemLp.of_bound
      (((continuous_prime_sum_S10c ϕ X j).pow 2).measurable.mul hW).aestronglyMeasurable
      ((∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
        ‖((vonMangoldt k * ϕ (k / j) : ℝ) : ℂ)‖) ^ 2 * B)
    apply Filter.Eventually.of_forall
    intro α
    change ‖P j α ^ 2 * W α‖ ≤ _
    rw [norm_mul, norm_pow]
    exact mul_le_mul
      (pow_le_pow_left₀ (norm_nonneg _) (prime_sum_norm_le_S10c ϕ X j α) 2)
      (hWB α) (norm_nonneg _) (by positivity)
  have hzero : F 0 = 0 := by funext α; simp [F, hP0]
  have hint (j : ℕ) : IntervalIntegrable (F j) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    exact MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (hLp j)
  have hinc (j : ℕ) (_hj : j ∈ Finset.Icc 1 X) :
      MemLp (fun α => F j α - F (j - 1) α) 2 (volume.restrict (Set.Ioc 0 1)) :=
    (hLp j).sub (hLp (j - 1))
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  have hE (j : ℕ) (hj : j ∈ Finset.Icc 1 X) :
      (∫ α in (0 : ℝ)..1, ‖F j α - F (j - 1) α‖ ^ 2) ≤
        24 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * Real.log X / j := by
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjX : j ≤ X := (Finset.mem_Icc.mp hj).2
    by_cases heq : j = 1
    · subst j
      simp only [F, hP1, hP0, Nat.sub_self, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_mul, sub_self, norm_zero,
        intervalIntegral.integral_zero]
      positivity
    · have hj2 : 2 ≤ j := by omega
      have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
      have hi : IntervalIntegrable (fun α => ‖F j α - F (j - 1) α‖ ^ 2) volume 0 1 := by
        apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
        exact (hinc j hj).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
      have hc : Continuous (fun α => ‖P j α - P (j - 1) α‖ ^ 2) :=
        ((continuous_prime_sum_S10c ϕ X j).sub
          (continuous_prime_sum_S10c ϕ X (j - 1))).norm.pow 2
      have hpoint (α : ℝ) :
          ‖F j α - F (j - 1) α‖ ≤ (2 * B * U) * ‖P j α - P (j - 1) α‖ := by
        by_cases hz : W α = 0
        · simp only [F, hz, mul_zero, sub_self, norm_zero]
          positivity
        · rw [show F j α - F (j - 1) α =
              (P j α - P (j - 1) α) * (P j α + P (j - 1) α) * W α by
              simp only [F]; ring,
            norm_mul, norm_mul]
          have hs : ‖P j α + P (j - 1) α‖ ≤ 2 * U :=
            (norm_add_le _ _).trans (by
              linarith [hsup j hjX α hz, hsup (j - 1) (by omega) α hz])
          calc
            _ ≤ ‖P j α - P (j - 1) α‖ * (2 * U) * B :=
              mul_le_mul (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
                (hWB α) (norm_nonneg _) (by positivity)
            _ = _ := by ring
      have henergy := prime_increment_energy_S10c hϕ hL hj2 hjX
      have hlog : Real.log j ≤ Real.log X :=
        Real.log_le_log hjpos (by exact_mod_cast hjX)
      calc
        _ ≤ ∫ α in (0 : ℝ)..1, (2 * B * U) ^ 2 * ‖P j α - P (j - 1) α‖ ^ 2 := by
          apply intervalIntegral.integral_mono_on (by norm_num) hi
            ((continuous_const.mul hc).intervalIntegrable 0 1)
          intro α _
          simpa only [Pi.mul_apply, mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hpoint α) 2
        _ = (2 * B * U) ^ 2 * ∫ α in (0 : ℝ)..1, ‖P j α - P (j - 1) α‖ ^ 2 :=
          intervalIntegral.integral_const_mul _ _
        _ ≤ (2 * B * U) ^ 2 * (6 * (L : ℝ) ^ 2 * Real.log j / j) :=
          mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
        _ = 24 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * Real.log j / j := by ring
        _ ≤ _ := by gcongr
  have h := family_inverse_energy261 X F hzero hint hinc
    (by positivity : 0 ≤ 24 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * Real.log X) hE
  refine le_trans h (le_of_eq ?_)
  ring

/-- Assembly of the parent `prime_minor_multi_525`, the proof of
`prime_minor_multi_451_from_leaves` with both MEDIUM leaves replaced by `nonprime_partial_S10b`
and `prime_family_S10c`, so it rests on `split_leaf_ssum_minor_log2` alone. -/
theorem prime_minor_multi_525_full_S10c {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1,
          if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 *
              ee (-(N * α))‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  classical
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hϕ.compact hϕ.smooth (by simp)
  obtain ⟨C₀, hC₀, h₀⟩ := split_leaf_ssum_minor_log2
  obtain ⟨K, hK, hfamK⟩ := prime_family_S10c hϕ
  refine ⟨2 * K * ((L : ℝ) * (C₀ + 2)) ^ 2, by positivity, ?_⟩
  intro X hX _hR2
  set R : ℝ := (X : ℝ) ^ ϑ with hRdef
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ R := Real.one_le_rpow hX1 hϑ.le
  have hRp : 0 < R := by linarith
  have hRX : R ≤ X := by
    calc
      _ ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = _ := Real.rpow_one _
  set A : ℝ := (X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ) with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hlog2 : 0 ≤ Real.log X ^ 2 := by positivity
  have hX45 : (X : ℝ) ^ (4 / 5 : ℝ) ≤ A := by
    have : 0 ≤ (X : ℝ) / Real.sqrt R := by positivity
    linarith
  let W : ℝ → ℂ := fun α => if MajorArc X R α then 0 else 1
  have hW : Measurable W :=
    measurable_const.ite (measurableSet_majorArc84 X R) measurable_const
  have hWB (α : ℝ) : ‖W α‖ ≤ (1 : ℝ) := by
    by_cases hm : MajorArc X R α <;> simp [W, hm]
  set U : ℝ := (L : ℝ) * ((C₀ + 2) * A * Real.log X ^ 2) with hUdef
  have hU0 : 0 ≤ U := by positivity
  have hsup : ∀ n ≤ X, ∀ α, W α ≠ 0 →
      ‖∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
        ((vonMangoldt k * ϕ (k / n) : ℝ) : ℂ) * ee (α * k)‖ ≤ U := by
    intro n hn α hne
    have hm : ¬ MajorArc X R α := by
      intro hh
      exact hne (by simp [W, hh])
    have hBn : 0 ≤ (C₀ + 2) * A * Real.log X ^ 2 := by positivity
    apply leaf_prime_parts_feed1122 hϕ hL hn hBn
    intro m hmn
    have hmX : m ≤ X := hmn.trans hn
    have hS := h₀ X hX R hR1 hRX m hmX α hm
    have hD := nonprime_partial_S10b hX hmX α
    have htri : ‖∑ k ∈ (Finset.Icc 1 m).filter (fun k => k.Prime),
        (vonMangoldt k : ℂ) * ee (α * k)‖ ≤
        ‖Ssum m α‖ + ‖Ssum m α - ∑ k ∈ (Finset.Icc 1 m).filter (fun k => k.Prime),
          (vonMangoldt k : ℂ) * ee (α * k)‖ := by
      have := norm_sub_le (Ssum m α) (Ssum m α -
        ∑ k ∈ (Finset.Icc 1 m).filter (fun k => k.Prime), (vonMangoldt k : ℂ) * ee (α * k))
      simpa using this
    have hD' : 2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 ≤ 2 * A * Real.log X ^ 2 := by
      gcongr
    have hexp : (C₀ + 2) * A * Real.log X ^ 2 =
        C₀ * A * Real.log X ^ 2 + 2 * A * Real.log X ^ 2 := by ring
    linarith
  have hfam := hfamK X hX W hW 1 U (by norm_num) hU0 hWB hsup
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1,
          (∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
            ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) * ee (α * k)) ^ 2 * W α *
            ee (-(N * α))) =
      ∫ α in (0 : ℝ)..1,
          if MajorArc X R α then 0 else
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 *
              ee (-(N * α)) := by
    apply intervalIntegral.integral_congr
    intro α _
    by_cases hm : MajorArc X R α <;> simp [W, hm]
  simp_rw [heq] at hfam
  have hA2 : ((X : ℝ) / Real.sqrt R) ^ 2 = (X : ℝ) ^ 2 / R := by
    rw [div_pow, Real.sq_sqrt hRp.le]
  have hD2 : ((X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 = (X : ℝ) ^ (8 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]
    norm_num
  have hsq : A ^ 2 ≤ 2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) := by
    rw [← hA2, ← hD2, hAdef]
    nlinarith only [sq_nonneg ((X : ℝ) / Real.sqrt R - (X : ℝ) ^ (4 / 5 : ℝ))]
  have hlogX : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX1
  have hpi := split_leaf_power_identity X hX ϑ
  calc
    _ ≤ K * 1 ^ 2 * U ^ 2 * X * Real.log X := hfam
    _ = K * ((L : ℝ) * (C₀ + 2)) ^ 2 * A ^ 2 * X * Real.log X ^ 5 := by
      rw [hUdef]; ring
    _ ≤ K * ((L : ℝ) * (C₀ + 2)) ^ 2 *
        (2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ))) * X * Real.log X ^ 5 := by
      gcongr
    _ = 2 * K * ((L : ℝ) * (C₀ + 2)) ^ 2 *
        (((X : ℝ) ^ 2 / (X : ℝ) ^ ϑ + (X : ℝ) ^ (8 / 5 : ℝ)) * (X : ℝ)) *
          Real.log X ^ 5 := by
      rw [hRdef]; ring
    _ = _ := by
      rw [hpi, hRdef]; ring

/-- Assembly of `prime_minor_multi_525_mid` exact statement, from `prime_minor_multi_525_full_S10c`. -/
theorem prime_minor_multi_525_mid_S10c {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      (∑ N ∈ Finset.Icc 1 X,
        (if Nat.sqrt X < N ∧ N ≤ (Nat.sqrt X + X) / 2 then
          ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2
        else 0)) ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, h⟩ := prime_minor_multi_525_full_S10c hϕ ϑ hϑ hϑ'
  exact ⟨C, hC, fun X hX hR =>
    (sum_ite_le_S10b X _ _ (fun N => sq_nonneg _)).trans (h X hX hR)⟩

/-- Assembly of `prime_minor_multi_525_long` exact statement, from `prime_minor_multi_525_full_S10c`. -/
theorem prime_minor_multi_525_long_S10c {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      (∑ N ∈ Finset.Icc 1 X,
        (if (Nat.sqrt X + X) / 2 < N then
          ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2
        else 0)) ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, h⟩ := prime_minor_multi_525_full_S10c hϕ ϑ hϑ hϑ'
  exact ⟨C, hC, fun X hX hR =>
    (sum_ite_le_S10b X _ _ (fun N => sq_nonneg _)).trans (h X hX hR)⟩

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.prime_increment_energy_S10c
#print axioms LeanLab.BhowmikGrimmelt2026.prime_family_S10c
#print axioms LeanLab.BhowmikGrimmelt2026.prime_minor_multi_525_full_S10c
#print axioms LeanLab.BhowmikGrimmelt2026.prime_minor_multi_525_mid_S10c
#print axioms LeanLab.BhowmikGrimmelt2026.prime_minor_multi_525_long_S10c
