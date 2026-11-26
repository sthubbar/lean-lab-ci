/-
Burst S10 step mm525b, BhowmikGrimmelt2026. Source: Bhowmik and Grimmelt 2026,
arXiv 2607.27282, page 27, proof of Lemma 7.3, display 7.8, minor arc part.

* `nonprime_partial_S10b` PROVES the statement of the open leaf
  `leaf_nonprime_partial_feed1122`, MEDIUM, from Mathlib's `Chebyshev.psi_sub_theta_le`
  and the folder's `nonprime_mass_eq384`: the higher prime powers up to X carry von
  Mangoldt mass psi minus theta, at most two times the square root of X times log X.
* `prime_minor_multi_525_full_S10b` repeats the assembly of
  `prime_minor_multi_451_from_leaves` with that leaf replaced by the proof, and the range
  leaves `prime_minor_multi_525_mid` and `prime_minor_multi_525_long` follow with their
  exact statements as `prime_minor_multi_525_mid_S10b` and `prime_minor_multi_525_long_S10b`,
  CONDITIONAL ON `split_leaf_ssum_minor_log2` and `leaf_prime_family_feed1122` only.

No new sorry. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.SPLIT_prime_minor_multi_525
import LeanLab.BhowmikGrimmelt2026.LEAF_feed1122_prime_minor_multi_451
import LeanLab.BhowmikGrimmelt2026.Decomp384b

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction NNReal

attribute [local instance] Classical.propDecidable

/-- The additive character has modulus one. -/
theorem norm_ee_S10b (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by
    simp
  rw [hre, Real.exp_zero]

/-- P0029 page 27, proof of Lemma 7.3, display 7.8, the step from S to its prime part:
the statement of `leaf_nonprime_partial_feed1122`, PROVED. -/
theorem nonprime_partial_S10b {X m : ℕ} (hX : 2 ≤ X) (hm : m ≤ X) (α : ℝ) :
    ‖Ssum m α - ∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime),
        (vonMangoldt n : ℂ) * ee (α * n)‖ ≤
      2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 := by
  classical
  set g : ℕ → ℝ := fun n => vonMangoldt n - if n.Prime then vonMangoldt n else 0 with hg
  have hg0 : ∀ n, 0 ≤ g n := by
    intro n
    by_cases hp : n.Prime <;> simp [hg, hp, vonMangoldt_nonneg]
  have hdiff : Ssum m α - ∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime),
        (vonMangoldt n : ℂ) * ee (α * n) =
      ∑ n ∈ Finset.Icc 1 m, ((g n : ℝ) : ℂ) * ee (α * n) := by
    rw [Ssum, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hp : n.Prime <;> simp [hg, hp]
  have hnorm : ‖∑ n ∈ Finset.Icc 1 m, ((g n : ℝ) : ℂ) * ee (α * n)‖ ≤
      ∑ n ∈ Finset.Icc 1 m, g n := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, norm_ee_S10b, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hg0 n)]
  have hsub : ∑ n ∈ Finset.Icc 1 m, g n ≤ ∑ n ∈ Finset.range (X + 1), g n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => hg0 n
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    omega
  have hmass : ∑ n ∈ Finset.range (X + 1), g n =
      Chebyshev.psi X - Chebyshev.theta X := nonprime_mass_eq384 X
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hpsi : Chebyshev.psi X - Chebyshev.theta X ≤ 2 * Real.sqrt X * Real.log X :=
    Chebyshev.psi_sub_theta_le hX1
  rw [hdiff]
  refine hnorm.trans (hsub.trans ?_)
  rw [hmass]
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  rcases Nat.lt_or_ge X 3 with h3 | h3
  · have hX2 : X = 2 := by omega
    have hzero : ∑ n ∈ Finset.range (X + 1), g n = 0 := by
      subst hX2
      simp [hg, Finset.sum_range_succ, Nat.prime_two]
    rw [← hmass, hzero]
    positivity
  · have hX3 : (3 : ℝ) ≤ X := by exact_mod_cast h3
    have hlog1 : 1 ≤ Real.log X := by
      have h3' : (1 : ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have := Real.exp_one_lt_d9
        linarith
      exact h3'.le.trans (Real.log_le_log (by norm_num) hX3)
    have hsq : Real.sqrt X ≤ (X : ℝ) ^ (4 / 5 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    have hll : Real.log X ≤ Real.log X ^ 2 := by nlinarith
    calc Chebyshev.psi X - Chebyshev.theta X ≤ 2 * Real.sqrt X * Real.log X := hpsi
      _ ≤ 2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 := by
        have hs0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
        have : Real.sqrt X * Real.log X ≤ (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 :=
          mul_le_mul hsq hll hlog0 (by positivity)
        linarith

/-- Assembly of the parent `prime_minor_multi_525`, whose statement is that of
`prime_minor_multi_451`: the proof of `prime_minor_multi_451_from_leaves` copied with the
leaf `leaf_nonprime_partial_feed1122` replaced by the PROVED `nonprime_partial_S10b`, so it
rests only on `split_leaf_ssum_minor_log2` and `leaf_prime_family_feed1122`. -/
theorem prime_minor_multi_525_full_S10b {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
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
  obtain ⟨K, hK, hfamK⟩ := leaf_prime_family_feed1122 hϕ
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

/-- Switching off part of a family of nonnegative terms does not increase its sum. -/
theorem sum_ite_le_S10b (X : ℕ) (p : ℕ → Prop) {inst : DecidablePred p} (f : ℕ → ℝ)
    (hf : ∀ N, 0 ≤ f N) :
    ∑ N ∈ Finset.Icc 1 X, (if p N then f N else 0) ≤ ∑ N ∈ Finset.Icc 1 X, f N := by
  refine Finset.sum_le_sum fun N _ => ?_
  split_ifs
  · exact le_rfl
  · exact hf N

/-- Assembly of `prime_minor_multi_525_mid` exact statement, from `prime_minor_multi_525_full_S10b`. -/
theorem prime_minor_multi_525_mid_S10b {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      (∑ N ∈ Finset.Icc 1 X,
        (if Nat.sqrt X < N ∧ N ≤ (Nat.sqrt X + X) / 2 then
          ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2
        else 0)) ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, h⟩ := prime_minor_multi_525_full_S10b hϕ ϑ hϑ hϑ'
  exact ⟨C, hC, fun X hX hR =>
    (sum_ite_le_S10b X _ _ (fun N => sq_nonneg _)).trans (h X hX hR)⟩

/-- Assembly of `prime_minor_multi_525_long` exact statement, from `prime_minor_multi_525_full_S10b`. -/
theorem prime_minor_multi_525_long_S10b {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      (∑ N ∈ Finset.Icc 1 X,
        (if (Nat.sqrt X + X) / 2 < N then
          ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2
        else 0)) ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, h⟩ := prime_minor_multi_525_full_S10b hϕ ϑ hϑ hϑ'
  exact ⟨C, hC, fun X hX hR =>
    (sum_ite_le_S10b X _ _ (fun N => sq_nonneg _)).trans (h X hX hR)⟩

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.norm_ee_S10b
#print axioms LeanLab.BhowmikGrimmelt2026.nonprime_partial_S10b
#print axioms LeanLab.BhowmikGrimmelt2026.prime_minor_multi_525_full_S10b
#print axioms LeanLab.BhowmikGrimmelt2026.sum_ite_le_S10b
#print axioms LeanLab.BhowmikGrimmelt2026.prime_minor_multi_525_mid_S10b
#print axioms LeanLab.BhowmikGrimmelt2026.prime_minor_multi_525_long_S10b
