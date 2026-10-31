/-
P0059, arXiv 1407.7902v1, pages 2 and 3, equations 2.4 to 2.8.
The central smoothing interval keeps both prime interval endpoints strict.
AI wrote this Lean code, CODEX task92, 2026-10-26.
-/
import LeanLab.KadiriLumley2014.G92
import LeanLab.KadiriLumley2014.TableRounding
import LeanLab.KadiriLumley2014.BindingRow
import LeanLab.KadiriLumley2014.OmegaIntegral
import LeanLab.KadiriLumley2014.WeightTail

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- LEAF. Page 2 before Section 2.1. Theta is constant across a prime-free interval. -/
theorem theta_eq_of_no_prime {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z)
    (h : ∀ p : ℕ, p.Prime → ¬ (y < p ∧ (p : ℝ) ≤ z)) :
    Chebyshev.theta z = Chebyshev.theta y := by
  classical
  unfold Chebyshev.theta
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hp0, hpz⟩, hp⟩
    have hpz' : (p : ℝ) ≤ z := (Nat.le_floor_iff (hy.trans hyz)).mp hpz
    have hpy : (p : ℝ) ≤ y := le_of_not_gt (fun hpy => h p hp ⟨hpy, hpz'⟩)
    exact ⟨⟨hp0, (Nat.le_floor_iff hy).mpr hpy⟩, hp⟩
  · rintro ⟨⟨hp0, hpy⟩, hp⟩
    exact ⟨⟨hp0, hpy.trans (Nat.floor_mono hyz)⟩, hp⟩

/-- LEAF. Page 2 equation 2.5. A positive central weighted difference forces a prime
strictly inside the enclosing interval. No analytic estimate is assumed here. -/
theorem prime_of_central_integral {a b y x : ℝ} {L U w : ℝ → ℝ}
    (hab : a ≤ b)
    (hgeom : ∀ t ∈ Ioo a b, 0 ≤ L t ∧ y ≤ L t ∧ L t ≤ U t ∧ U t < x)
    (hpos : 0 < ∫ t in a..b, (Chebyshev.theta (U t) - Chebyshev.theta (L t)) * w t) :
    ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) < x := by
  by_contra! hnone
  have hz : (∫ t in a..b, (Chebyshev.theta (U t) - Chebyshev.theta (L t)) * w t) = 0 := by
    calc
      _ = ∫ _t in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hab
        intro t ht
        obtain ⟨hL, hyL, hLU, hUx⟩ := hgeom t ht
        have heq := theta_eq_of_no_prime hL hLU (fun p hp hmem =>
          (not_lt_of_ge (hnone p hp (hyL.trans_lt hmem.1))) (hmem.2.trans_lt hUx))
        simp only [heq, sub_self, zero_mul]
      _ = 0 := by simp
  linarith


/-- The unnormalized central theta difference from page 2 equation 2.5. -/
noncomputable def centralThetaIntegral (m : ℕ) (δ u X a : ℝ) : ℝ :=
  ∫ t in a..(1 - a),
    (Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
      Chebyshev.theta (X * (1 + δ * t))) * weight m t

/-- LEAF. Page 2 equations 2.1 and 2.5. The central interval lies strictly
below the upper endpoint. Positive delta is essential to this strictness. -/
theorem smoothing_geometry {δ u X a t : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u)
    (hX : 0 < X) (ha : 0 ≤ a) (ht : t ∈ Ioo a (1 - a)) :
    0 ≤ X * (1 + δ * t) ∧
    X * (1 + δ * a) ≤ X * (1 + δ * t) ∧
    X * (1 + δ * t) ≤ Real.exp u * (X * (1 + δ * t)) ∧
    Real.exp u * (X * (1 + δ * t)) < Real.exp u * (X * (1 + δ * (1 - a))) := by
  have ht0 : 0 ≤ t := ha.trans ht.1.le
  have hL : 0 ≤ X * (1 + δ * t) := by positivity
  have he : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu
  refine ⟨hL, ?_, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_left (by nlinarith [ht.1]) hX.le
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right he hL
  · apply mul_lt_mul_of_pos_left _ (Real.exp_pos u)
    apply mul_lt_mul_of_pos_left _ hX
    nlinarith [ht.2]

/-- LEAF. Page 2 equation 2.5. Central positivity yields a prime between
the parameter endpoints with both inequalities strict. -/
theorem prime_of_smoothing {m : ℕ} {δ u X a : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u)
    (hX : 0 < X) (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hpos : 0 < centralThetaIntegral m δ u X a) :
    ∃ p : ℕ, p.Prime ∧ X * (1 + δ * a) < p ∧
      (p : ℝ) < Real.exp u * (X * (1 + δ * (1 - a))) := by
  exact prime_of_central_integral (by linarith)
    (fun t ht => smoothing_geometry hδ hu hX ha ht) hpos

/-- LEAF. Page 2 equation 2.1. The denominator formula gives exactly
the lower parameter endpoint. -/
theorem lower_endpoint_identity {δ u X a D : ℝ}
    (hB : 1 + δ * (1 - a) ≠ 0)
    (hD : D = 1 / intervalFraction δ u a) :
    (1 - 1 / D) * (Real.exp u * (X * (1 + δ * (1 - a)))) = X * (1 + δ * a) := by
  rw [hD, one_div_one_div]
  unfold intervalFraction
  rw [Real.exp_neg]
  field_simp [hB, Real.exp_ne_zero]
  ring


/-- The two endpoint theta integrals subtracted in page 3 equations 2.6 and 2.7. -/
noncomputable def tailThetaIntegral (m : ℕ) (δ u X a : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..a,
    (Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
      Chebyshev.theta (X * (1 + δ * t))) * weight m t) +
  (∫ t in (1 - a)..1,
    (Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
      Chebyshev.theta (X * (1 + δ * t))) * weight m t)

/-- The enlarged Brun Titchmarsh coefficient used in page 3 equation 2.7. -/
noncomputable def tailCoefficient (δ u X : ℝ) : ℝ :=
  2 * (1 + δ) * (Real.exp u - 1) *
    (Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1))) * X

/-- LEAF. Page 3 equation 2.7. The central integral is the total weighted
average times its mass minus the two endpoint integrals. -/
theorem central_integral_split (m : ℕ) {δ u X a : ℝ}
    (hδ : 0 ≤ δ) (hX : 0 ≤ X) (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) :
    centralThetaIntegral m δ u X a =
      thetaAverage m δ u X * (∫ t in (0 : ℝ)..1, weight m t) -
        tailThetaIntegral m δ u X a := by
  let F := fun t => (Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
      Chebyshev.theta (X * (1 + δ * t))) * weight m t
  have hi : IntervalIntegrable F volume 0 1 :=
    weighted_difference_integrable Chebyshev.theta_mono m hδ (Real.exp_nonneg u) hX
  have ha1 : a ≤ 1 := by linarith
  have hmid : a ≤ 1 - a := by linarith
  have h1a : 0 ≤ 1 - a := by linarith
  have h1a1 : 1 - a ≤ 1 := by linarith
  have hi0a : IntervalIntegrable F volume 0 a := hi.mono_set (by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le ha] using
      Icc_subset_Icc le_rfl ha1)
  have hia1a : IntervalIntegrable F volume a (1 - a) := hi.mono_set (by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le hmid] using
      Icc_subset_Icc ha h1a1)
  have hi1a1 : IntervalIntegrable F volume (1 - a) 1 := hi.mono_set (by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le h1a1] using
      Icc_subset_Icc h1a le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi0a hia1a
  have hadd' := intervalIntegral.integral_add_adjacent_intervals (hi0a.trans hia1a) hi1a1
  have hmass := (weight_mass_pos m).ne'
  unfold centralThetaIntegral tailThetaIntegral thetaAverage
  rw [div_mul_cancel₀ _ hmass]
  change (∫ t in a..(1 - a), F t) = (∫ t in (0 : ℝ)..1, F t) -
    ((∫ t in (0 : ℝ)..a, F t) + (∫ t in (1 - a)..1, F t))
  linarith

/-- LEAF. Page 3 equations 2.13 and 2.14. The psi margin and an endpoint
upper bound imply central positivity. This implication is CONDITIONAL ON CostaEstimate. -/
theorem central_positive_of_psi_margin (hCosta : CostaEstimate)
    (m : ℕ) {δ u X a : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 0.0001) (hu : 0 ≤ u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (htail : tailThetaIntegral m δ u X a ≤ tailCoefficient δ u X * tailMass m a)
    (hmargin : (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X +
      tailCoefficient δ u X * tailMass m a / (∫ t in (0 : ℝ)..1, weight m t) <
        psiAverage m δ u X) :
    0 < centralThetaIntegral m δ u X a := by
  have hm := weight_mass_pos m
  have htheta := thetaAverage_ge_psiAverage_sub_omega hCosta m hδ hδ1 hu hu1 hX
  rw [central_integral_split m hδ ((Real.exp_pos 38).le.trans hX) ha ha2]
  have hdiv : tailCoefficient δ u X * tailMass m a /
      (∫ t in (0 : ℝ)..1, weight m t) < thetaAverage m δ u X := by linarith
  have hmul := (div_lt_iff₀ hm).mp hdiv
  linarith


/-- LEAF. Page 13 Table 2 and page 2 equation 2.1. Every printed smoothing
step is positive and lies inside the small-parameter range. -/
theorem table_small_steps : ∀ r ∈ tableTwo,
    (0 : ℚ) < r.deltaQ ∧ r.deltaQ ≤ 0.0001 ∧
      1 / 10 ^ 12 ≤ r.uQ ∧ r.uQ ≤ 0.0001 := by
  decide +kernel

/-- LEAF. Page 2 equation 2.1. A coarse certified bound for the exponential
threshold used in the normalization. -/
theorem exp38_lt_base_quarter : Real.exp 38 < (10 : ℝ) ^ 18 := by
  calc
    Real.exp 38 = Real.exp 1 ^ 38 := by rw [← Real.exp_nat_mul]; norm_num
    _ < (2.7182818286 : ℝ) ^ 38 := by
      exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_nonneg 1) (by norm_num)
    _ < (10 : ℝ) ^ 18 := by norm_num

/-- LEAF. Page 2 equation 2.1 and page 3 equation 2.7. Rescaling an upper
endpoint above the binary base gives X above exp 38 and a positive log denominator. -/
theorem normalized_domain {δ u a x : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 0.0001)
    (hu : 1 / 10 ^ 12 ≤ u) (hu1 : u ≤ 0.0001)
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hx : (4 * 10 ^ 18 : ℝ) < x) :
    let X := x / (Real.exp u * (1 + δ * (1 - a)))
    0 < X ∧ Real.exp 38 ≤ X ∧ 1 < X * (Real.exp u - 1) ∧
      Real.exp u * (X * (1 + δ * (1 - a))) = x := by
  dsimp only
  have hu0 : 0 ≤ u := by linarith
  have hB : 0 < 1 + δ * (1 - a) := by
    have : 0 ≤ δ * (1 - a) := mul_nonneg hδ (by linarith)
    linarith
  have hB2 : 1 + δ * (1 - a) ≤ 2 := by nlinarith [mul_nonneg hδ ha]
  have he : Real.exp u ≤ 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 0.0001)
      (by norm_num : (0.0001 : ℝ) < 1)
    have hu' := Real.exp_le_exp.mpr hu1
    norm_num at h
    linarith
  have hS : 0 < Real.exp u * (1 + δ * (1 - a)) := mul_pos (Real.exp_pos u) hB
  have hS4 : Real.exp u * (1 + δ * (1 - a)) ≤ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hB2)]
  have hlarge : (10 : ℝ) ^ 18 < x / (Real.exp u * (1 + δ * (1 - a))) := by
    apply (lt_div_iff₀ hS).mpr
    nlinarith
  refine ⟨by positivity, exp38_lt_base_quarter.le.trans hlarge.le, ?_, ?_⟩
  · have huE : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
    have hE : 1 / (10 : ℝ) ^ 12 ≤ Real.exp u - 1 := hu.trans huE
    have hprod := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ x / (Real.exp u * (1 + δ * (1 - a))))
    nlinarith
  · field_simp


/-- LEAF. Page 3 Lemma 2.1, equation 2.9. Cited external input:
N. Costa Pereira, Estimates for the Chebyshev Function psi minus theta,
Math. Comp. 44, 1985, Theorem 5. This leaf remains unproved. -/
theorem costa_pereira : CostaEstimate := by
  sorry

/-- LEAF. Page 3 equation 2.6. Integrating a pointwise theta bound over
the two endpoint intervals gives its weighted tail bound. -/
theorem tail_bound_of_pointwise (m : ℕ) {δ u X a C : ℝ}
    (hδ : 0 ≤ δ) (hX : 0 ≤ X) (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1,
      Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
        Chebyshev.theta (X * (1 + δ * t)) ≤ C) :
    tailThetaIntegral m δ u X a ≤ C * tailMass m a := by
  let F := fun t => (Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
    Chebyshev.theta (X * (1 + δ * t))) * weight m t
  have hi : IntervalIntegrable F volume 0 1 :=
    weighted_difference_integrable Chebyshev.theta_mono m hδ (Real.exp_nonneg u) hX
  have piece : ∀ s b : ℝ, 0 ≤ s → s ≤ b → b ≤ 1 →
      (∫ t in s..b, F t) ≤ C * (∫ t in s..b, weight m t) := by
    intro s b hs hsb hb
    rw [← intervalIntegral.integral_const_mul]
    have his : IntervalIntegrable F volume s b := hi.mono_set (by
      rw [uIcc_of_le hsb, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc hs hb)
    apply intervalIntegral.integral_mono_on hsb his
      (((weight_continuous m).const_mul C).intervalIntegrable _ _)
    intro t ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨hs.trans ht.1, ht.2.trans hb⟩
    exact mul_le_mul_of_nonneg_right (hC t ht01) (weight_nonneg m ht01)
  have hleft := piece 0 a le_rfl ha (by linarith)
  have hright := piece (1 - a) 1 (by linarith) (by linarith) le_rfl
  unfold tailThetaIntegral tailMass
  change (∫ t in (0 : ℝ)..a, F t) + (∫ t in (1 - a)..1, F t) ≤ _
  calc
    _ ≤ C * (∫ t in (0 : ℝ)..a, weight m t) + C * (∫ t in (1 - a)..1, weight m t) :=
      add_le_add hleft hright
    _ = _ := by ring

/-- LEAF. Page 3 equation 2.6 with the enlarged logarithm of equation 2.7.
Cited external input: Montgomery and Vaughan, The Large Sieve,
Mathematika 20, 1973, Theorem 2. The exact constant two remains unproved. -/
theorem brun_titchmarsh_pointwise {δ u X t : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) (hgap : 1 < X * (Real.exp u - 1))
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
      Chebyshev.theta (X * (1 + δ * t)) ≤ tailCoefficient δ u X := by
  sorry

/-- LEAF. Page 3 equations 2.6 and 2.7. Cited external input:
Montgomery and Vaughan, The Large Sieve, Mathematika 20, 1973, Theorem 2;
also Ramare and Saouter 2003 page 16. The weighted step is now derived.
CONDITIONAL ON brun_titchmarsh_pointwise. -/
theorem brun_titchmarsh_tail {m : ℕ} (_hm : 2 ≤ m) {δ u X a : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) (hgap : 1 < X * (Real.exp u - 1))
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) :
    tailThetaIntegral m δ u X a ≤ tailCoefficient δ u X * tailMass m a := by
  exact tail_bound_of_pointwise m hδ ((Real.exp_pos 38).le.trans hX) ha ha2
    (fun t ht => brun_titchmarsh_pointwise hδ hδ1 hu hu1 hX hgap ht)

/-- The absolute zero summand from page 4 equation 2.19, with multiplicity.
The index contains exactly the nontrivial zeros in the open critical strip. -/
noncomputable def zeroSummand (m : ℕ) (δ u X : ℝ)
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) : ℝ :=
  (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖smoothingG m δ u ρ‖ *
    X ^ ((ρ : ℂ).re - 1)

/-- The nonnegative absolute zero sum Sigma in page 4 equation 2.19.
Summability is stated explicitly in the following analytic leaf. -/
noncomputable def zeroError (m : ℕ) (δ u X : ℝ) : ℝ :=
  ∑' ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}, zeroSummand m δ u X ρ

/-- Every absolute zero summand is nonnegative for nonnegative X. -/
theorem zeroSummand_nonneg (m : ℕ) (δ u : ℝ) {X : ℝ} (hX : 0 ≤ X)
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    0 ≤ zeroSummand m δ u X ρ := by
  unfold zeroSummand
  exact mul_nonneg (mul_nonneg (by positivity) (norm_nonneg _)) (Real.rpow_nonneg hX _)

/-- The absolute zero term decreases with X because every real part is below one. -/
theorem zeroSummand_antitone (m : ℕ) (δ u : ℝ) {X0 X : ℝ}
    (hX0 : 0 < X0) (hX : X0 ≤ X)
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) :
    zeroSummand m δ u X ρ ≤ zeroSummand m δ u X0 ρ := by
  unfold zeroSummand
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hX0 hX (by linarith [ρ.property.2.2]))
  positivity

/-- Page 4 after equation 2.18. Replacing X by X0 is valid for the actual
absolute zero sum. This implication is CONDITIONAL ON summability at X0. -/
theorem zeroError_antitone (m : ℕ) (δ u : ℝ) {X0 X : ℝ}
    (hX0 : 0 < X0) (hX : X0 ≤ X) (hs : Summable (zeroSummand m δ u X0)) :
    Summable (zeroSummand m δ u X) ∧ zeroError m δ u X ≤ zeroError m δ u X0 := by
  have hsX : Summable (zeroSummand m δ u X) :=
    Summable.of_nonneg_of_le (zeroSummand_nonneg m δ u (hX0.le.trans hX))
      (zeroSummand_antitone m δ u hX0 hX) hs
  exact ⟨hsX, hsX.tsum_le_tsum (zeroSummand_antitone m δ u hX0 hX) hs⟩

/-- LEAF. Page 4 Lemma 2.2 and equations 2.16 to 2.19.
The polynomial-smoothed explicit formula, its absolute zero sum and remainder.
Lemma 2.2 cites Ramare and Saouter 2003 Lemma 4. This leaf remains unproved. -/
theorem smoothed_explicit_lower {m : ℕ} (hm : 2 ≤ m) {δ u X : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) :
    Summable (zeroSummand m δ u X) ∧
      (Real.exp u - 1) * X * (1 + δ / 2 - zeroError m δ u X) - u / (2 * X) ≤
        psiAverage m δ u X := by
  sorry

/-- LEAF. Page 9 equation 2.64 and page 13 Table 2.
This is the remaining zero-sum and numerical budget after the explicit formula.
Its analytic sources are Lemmas 2.5 and 2.6 and Theorem 3.2, including
Platt 2011, Kadiri 2005 and 2013 and Rosser 1941. This leaf remains unproved. -/
theorem table_zero_budget {r : PrintedRow} (hr : r ∈ tableTwo) {a X : ℝ}
    (ha : a ∈ Icc (r.aQ : ℝ) ((r.aQ : ℝ) + 1 / 10000))
    (hD : (r.gapDenom : ℝ) = 1 / intervalFraction r.deltaQ r.uQ a)
    (hX : Real.exp 38 ≤ X)
    (hx : r.threshold < Real.exp r.uQ * (X * (1 + (r.deltaQ : ℝ) * (1 - a)))) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X +
      tailCoefficient r.deltaQ r.uQ X * tailMass r.m a /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * X) <
      (Real.exp r.uQ - 1) * X *
        (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ X) := by
  sorry

/-- LEAF. Page 3 equation 2.14, page 9 Theorem 2.7 equation 2.64 and
page 13 Table 2. This is the remaining psi lower estimate and numerical margin,
with the exact a selected inside its printed rounding interval.
Its analytic sources are Lemma 2.2, Lemmas 2.5 and 2.6 and Theorem 3.2.
External inputs include Platt 2011, Kadiri 2005 and 2013 and Rosser 1941.
This implication is CONDITIONAL ON smoothed_explicit_lower and table_zero_budget. -/
theorem table_psi_margin {r : PrintedRow} (hr : r ∈ tableTwo) {a X : ℝ}
    (ha : a ∈ Icc (r.aQ : ℝ) ((r.aQ : ℝ) + 1 / 10000))
    (hD : (r.gapDenom : ℝ) = 1 / intervalFraction r.deltaQ r.uQ a)
    (hX : Real.exp 38 ≤ X)
    (hx : r.threshold < Real.exp r.uQ * (X * (1 + (r.deltaQ : ℝ) * (1 - a)))) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X +
      tailCoefficient r.deltaQ r.uQ X * tailMass r.m a /
        (∫ t in (0 : ℝ)..1, weight r.m t) < psiAverage r.m r.deltaQ r.uQ X  := by
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
  have hδ1 : (r.deltaQ : ℝ) ≤ 0.0001 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.1
    norm_num at h ⊢
    exact h
  have hu : (0 : ℝ) < r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    norm_num at h
    linarith
  have hu1 : (r.uQ : ℝ) ≤ 0.0001 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.2
    norm_num at h ⊢
    exact h
  have hl := (smoothed_explicit_lower (tableTwo_parameters r hr).1 hδ hδ1 hu hu1 hX).2
  have hb := table_zero_budget hr ha hD hX hx
  linarith

/-- Table 2 assembled from the analytic leaves and the proved rounding and
smoothing lemmas. CONDITIONAL ON the four unproved analytic leaves above. -/
theorem table_row_from_leaves {r : PrintedRow} (hr : r ∈ tableTwo) :
    KLRow r.threshold r.gapDenom := by
  intro x hx
  obtain ⟨a, ha, hD⟩ := tableTwo_rounding_consistent hr
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
  have hδ1 : (r.deltaQ : ℝ) ≤ 0.0001 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.1
    norm_num at h ⊢
    exact h
  have hu : 1 / (10 : ℝ) ^ 12 ≤ r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    norm_num at h ⊢
    exact h
  have hu1 : (r.uQ : ℝ) ≤ 0.0001 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.2
    norm_num at h ⊢
    exact h
  have hu0 : (0 : ℝ) < r.uQ := by linarith
  have hrpar := (tableTwo_rounding_arithmetic r hr).1
  have haQ : (0 : ℝ) ≤ r.aQ := by exact_mod_cast hrpar.2.2.2.1
  have hbQ : (r.aQ : ℝ) + 1 / 10000 ≤ 1 / 2 := by
    have hb := (Rat.cast_le (K := ℝ)).mpr hrpar.2.2.2.2.1
    push_cast at hb
    norm_num at hb ⊢
    exact hb
  have ha0 : 0 ≤ a := haQ.trans ha.1
  have ha2 : a ≤ 1 / 2 := ha.2.trans hbQ
  have hxbase : (4 * 10 ^ 18 : ℝ) < x :=
    lt_of_le_of_lt (by
      have h := tableTwo_threshold_ge_base hr
      norm_num [evenBase] at h ⊢
      exact h) hx
  let X : ℝ := x / (Real.exp r.uQ * (1 + (r.deltaQ : ℝ) * (1 - a)))
  obtain ⟨hX0, hX38, hgap, htop⟩ := normalized_domain hδ.le hδ1 hu hu1 ha0 ha2 hxbase
  change 0 < X at hX0
  change Real.exp 38 ≤ X at hX38
  change 1 < X * (Real.exp r.uQ - 1) at hgap
  change Real.exp r.uQ * (X * (1 + (r.deltaQ : ℝ) * (1 - a))) = x at htop
  have htail := brun_titchmarsh_tail (tableTwo_parameters r hr).1 hδ.le hδ1 hu0 hu1
    hX38 hgap ha0 ha2
  have hmargin := table_psi_margin hr ha hD hX38 (by rwa [htop])
  have hpos := central_positive_of_psi_margin costa_pereira r.m hδ.le hδ1 hu0.le hu1
    hX38 ha0 ha2 htail hmargin
  obtain ⟨p, hp, hlo, hhi⟩ := prime_of_smoothing hδ hu0.le hX0 ha0 ha2 hpos
  have hB : 1 + (r.deltaQ : ℝ) * (1 - a) ≠ 0 := by
    have : 0 ≤ (r.deltaQ : ℝ) * (1 - a) := mul_nonneg hδ.le (by linarith)
    positivity
  have hlow := lower_endpoint_identity (X := X) hB hD
  rw [htop] at hlow hhi
  exact ⟨p, hp, by rwa [hlow], hhi⟩

end LeanLab.KadiriLumley2014.Task92
