/-
P0069, Section 4, pages 24 to 42. CODEX task312.
Separate the Perron transfer from the sieve supply at the reference interval.
The sealed leaf declarations are unchanged. The new assembly is CONDITIONAL.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Sifted312
import LeanLab.BHP1997.DecompC165c
import LeanLab.BHP1997.Decomp132
import LeanLab.BHP1997.Decomp312c

namespace LeanLab.BHP1997.Decomp312a
open Classical Complex DecompC165b Decomp312c Decomp132
open scoped BigOperators
open Filter

/-- Pages 24 and 25, I is eventually shorter than the reference interval I1. -/
theorem reference_width_long {ε : ℝ} (hε : ε < 1 / 10) :
    ∀ᶠ x : ℝ in Filter.atTop, 2 * x ^ (11 / 20 + ε) ≤ referenceWidth x := by
  let δ : ℝ := (0.45 - ε) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hs : ∀ᶠ t : ℝ in Filter.atTop, t ^ (-(2 / 3 : ℝ)) < δ / 3 :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).eventually
      (eventually_lt_nhds (div_pos hδ (by norm_num)))
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (Real.log 2 / δ)),
    Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx2 hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have he : Real.log x ^ (1 / 3 : ℝ) = Real.log x * Real.log x ^ (-(2 / 3 : ℝ)) := by
    calc
      _ = Real.log x ^ ((1 : ℝ) + (-(2 / 3 : ℝ))) := by norm_num
      _ = _ := by rw [Real.rpow_add hl, Real.rpow_one]
  have hsmall : 3 * Real.log x ^ (1 / 3 : ℝ) ≤ δ * Real.log x := by
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hx.le hl.le]
  have hlog2 : Real.log 2 ≤ δ * Real.log x := by simpa only [mul_comm] using (div_le_iff₀ hδ).mp hx2
  have htot : Real.log 2 + (11 / 20 + ε) * Real.log x ≤
      Real.log x - 3 * Real.log x ^ (1 / 3 : ℝ) := by
    dsimp [δ] at hsmall hlog2
    linarith
  rw [referenceWidth, Real.rpow_def_of_pos (show 0 < x by linarith)]
  calc
    2 * Real.exp (Real.log x * (11 / 20 + ε)) =
        Real.exp (Real.log 2 + (11 / 20 + ε) * Real.log x) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring
    _ ≤ Real.exp (Real.log x - 3 * Real.log x ^ (1 / 3 : ℝ)) := Real.exp_le_exp.mpr htot
    _ = _ := by
      rw [show Real.log x - 3 * Real.log x ^ (1 / 3 : ℝ) =
        Real.log x + -3 * Real.log x ^ (1 / 3 : ℝ) by ring,
        Real.exp_add, Real.exp_log (show 0 < x by linarith)]

/-- Page 3 and page 25, a prefix in I is the difference of two suffixes. -/
theorem prefix_eq_suffix_difference (f : ℕ → ℂ) {ε x t : ℝ}
    (ht : x - 2 * x ^ (11 / 20 + ε) ≤ t) :
    (∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t), f k) =
      (∑ k ∈ leftInterval ε x, f k) - ∑ k ∈ Finset.Ioc ⌊t⌋₊ ⌊x⌋₊, f k := by
  have hlo : ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ≤ ⌊t⌋₊ := Nat.floor_mono ht
  have he : (leftInterval ε x).filter (fun k : ℕ => ¬(k : ℝ) ≤ t) =
      Finset.Ioc ⌊t⌋₊ ⌊x⌋₊ := by
    ext k
    simp only [Finset.mem_filter, leftInterval, Finset.mem_Ioc, not_le]
    constructor
    · rintro ⟨⟨hk0, hkx⟩, hkt⟩
      have hk : k ≠ 0 := by omega
      exact ⟨(Nat.floor_lt' hk).mpr hkt, hkx⟩
    · rintro ⟨hkt, hkx⟩
      have hk : k ≠ 0 := by omega
      exact ⟨⟨lt_of_le_of_lt hlo hkt, hkx⟩, (Nat.floor_lt' hk).mp hkt⟩
  have hs := Finset.sum_filter_add_sum_filter_not (leftInterval ε x)
    (fun k : ℕ => (k : ℝ) ≤ t) f
  rw [he] at hs
  exact eq_sub_iff_add_eq.mpr hs

/-- Page 3, a prefix ending before I is empty. This handles every real t. -/
theorem prefix_empty_before {ε x t : ℝ} (ht : t < x - 2 * x ^ (11 / 20 + ε)) :
    (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t) = ∅ := by
  apply Finset.filter_eq_empty_iff.mpr
  intro k hk hkt
  have hk0 := (Finset.mem_Ioc.mp hk).1
  have hkne : k ≠ 0 := by omega
  have hkreal := (Nat.floor_lt' hkne).mp hk0
  linarith

/-- Pages 3 and 25, the repaired suffix comparison implies the exact
prefix estimate relative to I1. The positive epsilon power saving absorbs
the error in 4.5. CONDITIONAL on the explicit window estimate. -/
theorem relative_of_window {ε : ℝ} (hε : 0 < ε) (hεu : ε < 1 / 10)
    {a : ℝ → ℕ → ℝ} (hw : WindowComparison ε a) : RelativeDistribution ε a := by
  intro A hA
  obtain ⟨C0, X0, hwin⟩ := hw A hA
  obtain ⟨X1, hwidth⟩ := Filter.eventually_atTop.mp (reference_width_long hεu)
  let K : ℝ := (ε / 12 / A) ^ (-A)
  let C : ℝ := 2 * |C0| * (2 + K)
  refine ⟨C, max X0 (max X1 2), ?_⟩
  intro x hx q hq hqx χ t ht
  have hx0 : X0 ≤ x := (le_max_left _ _).trans hx
  have hx1 : X1 ≤ x := (le_trans (le_max_left X1 2) (le_max_right X0 _)).trans hx
  have hx2 : 2 ≤ x := (le_trans (le_max_right X1 2) (le_max_right X0 _)).trans hx
  have hxp : 0 < x := by linarith
  have hp : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hy : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg hxp.le _
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  have hpower : x ^ (0.55 + 11 * ε / 12) ≤
      K * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
    have he : (0.55 + 11 * ε / 12 : ℝ) = (11 / 20 + ε) - ε / 12 := by ring
    rw [he]
    exact DecompC165c.power_saving_to_log_saving (by linarith) hA (by positivity)
  have hbound (y : ℝ) (hy0 : 0 ≤ y) (hyu : y ≤ 2 * x ^ (11 / 20 + ε)) :
      ‖∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊,
        ((a x k : ℂ) * χ (k : ZMod q) - referenceAverage a x χ)‖ ≤
        |C0| * (2 + K) * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
    calc
      _ ≤ C0 * (y * Real.log x ^ (-A) + x ^ (0.55 + 11 * ε / 12)) :=
        hwin x hx0 q hq hqx χ y hy0 (hyu.trans (hwidth x hx1))
      _ ≤ |C0| * (y * Real.log x ^ (-A) + x ^ (0.55 + 11 * ε / 12)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C0) (by positivity)
      _ ≤ |C0| * ((2 * x ^ (11 / 20 + ε)) * Real.log x ^ (-A) +
          K * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
        gcongr
      _ = _ := by ring
  by_cases hlo : t < x - 2 * x ^ (11 / 20 + ε)
  · rw [prefix_empty_before hlo, Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (by dsimp [C]; positivity) hy) hp
  · have htlo : x - 2 * x ^ (11 / 20 + ε) ≤ t := le_of_not_gt hlo
    rw [prefix_eq_suffix_difference _ htlo]
    have hfull := hbound (2 * x ^ (11 / 20 + ε)) (by positivity) le_rfl
    have htail := hbound (x - t) (sub_nonneg.mpr ht) (by linarith)
    rw [sub_sub_cancel] at htail
    calc
      _ ≤ ‖∑ k ∈ leftInterval ε x,
          ((a x k : ℂ) * χ (k : ZMod q) - referenceAverage a x χ)‖ +
          ‖∑ k ∈ Finset.Ioc ⌊t⌋₊ ⌊x⌋₊,
          ((a x k : ℂ) * χ (k : ZMod q) - referenceAverage a x χ)‖ := norm_sub_le _ _
      _ ≤ (|C0| * (2 + K) * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) +
          (|C0| * (2 + K) * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
        add_le_add hfull htail
      _ = C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by dsimp [C]; ring


/-- Pages 24 and 25, Lemma 11, displays 4.1 to 4.5.
Uniform Perron transfer from both critical-line mean values to prefixes of I.
No density, prime sandwich, discarded integral or sieve construction is asserted.
The tiny suffixes are included in the explicit window input.
CONDITIONAL on perron_window_comparison. -/
theorem perron_transfer (B : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ a : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      MeanValue41 ε a → RelativeDistribution ε a := by
  obtain ⟨ηw, hηw, hw⟩ := perron_window_comparison B
  refine ⟨min ηw (1 / 10), lt_min hηw (by norm_num), ?_⟩
  intro ε hε hεη a ha hm
  exact relative_of_window hε (lt_of_lt_of_le hεη (min_le_right _ _))
    (hw ε hε (lt_of_lt_of_le hεη (min_le_left _ _)) a ha hm)

/-- Page 25, finite centering identity and triangle bound used after 4.5. -/
theorem center_sum_bound (S : Finset ℕ) (f : ℕ → ℂ) (r d : ℂ) :
    ‖∑ k ∈ S, (f k - d)‖ ≤
      ‖∑ k ∈ S, (f k - r)‖ + (S.card : ℝ) * ‖r - d‖ := by
  have he : (∑ k ∈ S, (f k - d)) =
      (∑ k ∈ S, (f k - r)) + ∑ _ ∈ S, (r - d) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he]
  calc
    _ ≤ ‖∑ k ∈ S, (f k - r)‖ + ‖∑ _ ∈ S, (r - d)‖ := norm_add_le _ _
    _ ≤ ‖∑ k ∈ S, (f k - r)‖ + ∑ _ ∈ S, ‖r - d‖ :=
      add_le_add le_rfl (norm_sum_le _ _)
    _ = _ := by simp

/-- Page 3, prefix cardinal bound for I, used to sum the reference-density error. -/
theorem left_prefix_card_bound {ε x t : ℝ} (hε : 0 ≤ ε) (hx : 1 ≤ x) :
    (((leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t)).card : ℝ) ≤
      3 * x ^ (11 / 20 + ε) := by
  have hy : 1 ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx (by linarith)
  have hlo : ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ≤ ⌊x⌋₊ :=
    Nat.floor_mono (by linarith)
  have hcard : ((leftInterval ε x).card : ℝ) =
      (⌊x⌋₊ : ℝ) - (⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by
    simp only [leftInterval, Nat.card_Ioc, Nat.cast_sub hlo]
  have hupper := Nat.floor_le (show 0 ≤ x by linarith)
  have hlower := Nat.lt_floor_add_one (x - 2 * x ^ (11 / 20 + ε))
  have hfilter : (((leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t)).card : ℝ) ≤
      ((leftInterval ε x).card : ℝ) := by
    exact_mod_cast Finset.card_filter_le (leftInterval ε x) (fun k : ℕ => (k : ℝ) ≤ t)
  rw [hcard] at hfilter
  linarith

/-- Pages 3 and 25, combine the relative Perron estimate and the I1 density.
CONDITIONAL on the two explicit analytic estimates, with no cited theorem used. -/
theorem distribution_of_reference {ε u : ℝ} {a : ℝ → ℕ → ℝ} (hε : 0 ≤ ε)
    (hr : RelativeDistribution ε a) (hd : ReferenceDensity u a) :
    CharacterDistribution ε u a := by
  intro A hA
  obtain ⟨Cr, Xr, hr⟩ := hr A hA
  obtain ⟨Cd, Xd, hd⟩ := hd A hA
  let C := max (Cr + 3 * |Cd|) (max Xr (max Xd 1))
  refine ⟨C, ?_⟩
  intro x hx q hq hqx χ t ht
  have hx1 : 1 ≤ x := (le_trans (le_trans (le_max_right Xd 1)
    (le_max_right Xr (max Xd 1))) (le_max_right _ _)).trans hx
  have hxR : Xr ≤ x := (le_trans (le_max_left Xr _) (le_max_right _ _)).trans hx
  have hxD : Xd ≤ x := (le_trans (le_trans (le_max_left Xd 1)
    (le_max_right Xr (max Xd 1))) (le_max_right _ _)).trans hx
  have hp : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hy : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
  have hd' : ‖referenceAverage a x χ - Thm2.delta χ * u / Real.log x‖ ≤
      |Cd| * Real.log x ^ (-A) :=
    (hd x hxD q hq hqx χ).trans (mul_le_mul_of_nonneg_right (le_abs_self Cd) hp)
  calc
    _ ≤ ‖∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t),
        ((a x k : ℂ) * χ (k : ZMod q) - referenceAverage a x χ)‖ +
        (((leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t)).card : ℝ) *
          ‖referenceAverage a x χ - Thm2.delta χ * u / Real.log x‖ :=
      center_sum_bound _ _ _ _
    _ ≤ Cr * x ^ (11 / 20 + ε) * Real.log x ^ (-A) +
        (3 * x ^ (11 / 20 + ε)) * (|Cd| * Real.log x ^ (-A)) := by
      apply add_le_add (hr x hxR q hq hqx χ t ht)
      exact mul_le_mul (left_prefix_card_bound hε hx1) hd' (norm_nonneg _)
        (mul_nonneg (by norm_num) hy)
    _ = (Cr + 3 * |Cd|) * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by ring
    _ ≤ C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hy) hp

/-- Page 3, enlarging the divisor exponent preserves the coefficient bound.
The zero index is handled separately since its divisor set is empty. -/
theorem divisor_bound_mono {a : ℝ → ℕ → ℝ} {B0 B : ℝ} (hB0 : 0 < B0)
    (hB : B0 ≤ B)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) :
    ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B := by
  obtain ⟨C, hC⟩ := ha
  refine ⟨|C|, fun x k => ?_⟩
  by_cases hk : k = 0
  · subst k
    have hb : B ≠ 0 := ne_of_gt (lt_of_lt_of_le hB0 hB)
    simpa [Real.zero_rpow (ne_of_gt hB0), Real.zero_rpow hb] using hC x 0
  · have ht : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
        (Finset.card_ne_zero.mpr (Nat.nonempty_divisors.mpr hk)))
    calc
      _ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0 := hC x k
      _ ≤ |C| * ((k.divisors.card : ℕ) : ℝ) ^ B0 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by positivity) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht hB) (abs_nonneg _)

/-- Page 24, linearity of the normalized I1 average. -/
theorem reference_average_add (a b : ℝ → ℕ → ℝ) (x : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    referenceAverage (fun x k => a x k + b x k) x χ =
      referenceAverage a x χ + referenceAverage b x χ := by
  simp only [referenceAverage, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, add_div]

/-- Pages 32 and 33, addition preserves the reference density estimate.
CONDITIONAL on the two actual reference estimates. -/
theorem reference_density_add {u v : ℝ} {a b : ℝ → ℕ → ℝ}
    (ha : ReferenceDensity u a) (hb : ReferenceDensity v b) :
    ReferenceDensity (u + v) (fun x k => a x k + b x k) := by
  intro A hA
  obtain ⟨Ca, Xa, ha⟩ := ha A hA
  obtain ⟨Cb, Xb, hb⟩ := hb A hA
  refine ⟨Ca + Cb, max Xa Xb, ?_⟩
  intro x hx q hq hqx χ
  have he : referenceAverage (fun x k => a x k + b x k) x χ -
      Thm2.delta χ * (u + v) / Real.log x =
      (referenceAverage a x χ - Thm2.delta χ * u / Real.log x) +
      (referenceAverage b x χ - Thm2.delta χ * v / Real.log x) := by
    rw [reference_average_add]
    ring
  simp only [Complex.ofReal_add]
  rw [he]
  calc
    _ ≤ ‖referenceAverage a x χ - Thm2.delta χ * u / Real.log x‖ +
        ‖referenceAverage b x χ - Thm2.delta χ * v / Real.log x‖ := norm_add_le _ _
    _ ≤ Ca * Real.log x ^ (-A) + Cb * Real.log x ^ (-A) :=
      add_le_add (ha x ((le_max_left _ _).trans hx) q hq hqx χ)
        (hb x ((le_max_right _ _).trans hx) q hq hqx χ)
    _ = _ := by ring

/-- Pages 32 and 33, a sign reversal preserves the normalized reference estimate.
CONDITIONAL on the stated reference estimate. -/
theorem reference_density_neg {u : ℝ} {a : ℝ → ℕ → ℝ}
    (ha : ReferenceDensity u a) : ReferenceDensity (-u) (fun x k => -a x k) := by
  intro A hA
  obtain ⟨C, X, hC⟩ := ha A hA
  refine ⟨C, X, ?_⟩
  intro x hx q hq hqx χ
  have he : referenceAverage (fun x k => -a x k) x χ -
      Thm2.delta χ * (-u) / Real.log x =
      -(referenceAverage a x χ - Thm2.delta χ * u / Real.log x) := by
    simp only [referenceAverage, Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib,
      neg_div, mul_neg]
    ring
  simp only [Complex.ofReal_neg]
  rw [he, norm_neg]
  exact hC x hx q hq hqx χ

/-- Pages 24 and 25, zero-family consistency of all four paper predicates.
The nonzero finite-interval instance below tests the normalization separately. -/
theorem analytic_zero_instances (ε : ℝ) :
    MeanValue41 ε (fun _ _ => 0) ∧ ReferenceDensity 0 (fun _ _ => 0) ∧
      RelativeDistribution ε (fun _ _ => 0) ∧ WindowComparison ε (fun _ _ => 0) := by
  have havg (x : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q) :
      referenceAverage (fun _ _ => 0) x χ = 0 := by simp [referenceAverage]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A hA
    refine ⟨1, 1, ?_⟩
    intro x hx q hq hqx χ σ hσ
    simp only [Complex.ofReal_zero, zero_mul, zero_div, Finset.sum_const_zero, norm_zero,
      intervalIntegral.integral_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Real.log_nonneg hx) _)
  · intro A hA
    refine ⟨1, 1, ?_⟩
    intro x hx q hq hqx χ
    simp only [havg, Complex.ofReal_zero, mul_zero, zero_div, sub_zero, norm_zero, one_mul]
    exact Real.rpow_nonneg (Real.log_nonneg hx) _
  · intro A hA
    refine ⟨1, 1, ?_⟩
    intro x hx q hq hqx χ t ht
    simp only [Complex.ofReal_zero, zero_mul, havg, sub_zero, Finset.sum_const_zero, norm_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Real.log_nonneg hx) _)
  · intro A hA
    refine ⟨1, 1, ?_⟩
    intro x hx q hq hqx χ y hy hyu
    simp only [Complex.ofReal_zero, zero_mul, havg, sub_zero, Finset.sum_const_zero, norm_zero, one_mul]
    exact add_nonneg (mul_nonneg hy (Real.rpow_nonneg (Real.log_nonneg hx) _)) (by positivity)

/-- Pages 3, 24 and 25, a nonempty reference interval and the factor 2Y
normalization at x equal to 1. This local check asserts no asymptotic density. -/
theorem reference_nonzero_instance (ε : ℝ) :
    referenceWidth 1 = 1 ∧
    referenceAverage (fun _ _ => 1) 1 (1 : DirichletCharacter ℂ 1) = 1 ∧
    leftInterval ε 1 = {1} := by
  norm_num [referenceWidth, referenceAverage, leftInterval]

/-- Pages 41 and 42, local consistency of the two scalar density ranges. -/
theorem supply_density_instances :
    0.9953 < (0.999 : ℝ) ∧ (0.999 : ℝ) ≤ 1 ∧
      1 ≤ (1.00005 : ℝ) ∧ (1.00005 : ℝ) < 1.0001 ∧
      (0 : ℝ) < 0.001 ∧ (0.001 : ℝ) < 1 / 10 := by
  norm_num

/-- Pages 26 and 27, character twists do not enlarge an absolute coefficient error. -/
theorem twisted_sum_error (S T : Finset ℕ) (hST : S ⊆ T) (a b : ℕ → ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖∑ k ∈ S, (((a k - b k : ℝ) : ℂ) * χ (k : ZMod q))‖ ≤
      ∑ k ∈ T, |a k - b k| := by
  calc
    _ ≤ ∑ k ∈ S, ‖((a k - b k : ℝ) : ℂ) * χ (k : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ S, |a k - b k| := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (χ.norm_le_one (k : ZMod q)) (abs_nonneg (a k - b k))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hST (fun k hk hks => abs_nonneg _)

/-- Pages 26 and 27, transfer 1.7 through the absolute Möbius truncation error.
CONDITIONAL on the approximation and the auxiliary character distribution. -/
theorem distribution_of_approximation {ε u : ℝ} {a b : ℝ → ℕ → ℝ}
    (ha : ShortApproximation ε a b) (hb : CharacterDistribution ε u b) :
    CharacterDistribution ε u a := by
  intro A hA
  obtain ⟨Ca, Xa, ha⟩ := ha A hA
  obtain ⟨Cb, hb⟩ := hb A hA
  let C : ℝ := max (Ca + Cb) (max Xa (max Cb 1))
  refine ⟨C, ?_⟩
  intro x hx q hq hqx χ t ht
  have hxa : Xa ≤ x := (le_trans (le_max_left Xa _) (le_max_right _ _)).trans hx
  have hxb : Cb ≤ x := (le_trans (le_trans (le_max_left Cb 1)
    (le_max_right Xa (max Cb 1))) (le_max_right _ _)).trans hx
  have hx1 : 1 ≤ x := (le_trans (le_trans (le_max_right Cb 1)
    (le_max_right Xa (max Cb 1))) (le_max_right _ _)).trans hx
  have hp : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hy : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
  let S := (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t)
  have he : (∑ k ∈ S, ((a x k : ℂ) * χ (k : ZMod q) - Thm2.delta χ * u / Real.log x)) =
      (∑ k ∈ S, (((a x k - b x k : ℝ) : ℂ) * χ (k : ZMod q))) +
      ∑ k ∈ S, ((b x k : ℂ) * χ (k : ZMod q) - Thm2.delta χ * u / Real.log x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    ring
  change ‖∑ k ∈ S, _‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖∑ k ∈ S, (((a x k - b x k : ℝ) : ℂ) * χ (k : ZMod q))‖ +
        ‖∑ k ∈ S, ((b x k : ℂ) * χ (k : ZMod q) - Thm2.delta χ * u / Real.log x)‖ := norm_add_le _ _
    _ ≤ Ca * x ^ (11 / 20 + ε) * Real.log x ^ (-A) +
        Cb * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
      add_le_add ((twisted_sum_error S (leftInterval ε x) (Finset.filter_subset _ _) _ _ χ).trans (ha x hxa))
        (hb x hxb q hq hqx χ t ht)
    _ = (Ca + Cb) * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by ring
    _ ≤ C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hy) hp

/-- Pages 26 and 27, exact agreement gives zero absolute truncation error. -/
theorem short_approximation_refl (ε : ℝ) (a : ℝ → ℕ → ℝ) :
    ShortApproximation ε a a := by
  intro A hA
  exact ⟨0, 0, by simp⟩

/-- Pages 26 and 27, successive truncations add their absolute error budgets.
CONDITIONAL on the two stated approximation estimates. -/
theorem short_approximation_trans {ε : ℝ} {a b c : ℝ → ℕ → ℝ}
    (hab : ShortApproximation ε a b) (hbc : ShortApproximation ε b c) :
    ShortApproximation ε a c := by
  intro A hA
  obtain ⟨Cab, Xab, hab⟩ := hab A hA
  obtain ⟨Cbc, Xbc, hbc⟩ := hbc A hA
  refine ⟨Cab + Cbc, max Xab Xbc, ?_⟩
  intro x hx
  calc
    _ ≤ ∑ k ∈ leftInterval ε x, (|a x k - b x k| + |b x k - c x k|) :=
      Finset.sum_le_sum (fun k hk => abs_sub_le _ _ _)
    _ = (∑ k ∈ leftInterval ε x, |a x k - b x k|) +
        ∑ k ∈ leftInterval ε x, |b x k - c x k| := Finset.sum_add_distrib
    _ ≤ Cab * x ^ (11 / 20 + ε) * Real.log x ^ (-A) +
        Cbc * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
      add_le_add (hab x ((le_max_left _ _).trans hx)) (hbc x ((le_max_right _ _).trans hx))
    _ = _ := by ring

/-- Pages 26, 27 and 32, two signed sieve contributions add their absolute errors.
CONDITIONAL on the two stated approximation estimates. -/
theorem short_approximation_add {ε : ℝ} {a b c d : ℝ → ℕ → ℝ}
    (hab : ShortApproximation ε a b) (hcd : ShortApproximation ε c d) :
    ShortApproximation ε (fun x k => a x k + c x k) (fun x k => b x k + d x k) := by
  intro A hA
  obtain ⟨Cab, Xab, hab⟩ := hab A hA
  obtain ⟨Ccd, Xcd, hcd⟩ := hcd A hA
  refine ⟨Cab + Ccd, max Xab Xcd, ?_⟩
  intro x hx
  calc
    _ ≤ ∑ k ∈ leftInterval ε x, (|a x k - b x k| + |c x k - d x k|) := by
      apply Finset.sum_le_sum
      intro k hk
      have he : a x k + c x k - (b x k + d x k) =
          (a x k - b x k) + (c x k - d x k) := by ring
      rw [he]
      exact abs_add_le _ _
    _ = (∑ k ∈ leftInterval ε x, |a x k - b x k|) +
        ∑ k ∈ leftInterval ε x, |c x k - d x k| := Finset.sum_add_distrib
    _ ≤ Cab * x ^ (11 / 20 + ε) * Real.log x ^ (-A) +
        Ccd * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
      add_le_add (hab x ((le_max_left _ _).trans hx)) (hcd x ((le_max_right _ _).trans hx))
    _ = _ := by ring

/-- Pages 26, 27 and 32, sign reversal preserves the absolute approximation.
CONDITIONAL on the stated approximation estimate. -/
theorem short_approximation_neg {ε : ℝ} {a b : ℝ → ℕ → ℝ}
    (hab : ShortApproximation ε a b) :
    ShortApproximation ε (fun x k => -a x k) (fun x k => -b x k) := by
  intro A hA
  obtain ⟨C, X, hC⟩ := hab A hA
  refine ⟨C, X, ?_⟩
  intro x hx
  simpa only [neg_sub_neg, abs_sub_comm] using hC x hx

/-- Pages 26, 27 and 32, finitely many sieve contributions preserve the approximation.
CONDITIONAL on the approximation estimate for every contribution. -/
theorem short_approximation_sum {ι : Type*} (S : Finset ι) {ε : ℝ}
    (a b : ι → ℝ → ℕ → ℝ) (h : ∀ i ∈ S, ShortApproximation ε (a i) (b i)) :
    ShortApproximation ε (fun x k => ∑ i ∈ S, a i x k) (fun x k => ∑ i ∈ S, b i x k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using short_approximation_refl ε (fun _ _ => 0)
  | @insert i S hi ih =>
    have hS := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using
      short_approximation_add (h i (Finset.mem_insert_self _ _)) hS

/-- Pages 32 and 33, a finite collection of reference means has the summed density.
CONDITIONAL on the reference estimate for every contribution. -/
theorem reference_density_sum {ι : Type*} (S : Finset ι) (u : ι → ℝ)
    (a : ι → ℝ → ℕ → ℝ) (h : ∀ i ∈ S, ReferenceDensity (u i) (a i)) :
    ReferenceDensity (∑ i ∈ S, u i) (fun x k => ∑ i ∈ S, a i x k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (analytic_zero_instances 0).2.1
  | @insert i S hi ih =>
    have hS := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using
      reference_density_add (h i (Finset.mem_insert_self _ _)) hS

/-- Page 26, the Möbius divisor expansion preceding the truncation in Lemma 12.
Mathlib's Möbius times zeta identity supplies the inversion. -/
theorem sifted_mobius_expansion (n : ℕ) (z : ℝ) :
    siftedWeight n ⌈z⌉₊ =
      ∑ d ∈ (Thm2.primorialBelow z).divisors.filter (fun d => d ∣ n),
        (ArithmeticFunction.moebius d : ℝ) := by
  have hP : Thm2.primorialBelow z ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1.ne_zero
  have hg : Nat.gcd n (Thm2.primorialBelow z) ≠ 0 := by
    intro h
    exact hP (Nat.gcd_eq_zero_iff.mp h).2
  have he : (Thm2.primorialBelow z).divisors.filter (fun d => d ∣ n) =
      (Nat.gcd n (Thm2.primorialBelow z)).divisors := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd, hdn⟩
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hdn (Nat.mem_divisors.mp hd).1, hg⟩
    · intro hd
      have h := (Nat.mem_divisors.mp hd).1
      exact ⟨Nat.mem_divisors.mpr ⟨h.trans (Nat.gcd_dvd_right _ _), hP⟩,
        h.trans (Nat.gcd_dvd_left _ _)⟩
  rw [he, sifted_weight_primorial]
  have h := congrArg (fun f : ArithmeticFunction ℝ => f (Nat.gcd n (Thm2.primorialBelow z)))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  symm
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using h

/-- Page 26, the truncated Möbius indicator in the c prime contribution.
This definition asserts no estimate for its remaining tail. -/
noncomputable def truncatedMobiusWeight (n : ℕ) (z γ : ℝ) : ℝ :=
  ∑ d ∈ (Thm2.primorialBelow z).divisors.filter (fun d => d ∣ n ∧ (d : ℝ) ≤ γ),
    (ArithmeticFunction.moebius d : ℝ)

/-- Page 26, exact full-tail partition at the truncation threshold.
This identity does not replace the stronger intermediate-band estimate cited there. -/
theorem truncated_mobius_partition (n : ℕ) (z γ : ℝ) :
    siftedWeight n ⌈z⌉₊ = truncatedMobiusWeight n z γ +
      ∑ d ∈ (Thm2.primorialBelow z).divisors.filter (fun d => d ∣ n ∧ γ < (d : ℝ)),
        (ArithmeticFunction.moebius d : ℝ) := by
  rw [sifted_mobius_expansion, truncatedMobiusWeight]
  have h := Finset.sum_filter_add_sum_filter_not
    ((Thm2.primorialBelow z).divisors.filter (fun d => d ∣ n))
    (fun d : ℕ => (d : ℝ) ≤ γ) (fun d => (ArithmeticFunction.moebius d : ℝ))
  simpa only [Finset.filter_filter, not_le] using h.symm

/-- Page 26, a conservative absolute full-tail bound at the truncation threshold.
It supplies no Hildebrand estimate for the smaller intermediate band. -/
theorem truncated_mobius_tail_bound (n : ℕ) (z γ : ℝ) :
    |siftedWeight n ⌈z⌉₊ - truncatedMobiusWeight n z γ| ≤
      (((Thm2.primorialBelow z).divisors.filter (fun d => d ∣ n ∧ γ < (d : ℝ))).card : ℝ) := by
  have he : siftedWeight n ⌈z⌉₊ - truncatedMobiusWeight n z γ =
      ∑ d ∈ (Thm2.primorialBelow z).divisors.filter (fun d => d ∣ n ∧ γ < (d : ℝ)),
        (ArithmeticFunction.moebius d : ℝ) := by
    linarith only [truncated_mobius_partition n z γ]
  rw [he]
  calc
    _ ≤ ∑ d ∈ (Thm2.primorialBelow z).divisors.filter (fun d => d ∣ n ∧ γ < (d : ℝ)),
        |(ArithmeticFunction.moebius d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ (Thm2.primorialBelow z).divisors.filter (fun d => d ∣ n ∧ γ < (d : ℝ)),
        (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    _ = _ := by simp

/-- Page 26, the truncation at 1 retains exactly the unit divisor. -/
theorem truncated_mobius_at_one (n : ℕ) (z : ℝ) : truncatedMobiusWeight n z 1 = 1 := by
  have hP : Thm2.primorialBelow z ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1.ne_zero
  have he : (Thm2.primorialBelow z).divisors.filter
      (fun d => d ∣ n ∧ (d : ℝ) ≤ 1) = {1} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, hdn, hd1⟩
      have hdn0 : d ≠ 0 := by
        intro h
        subst d
        exact hP (zero_dvd_iff.mp (Nat.mem_divisors.mp hd).1)
      have hd1' : d ≤ 1 := by exact_mod_cast hd1
      omega
    · intro h
      subst d
      exact ⟨Nat.mem_divisors.mpr ⟨one_dvd _, hP⟩, one_dvd _, by norm_num⟩
  rw [truncatedMobiusWeight, he]
  simp

/-- Page 26, a nonzero tail at a concrete truncation.
The truncated weight is 1 but the exact sifted indicator is 0. -/
theorem truncated_mobius_nontrivial_instance :
    truncatedMobiusWeight 6 4 1 = 1 ∧ siftedWeight 6 ⌈(4 : ℝ)⌉₊ = 0 := by
  exact ⟨truncated_mobius_at_one 6 4, by norm_num [siftedWeight, Nat.minFac_eq]⟩

/-- Page 26, the intermediate-band Möbius truncation used in Lemma 12.
The error is at most the number of common divisors in the band from gamma
to gamma times z. This is the finite fundamental-lemma step. It does not
assert the Hildebrand estimate for the band on page 27. -/
theorem fundamental_sifted_truncation (n : ℕ) (z γ : ℝ) (hγ : 1 ≤ γ) :
    |siftedWeight n ⌈z⌉₊ - truncatedMobiusWeight n z γ| ≤
      (((Thm2.primorialBelow z).divisors.filter
        (fun d : ℕ => d ∣ n ∧ γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * z)).card : ℝ) := by
  have hP : Thm2.primorialBelow z ≠ 0 := (primorial_squarefree z).ne_zero
  have hgs : Squarefree (Nat.gcd n (Thm2.primorialBelow z)) :=
    Squarefree.squarefree_of_dvd (Nat.gcd_dvd_right _ _) (primorial_squarefree z)
  have hg : Nat.gcd n (Thm2.primorialBelow z) ≠ 0 := hgs.ne_zero
  have he : (Thm2.primorialBelow z).divisors.filter (fun d => d ∣ n) =
      (Nat.gcd n (Thm2.primorialBelow z)).divisors := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd, hdn⟩
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hdn (Nat.mem_divisors.mp hd).1, hg⟩
    · intro hd
      have h := (Nat.mem_divisors.mp hd).1
      exact ⟨Nat.mem_divisors.mpr ⟨h.trans (Nat.gcd_dvd_right _ _), hP⟩,
        h.trans (Nat.gcd_dvd_left _ _)⟩
  have ht : truncatedMobiusWeight n z γ =
      ∑ d ∈ (Nat.gcd n (Thm2.primorialBelow z)).divisors.filter
        (fun d : ℕ => (d : ℝ) ≤ γ), (ArithmeticFunction.moebius d : ℝ) := by
    rw [truncatedMobiusWeight, ← Finset.filter_filter, he]
  have hb : (Thm2.primorialBelow z).divisors.filter
      (fun d : ℕ => d ∣ n ∧ γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * z) =
      (Nat.gcd n (Thm2.primorialBelow z)).divisors.filter
        (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * z) := by
    rw [← Finset.filter_filter, he]
  rw [sifted_weight_primorial, ht, hb]
  exact squarefree_mobius_truncation _ hgs hγ (fun p hp hpd =>
    prime_lt_of_dvd_primorial hp (hpd.trans (Nat.gcd_dvd_right _ _)))

/-- Page 26, display 4.7 with real coefficients and the exact dyadic ranges.
At positive k the divisible product determines the remaining variable. -/
noncomputable def sieveConvolution (M N : ℝ) (a b : ℕ → ℝ) (z : ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
    if m * n ∣ k then a m * b n * siftedWeight (k / (m * n)) ⌈z⌉₊ else 0

/-- Page 26, the c prime coefficient after the Möbius truncation. -/
noncomputable def truncatedConvolution (M N : ℝ) (a b : ℕ → ℝ) (z γ : ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
    if m * n ∣ k then a m * b n * truncatedMobiusWeight (k / (m * n)) z γ else 0

/-- Pages 26 and 27, the positive c double prime majorant before 4.11.
This definition asserts no analytic estimate for its size. -/
noncomputable def bandConvolutionMajorant (M N : ℝ) (a b : ℕ → ℝ) (z γ : ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
    if m * n ∣ k then |a m * b n| *
      (((Thm2.primorialBelow z).divisors.filter
        (fun d : ℕ => d ∣ k / (m * n) ∧ γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * z)).card : ℝ)
    else 0

/-- Page 26, the pointwise majorant for replacing 4.7 by c prime.
The finite fundamental-lemma bound controls every summand. No Hildebrand
estimate or character-distribution input is used. -/
theorem sieve_convolution_truncation (M N : ℝ) (a b : ℕ → ℝ) (z γ : ℝ)
    (k : ℕ) (hγ : 1 ≤ γ) :
    |sieveConvolution M N a b z k - truncatedConvolution M N a b z γ k| ≤
      bandConvolutionMajorant M N a b z γ k := by
  let S := Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊
  let T := Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊
  let f (m n : ℕ) : ℝ := if m * n ∣ k then a m * b n *
    (siftedWeight (k / (m * n)) ⌈z⌉₊ - truncatedMobiusWeight (k / (m * n)) z γ) else 0
  have he : sieveConvolution M N a b z k - truncatedConvolution M N a b z γ k =
      ∑ m ∈ S, ∑ n ∈ T, f m n := by
    unfold sieveConvolution truncatedConvolution
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : m * n ∣ k <;> simp [f, h, mul_sub]
  rw [he]
  calc
    _ ≤ ∑ m ∈ S, |∑ n ∈ T, f m n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ S, ∑ n ∈ T, |f m n| :=
      Finset.sum_le_sum (fun m hm => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ bandConvolutionMajorant M N a b z γ k := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      by_cases h : m * n ∣ k
      · simp only [f, h, ite_true, abs_mul]
        exact mul_le_mul_of_nonneg_left
          (fundamental_sifted_truncation (k / (m * n)) z γ hγ) (by positivity)
      · simp [f, h]

/-- Page 26, a nonempty convolution with a nonzero truncation error.
The singleton factor ranges both contain 1 and the remaining variable is 6. -/
theorem sieve_convolution_nonzero_error_instance :
    sieveConvolution 0.75 0.75 (fun _ => 1) (fun _ => 1) 4 6 = 0 ∧
      truncatedConvolution 0.75 0.75 (fun _ => 1) (fun _ => 1) 4 1 6 = 1 := by
  norm_num [sieveConvolution, truncatedConvolution, truncated_mobius_at_one,
    siftedWeight, Nat.minFac_eq, Finset.filter_singleton]

/-- Pages 26 and 27, the analytic band-sum bound gives the required absolute
approximation for the actual and truncated convolution families.
CONDITIONAL on that explicit band-sum estimate. -/
theorem approximation_of_band_sum {ε : ℝ} (M N z γ : ℝ → ℝ)
    (a b : ℝ → ℕ → ℝ)
    (hγ : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ γ x)
    (hband : ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
      (∑ k ∈ leftInterval ε x, bandConvolutionMajorant (M x) (N x) (a x) (b x) (z x) (γ x) k) ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    ShortApproximation ε
      (fun x k => sieveConvolution (M x) (N x) (a x) (b x) (z x) k)
      (fun x k => truncatedConvolution (M x) (N x) (a x) (b x) (z x) (γ x) k) := by
  obtain ⟨Xγ, hγ⟩ := Filter.eventually_atTop.mp hγ
  intro A hA
  obtain ⟨C, X, hC⟩ := hband A hA
  refine ⟨C, max X Xγ, ?_⟩
  intro x hx
  calc
    _ ≤ ∑ k ∈ leftInterval ε x,
        bandConvolutionMajorant (M x) (N x) (a x) (b x) (z x) (γ x) k :=
      Finset.sum_le_sum (fun k hk => sieve_convolution_truncation _ _ _ _ _ _ _
        (hγ x ((le_max_right _ _).trans hx)))
    _ ≤ _ := hC x ((le_max_left _ _).trans hx)

/-- LEAF. Pages 26 to 41, displays 4.7, 4.24 and 4.25, and the
Siegel Walfisz reference-interval calculation on page 33. Supply the lower
sifted family at one fixed positive divisor exponent and its auxiliary
Möbius-truncated family with both mean values 4.1, its I1 density and a
small absolute difference on I. Use the repaired 4.5 transfer and the
Lemma1112.lemma12_339_ok grouping range, not the unsupported printed 4.9
step. The numerical discarded-region classification is retained here. No short-window distribution conclusion is asserted. OPEN. -/
theorem lower_mean_value_supply (h4 : Thm4.Theorem4Paper) :
    ∃ B0 η : ℝ, 0 < B0 ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ (u0 : ℝ) (c0 b : ℝ → ℕ → ℝ),
        0.9953 < u0 ∧ u0 ≤ 1 ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        MeanValue41 ε b ∧ ReferenceDensity u0 b ∧
        ShortApproximation ε (section4SiftedFamily c0) b ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, section4SiftedFamily c0 x k ≤ Decomp132.primeWeight k := by
  sorry

/-- Pages 24 to 41. The exact sealed lower leaf follows from the two
smaller supply and Perron inputs. CONDITIONAL on those OPEN inputs.
The existing DecompC165b declaration is unchanged. -/
theorem section4_lower_sifted_data (h4 : Thm4.Theorem4Paper) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (u0 : ℝ) (c0 : ℝ → ℕ → ℝ),
        0.9953 < u0 ∧ u0 ≤ 1 ∧
        (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
          ∀ t : ℝ, t ≤ x →
            ‖∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t),
              ((section4SiftedFamily c0 x k : ℂ) * χ (k : ZMod q) -
                Thm2.delta χ * u0 / Real.log x)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, section4SiftedFamily c0 x k ≤ primeWeight k := by
  obtain ⟨B0, ηs, hB0, hηs, hs⟩ := lower_mean_value_supply h4
  obtain ⟨ηp, hηp, hp⟩ := perron_transfer B0
  refine ⟨B0, min ηs ηp, lt_min hηs hηp, ?_⟩
  intro B ε hB hε hεη
  obtain ⟨u, c, b, hu, hu1, hc, hb, hm, hd, happ, hlo⟩ := hs ε hε (lt_of_lt_of_le hεη (min_le_left _ _))
  have hr := hp ε hε (lt_of_lt_of_le hεη (min_le_right _ _))
    b hb hm
  exact ⟨u, c, hu, hu1, distribution_of_approximation happ (distribution_of_reference hε.le hr hd),
    divisor_bound_mono hB0 hB hc, hlo⟩

end LeanLab.BHP1997.Decomp312a
