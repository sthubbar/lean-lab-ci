/-
MMS https://arxiv.org/abs/1610.02017v2 pages 11 and 12.
Feed split of the ordered prime sum to integral passage in the Buchstab display.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp678a
import LeanLab.Ternary.Feed1122Decomp581bS145b

namespace LeanLab.Ternary.MMS.Task581.Feed1122
open Finset MeasureTheory

/-- LEAF: MMS page 11 bottom Buchstab display, continued on page 12, ordered
prime quadrature by partial summation in each prime coordinate. Class MEDIUM.
For every globally continuous kernel, the ordered triple sum against the three
logarithmic prime measure atoms log p over p log x tends to the ordered
integral of the kernel. Available inputs: the proved box limit
Task678.prime_log_box_tendsto, the diagonal bound prime_diagonal_mass_limit,
and uniform continuity of the kernel on the compact cube. This leaf has no
Buchstab function and no rough number input. -/
theorem ordered_prime_quadrature (K : (ℝ × ℝ) × ℝ → ℝ) (hK : Continuous K) :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |(∑ p ∈ primeTriples x,
          K ((Real.log p.1 / Real.log x, Real.log p.2.1 / Real.log x),
            Real.log p.2.2 / Real.log x) *
          ((Real.log p.1 / p.1) / Real.log x) *
          ((Real.log p.2.1 / p.2.1) / Real.log x) *
          ((Real.log p.2.2 / p.2.2) / Real.log x)) -
        ∫ a in (1 / 10 : ℝ)..(1 / 4 : ℝ),
          ∫ b in a..(1 / 4 : ℝ), ∫ c in b..(1 / 4 : ℝ), K ((a, b), c)| ≤ δ := by
  exact ordered_prime_quadrature_of_s145_leaves K hK

/-- The displayed Buchstab integral equals the ordered integral of the
clipped continuous kernel. MMS page 11 bottom display, domain check. -/
theorem profileIntegral_eq_extended :
    Task571.profileIntegral Task571.buchstabModel =
      ∫ a in (1 / 10 : ℝ)..(1 / 4 : ℝ), ∫ b in a..(1 / 4 : ℝ),
        ∫ c in b..(1 / 4 : ℝ), Task571.extendedKernel Task571.buchstabModel a b c := by
  unfold Task571.profileIntegral
  apply intervalIntegral.integral_congr
  intro a ha
  rw [Set.uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 4)] at ha
  apply intervalIntegral.integral_congr
  intro b hb
  rw [Set.uIcc_of_le ha.2] at hb
  apply intervalIntegral.integral_congr
  intro c hc
  rw [Set.uIcc_of_le hb.2] at hc
  exact (Task571.extendedKernel_eq ha.1 ha.2 hb.1 hb.2 hc.1 hc.2).symm

/-- The original cofactorModel_sum_limit statement, proved from the ordered
prime quadrature leaf with the clipped Buchstab kernel.
MMS page 11 bottom display and page 12.
CONDITIONAL ON ordered_prime_quadrature. -/
theorem cofactorModel_sum_limit_of_leaves :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |(∑ p ∈ primeTriples x, cofactorModel x p) -
        Task571.profileIntegral Task571.buchstabModel| ≤ δ := by
  intro δ hδ
  have hK : Continuous (fun q : (ℝ × ℝ) × ℝ =>
      Task571.extendedKernel Task571.buchstabModel q.1.1 q.1.2 q.2) :=
    Task571.extendedKernel_continuous (Task571.buchstabStage_continuous_clamp 8)
  obtain ⟨X, hX⟩ := ordered_prime_quadrature _ hK δ hδ
  refine ⟨max X 2, fun x hx => ?_⟩
  have hx1 : 1 < x := by linarith [le_max_right X 2]
  have h := hX x ((le_max_left X 2).trans hx)
  rw [profileIntegral_eq_extended]
  rw [sum_congr rfl (fun p hp => Task678.cofactorModel_eq_kernel_mass hx1 hp)]
  exact h


/-! ## Pass 2 split of cofactorMean_uniform -/

/-- LEAF: MMS page 11 bottom Buchstab display, continued on page 12, the cited
short interval prime number theorem at every rescaled cofactor scale.
Class HARD for Codex. CITED: for y equal to x over d at least x to the one
tenth, the primes in subintervals of length at most y times exp of minus the
square root of log x, about y exp of minus 3.17 times the square root of log y,
need an error term beating that length, for example the Vinogradov Korobov zero
free region or Huxley's short interval theorem. The lab StrongPNT envelope is
too weak, see Task571.pnt_envelope_not_half_referenceLength. Uniform in the
modulus d, which is what the Buchstab recursion over the cofactor primes uses.
This leaf has no rough numbers and no Buchstab function. -/
theorem shortIntervalPNT_scaled :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ x ^ (9 / 10 : ℝ) → ∀ a b : ℝ, x ≤ a → a ≤ b →
      b ≤ x + Task379.referenceLength x →
      |Real.log (x / d) * (((ints (x / d) ((x + Task379.referenceLength x) / d)).filter
          (fun m : ℕ => m.Prime ∧ a < (d : ℝ) * m ∧ (d : ℝ) * m < b)).card : ℝ) -
          (b - a) / d| ≤ ε * Task379.referenceLength x / d := by
  sorry

/-- LEAF: MMS page 11 bottom display, Buchstab recursion for the rough cofactor
n over p one p two p three, summed over its least prime factor, density frozen
at u equal to log of x over d over log p one. Class HARD for Codex.
The last prime of the recursion lies in a short interval at scale at least x to
the one tenth, where the cited input applies. CONDITIONAL ON the cited
shortIntervalPNT_scaled, the hypothesis. No smooth weight, no layer cake. -/
theorem roughCount_of_shortIntervalPNT
    (hPNT : ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ x ^ (9 / 10 : ℝ) → ∀ a b : ℝ, x ≤ a → a ≤ b →
      b ≤ x + Task379.referenceLength x →
      |Real.log (x / d) * (((ints (x / d) ((x + Task379.referenceLength x) / d)).filter
          (fun m : ℕ => m.Prime ∧ a < (d : ℝ) * m ∧ (d : ℝ) * m < b)).card : ℝ) -
          (b - a) / d| ≤ ε * Task379.referenceLength x / d) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p ∈ primeTriples x,
      ∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
          if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
            Task361.roughIndicator (n / tripleProduct p) p.1 else 0) -
          (b - a) * cofactorModel x p| ≤
        ε * Task379.referenceLength x / tripleProduct p := by
  sorry


/-- Pass 6 helper for the finite layer cake step of cofactorMean_transfer,
MMS page 11 bottom display: one level indicator is integrable. -/
theorem layer_term_integrable (w M c : ℝ) (hw : 0 ≤ w) (hM : w ≤ M) :
    IntervalIntegrable (fun s : ℝ => if s < w then c else 0) volume 0 M := by
  have h1 : IntervalIntegrable (fun s : ℝ => if s < w then c else 0) volume 0 w := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hw]
    refine IntegrableOn.congr_fun_ae (f := fun _ => c) (integrableOn_const (by simp)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (Measure.ae_ne volume w).filter_mono ae_restrict_le] with s hs hne
    simp [lt_of_le_of_ne hs.2 hne]
  have h2 : IntervalIntegrable (fun s : ℝ => if s < w then c else 0) volume w M := by
    refine (intervalIntegrable_const (c := (0:ℝ))).congr ?_
    rw [Set.uIoc_of_le hM]
    intro s hs
    simp [not_lt.mpr hs.1.le]
  exact h1.trans h2

/-- Pass 6 helper, MMS page 11 bottom display, layer cake for one term:
the integral over levels of one indicator recovers the weight. -/
theorem layer_term (w M c : ℝ) (hw : 0 ≤ w) (hM : w ≤ M) :
    ∫ s in (0:ℝ)..M, (if s < w then c else 0) = w * c := by
  have h2 : IntervalIntegrable (fun s : ℝ => if s < w then c else 0) volume w M := by
    refine (intervalIntegrable_const (c := (0:ℝ))).congr ?_
    rw [Set.uIoc_of_le hM]
    intro s hs
    simp [not_lt.mpr hs.1.le]
  have h1 : IntervalIntegrable (fun s : ℝ => if s < w then c else 0) volume 0 w := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hw]
    refine IntegrableOn.congr_fun_ae (f := fun _ => c) (integrableOn_const (by simp)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (Measure.ae_ne volume w).filter_mono ae_restrict_le] with s hs hne
    simp [lt_of_le_of_ne hs.2 hne]
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have e1 : ∫ s in (0:ℝ)..w, (if s < w then c else 0) = ∫ s in (0:ℝ)..w, c := by
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le hw]
    filter_upwards [Measure.ae_ne volume w] with s hne hs
    simp [lt_of_le_of_ne hs.2 hne]
  have e2 : ∫ s in w..M, (if s < w then c else 0) = ∫ s in w..M, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hM] at hs
    simp [not_lt.mpr hs.1]
  rw [e1, e2]; simp

/-- Pass 6, finite layer cake identity for the layer cake step of
cofactorMean_transfer, MMS page 11 bottom display: a weighted finite sum is
the integral over levels s of the sums over the superlevel sets. -/
theorem finite_layer_cake {ι : Type*} (S : Finset ι) (w f : ι → ℝ) (M : ℝ)
    (hw : ∀ n ∈ S, 0 ≤ w n) (hM : ∀ n ∈ S, w n ≤ M) :
    ∑ n ∈ S, w n * f n =
      ∫ s in (0:ℝ)..M, ∑ n ∈ S, (if s < w n then f n else 0) := by
  rw [intervalIntegral.integral_finsetSum
    (fun n hn => layer_term_integrable _ _ _ (hw n hn) (hM n hn))]
  exact Finset.sum_congr rfl (fun n hn => (layer_term _ _ _ (hw n hn) (hM n hn)).symm)

/-- Pass 6, the finite layer cake identity applied to the numerator of
cofactorMean, MMS page 11 equation 5.1. Any upper bound M of the weight works. -/
theorem cofactorNumerator_layer_cake (x : ℝ) (p : ℕ × ℕ × ℕ) (M : ℝ)
    (hM : ∀ n : ℕ, Task379.referenceWeight x n ≤ M) :
    (∑ n ∈ ints x (x + Task379.referenceLength x),
      if tripleProduct p ∣ n then
        Task379.referenceWeight x n * Task361.roughIndicator (n / tripleProduct p) p.1
      else 0) =
    ∫ s in (0:ℝ)..M, ∑ n ∈ ints x (x + Task379.referenceLength x),
      (if s < Task379.referenceWeight x n then
        (if tripleProduct p ∣ n then Task361.roughIndicator (n / tripleProduct p) p.1
          else 0) else 0) := by
  rw [← finite_layer_cake _ (fun n : ℕ => Task379.referenceWeight x n)
    (fun n : ℕ => if tripleProduct p ∣ n then
      Task361.roughIndicator (n / tripleProduct p) p.1 else 0) M
    (fun n _ => Task379.referenceWeight_nonneg x n) (fun n _ => hM n)]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  split_ifs <;> simp

/-- Pass 6 helper: the flat exponential factor is at most one. Derived bound
for the chosen g1 of MMS page 11 Proposition 5.1. -/
theorem expNegInvGlue_le_one' (x : ℝ) : expNegInvGlue x ≤ 1 := by
  unfold expNegInvGlue
  split_ifs with h
  · norm_num
  · push Not at h
    exact Real.exp_le_one_iff.mpr (by have := inv_pos.mpr h; linarith)

/-- Pass 6 helper: the reference weight is at most one, so M equal to one is
an admissible level bound. Derived bound for MMS page 11 Proposition 5.1. -/
theorem referenceWeight_le_one (x t : ℝ) : Task379.referenceWeight x t ≤ 1 := by
  unfold Task379.referenceWeight
  have h1 := expNegInvGlue_le_one' ((t - x) / Task379.referenceLength x)
  have h2 := expNegInvGlue_le_one' (1 - (t - x) / Task379.referenceLength x)
  have h3 := expNegInvGlue.nonneg ((t - x) / Task379.referenceLength x)
  have h4 := expNegInvGlue.nonneg (1 - (t - x) / Task379.referenceLength x)
  nlinarith

/-- Pass 6, level step of the layer cake for cofactorMean_transfer, MMS page 11
bottom display: when the superlevel set at level s of the weight is the open
interval from a to b on the integers, the level sum is the interval rough
cofactor count of the hypothesis. -/
theorem levelSum_eq_intervalCount (x s a b : ℝ) (p : ℕ × ℕ × ℕ)
    (hlev : ∀ n : ℕ, s < Task379.referenceWeight x n ↔ a < (n : ℝ) ∧ (n : ℝ) < b) :
    (∑ n ∈ ints x (x + Task379.referenceLength x),
      (if s < Task379.referenceWeight x n then
        (if tripleProduct p ∣ n then Task361.roughIndicator (n / tripleProduct p) p.1
          else 0) else 0)) =
    ∑ n ∈ ints x (x + Task379.referenceLength x),
      if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
        Task361.roughIndicator (n / tripleProduct p) p.1 else 0 := by
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h1 : s < Task379.referenceWeight x n <;>
    by_cases h2 : tripleProduct p ∣ n <;> simp_all

section S145_cofactorMean_transfer
open Finset MeasureTheory

theorem s145_profile_level (s : ℝ) (hs : 0 < s) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 / 2 ∧ ∀ u : ℝ,
      s < expNegInvGlue u * expNegInvGlue (1 - u) ↔ |u - 1 / 2| < r := by
  rcases le_or_gt 1 s with h1 | h1
  · refine ⟨0, le_refl _, by norm_num, fun u => ?_⟩
    have a1 := expNegInvGlue_le_one' u
    have a2 := expNegInvGlue_le_one' (1 - u)
    have a3 := expNegInvGlue.nonneg u
    have a4 := expNegInvGlue.nonneg (1 - u)
    constructor
    · intro h; nlinarith
    · intro h; exact absurd h (not_lt.mpr (abs_nonneg _))
  have hlog : Real.log s < 0 := Real.log_neg hs h1
  set k : ℝ := (-Real.log s)⁻¹ with hk
  have hk0 : 0 < k := inv_pos.mpr (by linarith)
  refine ⟨Real.sqrt (max (1 / 4 - k) 0), Real.sqrt_nonneg _, ?_, fun u => ?_⟩
  · rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (max_le (by linarith) (by norm_num))
  rw [Real.lt_sqrt (abs_nonneg _), sq_abs]
  by_cases hu : 0 < u ∧ u < 1
  · obtain ⟨hu0, hu1⟩ := hu
    have h1u : 0 < 1 - u := by linarith
    simp only [expNegInvGlue, not_le.mpr hu0, not_le.mpr h1u, ite_false, ← Real.exp_add]
    have e1 : -u⁻¹ + -(1 - u)⁻¹ = -(u * (1 - u))⁻¹ := by field_simp; ring
    rw [e1, ← Real.log_lt_iff_lt_exp hs]
    have hq : 0 < u * (1 - u) := mul_pos hu0 h1u
    have step : Real.log s < -(u * (1 - u))⁻¹ ↔ k < u * (1 - u) := by
      rw [hk, inv_lt_comm₀ (by linarith) hq]
      constructor <;> intro h <;> linarith
    rw [step]
    constructor
    · intro h
      calc (u - 1 / 2) ^ 2 = 1 / 4 - u * (1 - u) := by ring
        _ < 1 / 4 - k := by linarith
        _ ≤ max (1 / 4 - k) 0 := le_max_left _ _
    · intro h
      rcases le_total (1 / 4 - k) 0 with h2 | h2
      · rw [max_eq_right h2] at h; nlinarith [sq_nonneg (u - 1 / 2)]
      · rw [max_eq_left h2] at h; nlinarith
  · have hz : expNegInvGlue u * expNegInvGlue (1 - u) = 0 := by
      rcases le_or_gt u 0 with h0 | h0
      · rw [expNegInvGlue.zero_of_nonpos h0, zero_mul]
      · have : 1 ≤ u := by by_contra hc; exact hu ⟨h0, by linarith⟩
        rw [expNegInvGlue.zero_of_nonpos (by linarith : 1 - u ≤ 0), mul_zero]
    rw [hz]
    constructor
    · intro h; linarith
    · intro h
      exfalso
      have hb : (1 / 4 : ℝ) ≤ (u - 1 / 2) ^ 2 := by
        rcases le_or_gt u 0 with h0 | h0
        · nlinarith
        · have : 1 ≤ u := by by_contra hc; exact hu ⟨h0, by linarith⟩
          nlinarith
      have : max (1 / 4 - k) 0 ≤ 1 / 4 := max_le (by linarith) (by norm_num)
      linarith


theorem s145_weight_level {x : ℝ} (hx : 0 < x) (s : ℝ) (hs : 0 < s) :
    ∃ a b : ℝ, x ≤ a ∧ a ≤ b ∧ b ≤ x + Task379.referenceLength x ∧
      ∀ t : ℝ, s < Task379.referenceWeight x t ↔ a < t ∧ t < b := by
  have hL := Task379.referenceLength_pos hx
  set L := Task379.referenceLength x with hLdef
  obtain ⟨r, hr0, hr1, hr⟩ := s145_profile_level s hs
  refine ⟨x + L * (1 / 2 - r), x + L * (1 / 2 + r), ?_, ?_, ?_, fun t => ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  unfold Task379.referenceWeight
  rw [← hLdef, hr, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : (1 / 2 - r) < (t - x) / L := by linarith
    have e2 : (t - x) / L < 1 / 2 + r := by linarith
    rw [lt_div_iff₀ hL] at e1
    rw [div_lt_iff₀ hL] at e2
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    have e1 : (1 / 2 - r) < (t - x) / L := by rw [lt_div_iff₀ hL]; nlinarith
    have e2 : (t - x) / L < 1 / 2 + r := by rw [div_lt_iff₀ hL]; nlinarith
    constructor <;> linarith

theorem s145_profile_rescale_integral (x L : ℝ) (hL : 0 < L) :
    (∫ t in x..(x + L), expNegInvGlue ((t - x) / L) * expNegInvGlue (1 - (t - x) / L)) =
      L * ∫ s in (0:ℝ)..1, expNegInvGlue s * expNegInvGlue (1 - s) := by
  have h := intervalIntegral.integral_comp_div_sub
    (fun s => expNegInvGlue s * expNegInvGlue (1 - s)) (c := L) (d := x / L) hL.ne'
    (a := x) (b := x + L)
  simp only [sub_div] at *
  rw [h]
  have e1 : x / L - x / L = 0 := sub_self _
  have e2 : (x + L) / L - x / L = 1 := by field_simp; ring
  rw [e1, e2, smul_eq_mul]

theorem s145_profile_integral_pos :
    0 < ∫ s in (0:ℝ)..1, expNegInvGlue s * expNegInvGlue (1 - s) := by
  have hc : Continuous (fun s : ℝ => expNegInvGlue s * expNegInvGlue (1 - s)) := by
    fun_prop
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _) _ zero_lt_one
  intro s hs
  exact mul_pos (expNegInvGlue.pos_of_pos hs.1) (expNegInvGlue.pos_of_pos (by linarith [hs.2]))

/-- Layer cake for the weight integral over the reference interval. -/
theorem s145_weight_layer {x : ℝ} (hx : 0 < x) :
    (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t) =
      ∫ s in (0:ℝ)..1, ((volume.restrict (Set.Ioc x (x + Task379.referenceLength x))).real
        {t | s < Task379.referenceWeight x t}) := by
  have hL := Task379.referenceLength_pos hx
  set L := Task379.referenceLength x with hLdef
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le zero_le_one]
  have hint : Integrable (Task379.referenceWeight x) (volume.restrict (Set.Ioc x (x + L))) :=
    ((Task379.referenceWeight_contDiff x 0).continuous.integrableOn_Icc).mono_set
      Set.Ioc_subset_Icc_self
  rw [hint.integral_eq_integral_meas_lt
    (Filter.Eventually.of_forall fun t => Task379.referenceWeight_nonneg x t)]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Set.Ioc_subset_Ioi_self
  intro s hs
  have hs1 : 1 < s := by
    rcases hs with ⟨h1, h2⟩
    simp only [Set.mem_Ioi] at h1
    simp only [Set.mem_Ioc, not_and, not_le] at h2
    exact h2 h1
  have he : {t | s < Task379.referenceWeight x t} = ∅ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    linarith [referenceWeight_le_one x t]
  rw [he, measureReal_empty]

theorem cofactorMean_transfer_s145 :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ p ∈ primeTriples x, ∀ ε : ℝ, 0 ≤ ε →
      (∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
        |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
            if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
              Task361.roughIndicator (n / tripleProduct p) p.1 else 0) -
            (b - a) * cofactorModel x p| ≤
          ε * Task379.referenceLength x / tripleProduct p) →
      |cofactorMean x p - cofactorModel x p| ≤ C * ε / tripleProduct p := by
  set c0 := ∫ s in (0:ℝ)..1, expNegInvGlue s * expNegInvGlue (1 - s) with hc0
  have hc0p : 0 < c0 := s145_profile_integral_pos
  refine ⟨1 / c0, by positivity, fun x hx p hp ε hε hyp => ?_⟩
  have hx0 : 0 < x := by linarith
  have hL := Task379.referenceLength_pos hx0
  set L := Task379.referenceLength x with hLdef
  have hd : (0 : ℝ) < tripleProduct p := by exact_mod_cast tripleProduct_pos hp
  set d : ℝ := (tripleProduct p : ℝ) with hddef
  set μ := volume.restrict (Set.Ioc x (x + L)) with hμ
  set m : ℝ → ℝ := fun s => μ.real {t | s < Task379.referenceWeight x t} with hmdef
  set F : ℕ → ℝ := fun n => if tripleProduct p ∣ n then
    Task361.roughIndicator (n / tripleProduct p) p.1 else 0 with hF
  set cnt : ℝ → ℝ := fun s => ∑ n ∈ ints x (x + L),
      (if s < Task379.referenceWeight x n then F n else 0) with hcnt
  set N := ∑ n ∈ ints x (x + L),
    if tripleProduct p ∣ n then
      Task379.referenceWeight x n * Task361.roughIndicator (n / tripleProduct p) p.1
    else 0 with hN
  set I := ∫ t in x..(x + L), Task379.referenceWeight x t with hIdef
  -- weight integral scaling
  have hIs : I = c0 * L := by
    rw [hIdef]
    unfold Task379.referenceWeight
    rw [← hLdef, s145_profile_rescale_integral x L hL, mul_comm]
  have hIp : 0 < I := by rw [hIs]; positivity
  -- layer cakes
  have hNl : N = ∫ s in (0:ℝ)..1, cnt s :=
    cofactorNumerator_layer_cake x p 1 (fun n => referenceWeight_le_one x n)
  have hIl : I = ∫ s in (0:ℝ)..1, m s := s145_weight_layer hx0
  -- integrability
  have hcntI : IntervalIntegrable cnt volume 0 1 := by
    have := IntervalIntegrable.sum (μ := volume) (a := (0:ℝ)) (b := 1) (ints x (x + L))
      (f := fun n s => if s < Task379.referenceWeight x n then F n else 0)
      (fun n _ => layer_term_integrable _ _ _ (Task379.referenceWeight_nonneg x n)
        (referenceWeight_le_one x n))
    refine this.congr ?_
    intro s _
    simp [hcnt, Finset.sum_apply]
  have hmanti : Antitone m := by
    intro s1 s2 h12
    simp only [hmdef]
    apply measureReal_mono
    · intro t ht
      simp only [Set.mem_ofPred_eq] at ht ⊢
      linarith
    · apply ne_of_lt
      calc μ {t | s1 < Task379.referenceWeight x t} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = volume (Set.Ioc x (x + L)) := Measure.restrict_apply_univ _
        _ < ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hmI : IntervalIntegrable m volume 0 1 := hmanti.intervalIntegrable
  -- pointwise bound
  have hpt : ∀ s ∈ Set.uIoc (0:ℝ) 1,
      ‖Real.log x * cnt s - m s * cofactorModel x p‖ ≤ ε * L / d := by
    intro s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    obtain ⟨a, b, hxa, hab, hbL, hlev⟩ := s145_weight_level hx0 s hs.1
    have hcs : cnt s = ∑ n ∈ ints x (x + L),
        if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
          Task361.roughIndicator (n / tripleProduct p) p.1 else 0 :=
      levelSum_eq_intervalCount x s a b p (fun n => hlev n)
    have hms : m s = b - a := by
      simp only [hmdef]
      have hset : {t | s < Task379.referenceWeight x t} = Set.Ioo a b := by
        ext t; simp [hlev t]
      rw [hset, hμ, measureReal_restrict_apply measurableSet_Ioo,
        Set.inter_eq_left.mpr (show Set.Ioo a b ⊆ Set.Ioc x (x + L) from
          fun t ht => ⟨lt_of_le_of_lt hxa ht.1, (ht.2.trans_le hbL).le⟩),
        Real.volume_real_Ioo_of_le hab]
    rw [Real.norm_eq_abs, hcs, hms]
    exact hyp a b hxa hab hbL
  have hdiff : Real.log x * N - I * cofactorModel x p =
      ∫ s in (0:ℝ)..1, (Real.log x * cnt s - m s * cofactorModel x p) := by
    rw [intervalIntegral.integral_sub (hcntI.const_mul _) (hmI.mul_const _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const, hNl, hIl]
  have hbound : |Real.log x * N - I * cofactorModel x p| ≤ ε * L / d := by
    rw [hdiff]
    have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    simpa using this
  have hmean : cofactorMean x p = Real.log x * N / I := rfl
  rw [hmean]
  have he : Real.log x * N / I - cofactorModel x p =
      (Real.log x * N - I * cofactorModel x p) / I := by field_simp
  rw [he, abs_div, abs_of_pos hIp, div_le_iff₀ hIp]
  calc _ ≤ ε * L / d := hbound
    _ = 1 / c0 * ε / d * I := by rw [hIs]; field_simp

end S145_cofactorMean_transfer

/-- LEAF: MMS page 11 bottom display, passage from interval rough cofactor
counts to the smooth weighted cofactor mean. Class MEDIUM for Open Math OS.
Deterministic layer cake step, as in primeMean_transfer of the Decomp581a
split: the reference weight is unimodal and vanishes at both ends of the
reference interval, so each superlevel set is an open subinterval, and the
weighted sum and the weight integral are integrals over levels of counts and
lengths. One may take C equal to the maximum of the profile over its integral.
This leaf has no prime number theorem and no Buchstab recursion. -/
theorem cofactorMean_transfer :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ p ∈ primeTriples x, ∀ ε : ℝ, 0 ≤ ε →
      (∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
        |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
            if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
              Task361.roughIndicator (n / tripleProduct p) p.1 else 0) -
            (b - a) * cofactorModel x p| ≤
          ε * Task379.referenceLength x / tripleProduct p) →
      |cofactorMean x p - cofactorModel x p| ≤ C * ε / tripleProduct p := by
  exact cofactorMean_transfer_s145

/-- The original cofactorMean_uniform statement from the three leaves above.
MMS page 11 bottom display and page 12. CONDITIONAL ON shortIntervalPNT_scaled,
roughCount_of_shortIntervalPNT and cofactorMean_transfer. -/
theorem cofactorMean_uniform_of_leaves :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ p ∈ primeTriples x,
        |cofactorMean x p - cofactorModel x p| ≤ δ / (tripleProduct p : ℝ) := by
  intro δ hδ
  obtain ⟨C, hC, hT⟩ := cofactorMean_transfer
  obtain ⟨X, hX⟩ := roughCount_of_shortIntervalPNT shortIntervalPNT_scaled (δ / C)
    (by positivity)
  refine ⟨max X 2, fun x hx p hp => ?_⟩
  have hx1 : 1 < x := by linarith [le_max_right X 2]
  have h := hT x hx1 p hp (δ / C) (by positivity)
    (hX x ((le_max_left _ _).trans hx) p hp)
  have he : C * (δ / C) / (tripleProduct p : ℝ) = δ / (tripleProduct p : ℝ) := by
    field_simp
  rwa [he] at h

end LeanLab.Ternary.MMS.Task581.Feed1122
