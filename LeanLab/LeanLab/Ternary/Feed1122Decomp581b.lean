/-
MMS https://arxiv.org/abs/1610.02017v2 pages 11 and 12.
Feed split of the ordered prime sum to integral passage in the Buchstab display.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp678a

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
  sorry

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
  sorry

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
