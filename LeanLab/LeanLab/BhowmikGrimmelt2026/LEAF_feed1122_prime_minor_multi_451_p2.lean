/-
Helpers for LEAF_feed1122_prime_minor_multi_451, P0029 page 27, proof of Lemma 7.3,
display 7.8, the minor arc part for the prime restricted smoothed sum.

* `nonprime_partial_aux451`: the higher prime powers cost at most the Chebyshev difference
  psi minus theta, bounded through Mathlib's `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`.
* `Cphi451` is the smoothed sum with an arbitrary coefficient sequence c bounded between zero
  and the von Mangoldt function. The proofs of `Sphi_increment_energy261`,
  `supported_increment261` and `supported_family_sharp261` are repeated for it, since
  Parseval only needs the coefficient bound. The prime restricted sum is the case
  c n = Lambda n on primes and zero elsewhere.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp451a
import LeanLab.BhowmikGrimmelt2026.SPLIT_minor_bare_family328
import LeanLab.BhowmikGrimmelt2026.SharpSupported261

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction NNReal

attribute [local instance] Classical.propDecidable

/-- The higher prime powers part of a partial von Mangoldt sum, the statement of
`leaf_nonprime_partial_feed1122`. -/
theorem nonprime_partial_aux451 {X m : ℕ} (hX : 2 ≤ X) (hm : m ≤ X) (α : ℝ) :
    ‖Ssum m α - ∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime),
        (vonMangoldt n : ℂ) * ee (α * n)‖ ≤
      2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 := by
  have hsplit : Ssum m α - ∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime),
        (vonMangoldt n : ℂ) * ee (α * n) =
      ∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime),
        (vonMangoldt n : ℂ) * ee (α * n) := by
    unfold Ssum
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 m) (fun n => n.Prime)]
    ring
  rw [hsplit]
  have h1 : ‖∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime),
        (vonMangoldt n : ℂ) * ee (α * n)‖ ≤
      ∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), vonMangoldt n := by
    apply norm_sum_le_of_le
    intro n _
    simp [ee_eq_library84, LeanLab.PNTPort.LargeSieve.norm_e, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
  have h2 : (∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ n.Prime), vonMangoldt n) ≤
      ∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime), vonMangoldt n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl hm)
    · intro n _ _
      exact vonMangoldt_nonneg
  have hlogX : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  have hrhs : 0 ≤ 2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 := by positivity
  refine h1.trans (h2.trans ?_)
  by_cases hX4 : X ≤ 3
  · have hz : (∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime), vonMangoldt n) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnX⟩, hnp⟩ := hn
      have hn3 : n ≤ 3 := by omega
      have : n = 1 := by
        interval_cases n
        · rfl
        · exact absurd Nat.prime_two hnp
        · exact absurd Nat.prime_three hnp
      subst this
      simp
    rw [hz]
    exact hrhs
  · push Not at hX4
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
    have hX4' : (4 : ℝ) ≤ X := by exact_mod_cast hX4
    have heq : (∑ n ∈ (Finset.Icc 1 X).filter (fun n => ¬ n.Prime), vonMangoldt n) =
        Chebyshev.psi X - Chebyshev.theta X := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast,
        Finset.sum_filter, Finset.sum_filter]
      have hI : Finset.Icc 1 X = Finset.Ioc 0 X := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
      rw [hI]
    have hb := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hX1
    have hle := (le_abs_self _).trans hb
    rw [heq]
    refine hle.trans ?_
    have hsq : Real.sqrt X ≤ (X : ℝ) ^ (4 / 5 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    have hlog1 : 1 ≤ Real.log X := by
      have h4 : Real.log 4 ≤ Real.log X := Real.log_le_log (by norm_num) hX4'
      have h42 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_gt_d9
      linarith
    have hlsq : Real.log X ≤ Real.log X ^ 2 := by nlinarith
    have hp : 0 ≤ (X : ℝ) ^ (4 / 5 : ℝ) := by positivity
    calc
      2 * Real.sqrt X * Real.log X ≤ 2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X := by
        gcongr
      _ ≤ _ := by gcongr

/-- The smoothed sum with an arbitrary coefficient sequence. -/
noncomputable def Cphi451 (c : ℕ → ℝ) (ϕ : ℝ → ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), ((c n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)

theorem continuous_Cphi451 (c : ℕ → ℝ) (ϕ : ℝ → ℝ) (N : ℕ) :
    Continuous (Cphi451 c ϕ N) := by
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul (ee_contDiff.continuous.comp (continuous_id.mul continuous_const))

theorem Cphi_uniform451 {c : ℕ → ℝ} (hc0 : ∀ n, 0 ≤ c n) (hcL : ∀ n, c n ≤ vonMangoldt n)
    {ϕ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) (N : ℕ) (α : ℝ) :
    ‖Cphi451 c ϕ N α‖ ≤ 6 * M * N := by
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1),
        ‖((c n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (N + 1), vonMangoldt n * M := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul, ee_eq_library84, LeanLab.PNTPort.LargeSieve.norm_e,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (hc0 n)]
      exact mul_le_mul (hcL n) (hbound _) (abs_nonneg _) vonMangoldt_nonneg
    _ = (∑ n ∈ Finset.range (N + 1), vonMangoldt n) * M := by rw [Finset.sum_mul]
    _ ≤ 6 * M * N := by nlinarith [mul_le_mul_of_nonneg_right (mangoldt_mass261 N) hM]

theorem Cphi_extend451 {c : ℕ → ℝ} {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {N X : ℕ} (hNX : N ≤ X)
    (α : ℝ) :
    Cphi451 c ϕ N α = ∑ n ∈ Finset.range (X + 1),
      ((c n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n) := by
  unfold Cphi451
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro n _ hnN
  have hnN' : N < n := by simp only [Finset.mem_range] at hnN; omega
  by_cases hN : N = 0
  · subst N
    have hz : ϕ 0 = 0 := by
      by_contra h
      have hs := hϕ.supp (subset_tsupport ϕ h)
      linarith [hs.1]
    simp [hz]
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
    have hn : (N : ℝ) ≤ n := by exact_mod_cast hnN'.le
    rw [phi_zero_ge_one261 hϕ ((le_div_iff₀ hNpos).mpr (by simpa using hn))]
    simp

theorem Cphi_increment451 {c : ℕ → ℝ} {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (N : ℕ) (α : ℝ) :
    Cphi451 c ϕ N α - Cphi451 c ϕ (N - 1) α =
      ∑ n ∈ Finset.range (N + 1),
        ((c n * (ϕ (n / N) - ϕ (n / (N - 1 : ℕ))) : ℝ) : ℂ) * ee (α * n) := by
  rw [Cphi_extend451 hϕ (show N - 1 ≤ N by omega) α]
  unfold Cphi451
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

theorem Cphi_increment_energy451 {c : ℕ → ℝ} (hc0 : ∀ n, 0 ≤ c n)
    (hcL : ∀ n, c n ≤ vonMangoldt n) {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    {L : ℝ≥0} (hL : LipschitzWith L ϕ) {N : ℕ} (hN : 2 ≤ N) :
    (∫ α in (0 : ℝ)..1, ‖Cphi451 c ϕ N α - Cphi451 c ϕ (N - 1) α‖ ^ 2) ≤
      6 * (L : ℝ) ^ 2 * Real.log N / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hprev : (0 : ℝ) < (N - 1 : ℕ) := by exact_mod_cast (by omega : 0 < N - 1)
  have hcut (n : ℕ) (hn : n ∈ Finset.range (N + 1)) :
      |ϕ ((n : ℝ) / N) - ϕ ((n : ℝ) / (N - 1 : ℕ))| ≤ (L : ℝ) / N := by
    have hnN : n ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
    by_cases hn' : n ≤ N - 1
    · exact phi_scale_increment261 hL hN hn'
    · have heq : n = N := by omega
      subst n
      rw [div_self hNpos.ne', phi_zero_ge_one261 hϕ le_rfl,
        phi_zero_ge_one261 hϕ ((le_div_iff₀ hprev).mpr (by
          have hh : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N - 1 ≤ N)
          simpa using hh))]
      simp only [sub_self, abs_zero]
      positivity
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
  simp_rw [Cphi_increment451 hϕ N]
  rw [finite_parseval261]
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1), vonMangoldt n ^ 2 * ((L : ℝ) / N) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, mul_pow, sq_abs]
      exact mul_le_mul (pow_le_pow_left₀ (hc0 n) (hcL n) 2)
        (pow_le_pow_left₀ (abs_nonneg _) (hcut n hn) 2) (sq_nonneg _) (sq_nonneg _)
    _ = ((L : ℝ) / N) ^ 2 * ∑ n ∈ Finset.range (N + 1), vonMangoldt n ^ 2 := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ ((L : ℝ) / N) ^ 2 * (6 * N * Real.log N) :=
      mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
    _ = _ := by field_simp

theorem Cphi_multiplier_memLp451 {c : ℕ → ℝ} (hc0 : ∀ n, 0 ≤ c n)
    (hcL : ∀ n, c n ≤ vonMangoldt n) {ϕ : ℝ → ℝ} {M B : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x, |ϕ x| ≤ M)
    {W : ℝ → ℂ} (hW : Measurable W) (hB : 0 ≤ B) (hWB : ∀ α, ‖W α‖ ≤ B)
    (N : ℕ) :
    MemLp (fun α => Cphi451 c ϕ N α ^ 2 * W α) 2 (volume.restrict (Set.Ioc 0 1)) := by
  apply MemLp.of_bound
    (((continuous_Cphi451 c ϕ N).pow 2).measurable.mul hW).aestronglyMeasurable
    ((6 * M * N) ^ 2 * B)
  apply Filter.Eventually.of_forall
  intro α
  change ‖Cphi451 c ϕ N α ^ 2 * W α‖ ≤ _
  rw [norm_mul, norm_pow]
  exact mul_le_mul
    (pow_le_pow_left₀ (norm_nonneg _) (Cphi_uniform451 hc0 hcL hM hbound N α) 2)
    (hWB α) (norm_nonneg _) (sq_nonneg _)

theorem Cphi_supported_increment451 {c : ℕ → ℝ} (hc0 : ∀ n, 0 ≤ c n)
    (hcL : ∀ n, c n ≤ vonMangoldt n) {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, |ϕ x| ≤ M)
    {L : ℝ≥0} (hL : LipschitzWith L ϕ) {X N : ℕ} (hN : 2 ≤ N) (hNX : N ≤ X)
    {W : ℝ → ℂ} (hW : Measurable W) {B U : ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U)
    (hWB : ∀ α, ‖W α‖ ≤ B)
    (hsup : ∀ n ≤ X, ∀ α, W α ≠ 0 → ‖Cphi451 c ϕ n α‖ ≤ U) :
    (∫ α in (0 : ℝ)..1,
      ‖Cphi451 c ϕ N α ^ 2 * W α - Cphi451 c ϕ (N - 1) α ^ 2 * W α‖ ^ 2) ≤
        24 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * Real.log N / N := by
  have hLp := (Cphi_multiplier_memLp451 hc0 hcL hM hbound hW hB hWB N).sub
    (Cphi_multiplier_memLp451 hc0 hcL hM hbound hW hB hWB (N - 1))
  have hi : IntervalIntegrable
      (fun α => ‖Cphi451 c ϕ N α ^ 2 * W α - Cphi451 c ϕ (N - 1) α ^ 2 * W α‖ ^ 2)
      volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    exact hLp.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hc : Continuous (fun α => ‖Cphi451 c ϕ N α - Cphi451 c ϕ (N - 1) α‖ ^ 2) :=
    ((continuous_Cphi451 c ϕ N).sub (continuous_Cphi451 c ϕ (N - 1))).norm.pow 2
  have hpoint (α : ℝ) :
      ‖Cphi451 c ϕ N α ^ 2 * W α - Cphi451 c ϕ (N - 1) α ^ 2 * W α‖ ≤
        (2 * B * U) * ‖Cphi451 c ϕ N α - Cphi451 c ϕ (N - 1) α‖ := by
    by_cases hz : W α = 0
    · simp only [hz, mul_zero, sub_self, norm_zero]
      positivity
    · rw [show Cphi451 c ϕ N α ^ 2 * W α - Cphi451 c ϕ (N - 1) α ^ 2 * W α =
        (Cphi451 c ϕ N α - Cphi451 c ϕ (N - 1) α) *
          (Cphi451 c ϕ N α + Cphi451 c ϕ (N - 1) α) * W α by ring,
        norm_mul, norm_mul]
      have hs : ‖Cphi451 c ϕ N α + Cphi451 c ϕ (N - 1) α‖ ≤ 2 * U := by
        exact (norm_add_le _ _).trans (by
          linarith [hsup N hNX α hz, hsup (N - 1) (by omega) α hz])
      calc
        _ ≤ ‖Cphi451 c ϕ N α - Cphi451 c ϕ (N - 1) α‖ * (2 * U) * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
            (hWB α) (norm_nonneg _) (by positivity)
        _ = _ := by ring
  calc
    _ ≤ ∫ α in (0 : ℝ)..1,
        (2 * B * U) ^ 2 * ‖Cphi451 c ϕ N α - Cphi451 c ϕ (N - 1) α‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num) hi
        ((continuous_const.mul hc).intervalIntegrable 0 1)
      intro α _
      simpa only [Pi.mul_apply, mul_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (hpoint α) 2
    _ = (2 * B * U) ^ 2 *
        ∫ α in (0 : ℝ)..1, ‖Cphi451 c ϕ N α - Cphi451 c ϕ (N - 1) α‖ ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (2 * B * U) ^ 2 * (6 * (L : ℝ) ^ 2 * Real.log N / N) :=
      mul_le_mul_of_nonneg_left (Cphi_increment_energy451 hc0 hcL hϕ hL hN) (sq_nonneg _)
    _ = _ := by ring

/-- The analogue of `supported_family_sharp261` for any coefficients between zero and
Lambda. -/
theorem Cphi_family_sharp451 {c : ℕ → ℝ} (hc0 : ∀ n, 0 ≤ c n)
    (hcL : ∀ n, c n ≤ vonMangoldt n) {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    {L : ℝ≥0} (hL : LipschitzWith L ϕ) {X : ℕ} (hX : 2 ≤ X)
    {W : ℝ → ℂ} (hW : Measurable W) {B U : ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U)
    (hWB : ∀ α, ‖W α‖ ≤ B)
    (hsup : ∀ n ≤ X, ∀ α, W α ≠ 0 → ‖Cphi451 c ϕ n α‖ ≤ U) :
    ∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1, Cphi451 c ϕ N α ^ 2 * W α * ee (-(N * α))‖ ^ 2 ≤
        96 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * X * Real.log X := by
  obtain ⟨M, hM⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
  have hb : ∀ x, |ϕ x| ≤ max M 0 := by
    intro x
    exact (show |ϕ x| ≤ M by simpa only [Real.norm_eq_abs] using hM x).trans (le_max_left M 0)
  let F : ℕ → ℝ → ℂ := fun N α => Cphi451 c ϕ N α ^ 2 * W α
  have hS0 : Cphi451 c ϕ 0 = 0 := by
    funext α
    have hz : ϕ 0 = 0 := by
      by_contra h
      have hs := hϕ.supp (subset_tsupport ϕ h)
      linarith [hs.1]
    simp [Cphi451, hz]
  have hS1 : Cphi451 c ϕ 1 = 0 := by
    funext α
    have hz : ϕ 0 = 0 := by
      by_contra h
      have hs := hϕ.supp (subset_tsupport ϕ h)
      linarith [hs.1]
    have h1 : ϕ 1 = 0 := phi_zero_ge_one261 hϕ le_rfl
    simp [Cphi451, Finset.sum_range_succ, hz, h1]
  have hLp (j : ℕ) : MemLp (F j) 2 (volume.restrict (Set.Ioc 0 1)) :=
    Cphi_multiplier_memLp451 hc0 hcL (le_max_right M 0) hb hW hB hWB j
  have hzero : F 0 = 0 := by funext α; simp [F, hS0]
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
      simp only [F, hS1, hS0, Nat.sub_self, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_mul, sub_self, norm_zero,
        intervalIntegral.integral_zero]
      positivity
    · have hj2 : 2 ≤ j := by omega
      apply (Cphi_supported_increment451 hc0 hcL hϕ (le_max_right M 0) hb hL hj2 hjX hW hB
        hU hWB hsup).trans
      have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
      apply div_le_div_of_nonneg_right _ hjpos.le
      apply mul_le_mul_of_nonneg_left (Real.log_le_log hjpos (by exact_mod_cast hjX))
      positivity
  have h := family_inverse_energy261 X F hzero hint hinc
    (by positivity : 0 ≤ 24 * B ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * Real.log X) hE
  convert h using 1 <;> ring

/-- The statement of `leaf_prime_family_feed1122`, with K equal to 96 times L squared. -/
theorem prime_family_aux451 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
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
  set c : ℕ → ℝ := fun n => if n.Prime then vonMangoldt n else 0 with hcdef
  have hc0 : ∀ n, 0 ≤ c n := by
    intro n; by_cases h : n.Prime <;> simp [c, h, vonMangoldt_nonneg]
  have hcL : ∀ n, c n ≤ vonMangoldt n := by
    intro n; by_cases h : n.Prime <;> simp [c, h, vonMangoldt_nonneg]
  have hrepr : ∀ N ≤ X, ∀ α : ℝ,
      (∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
        ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) * ee (α * k)) = Cphi451 c ϕ N α := by
    intro N hN α
    rw [Cphi_extend451 hϕ hN α, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : k.Prime <;> simp [c, h]
  have hsup' : ∀ n ≤ X, ∀ α, W α ≠ 0 → ‖Cphi451 c ϕ n α‖ ≤ U := by
    intro n hn α hW0
    rw [← hrepr n hn α]
    exact hsup n hn α hW0
  have hmain := Cphi_family_sharp451 hc0 hcL hϕ hL hX hW hB hU hWB hsup'
  have hcongr : (∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1,
          (∑ k ∈ (Finset.range (X + 1)).filter (fun k => k.Prime),
            ((vonMangoldt k * ϕ (k / N) : ℝ) : ℂ) * ee (α * k)) ^ 2 * W α *
            ee (-(N * α))‖ ^ 2) =
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1, Cphi451 c ϕ N α ^ 2 * W α * ee (-(N * α))‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro N hN
    have hNX : N ≤ X := (Finset.mem_Icc.mp hN).2
    congr 2
    apply intervalIntegral.integral_congr
    intro α _
    simp only
    rw [hrepr N hNX α]
  rw [hcongr]
  refine hmain.trans (le_of_eq ?_)
  ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.nonprime_partial_aux451
#print axioms LeanLab.BhowmikGrimmelt2026.Cphi_family_sharp451
#print axioms LeanLab.BhowmikGrimmelt2026.prime_family_aux451
