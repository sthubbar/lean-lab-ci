/-
Split of `prime_minor_multi_451` from SPLIT_minor_bare_multi_denominator451, P0029 page 27,
proof of Lemma 7.3, display 7.8, the minor arc part: "On m(R) ... S_phi satisfies the same
Vinogradov-Vaughan minor-arc estimate as S, giving the minor arc fourth moment bound
(X^3/R + X^(13/5)) (log X)^5".

The paper's route for the prime restricted family is: a pointwise minor arc bound for the
unsmoothed partial sums, transferred to the smoothed sum by summation by parts, then the
family second moment with the supremum pulled out. Here:

* the pointwise bound for the full von Mangoldt partial sums at logarithm power two is the
  existing open leaf `split_leaf_ssum_minor_log2` of SPLIT_minor_bare_family328, reused, not
  restated; it is the QUESTION 2 input of the folder, since display 4.8 only prints power four;
* `leaf_nonprime_partial_feed1122`: removing the higher prime powers from a partial sum costs
  at most a power saving, MEDIUM;
* `leaf_prime_parts_feed1122`: summation by parts for the prime restricted smoothed sum, the
  analogue of the proved `Sphi_of_partial_bound261`, PROVED here;
* `leaf_prime_family_feed1122`: the family second moment with the supremum pulled out, the
  analogue of the proved `supported_family_sharp261` for the prime restricted sum, MEDIUM.

The assembly `prime_minor_multi_451_from_leaves` has exactly the parent statement.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp451a
import LeanLab.BhowmikGrimmelt2026.SPLIT_minor_bare_family328
import LeanLab.BhowmikGrimmelt2026.Decomp384b

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction NNReal

attribute [local instance] Classical.propDecidable

/-- PROVED in this file, no sorry, formerly a LEAF. P0029 page 27, proof of Lemma 7.3, display 7.8,
minor arc part, the step from the von Mangoldt sum S of display 4.8 to its prime part. Class MEDIUM. For every X at least two,
every partial length m at most X and every real alpha, the partial sum of S up to m minus its
prime restricted part, which is the sum of Lambda of n times e of alpha n over the higher
prime powers n at most m, has modulus at most two times X to four fifths times the square of
log X. Proof sketch: the modulus is at most the sum of Lambda over higher prime powers up to
X, which is psi of m minus theta of m, at most two times the square root of m times log m by
Mathlib's `Chebyshev.psi_sub_theta_le`; for X below four no higher prime power occurs. -/
theorem leaf_nonprime_partial_feed1122 {X m : ℕ} (hX : 2 ≤ X) (hm : m ≤ X) (α : ℝ) :
    ‖Ssum m α - ∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime),
        (vonMangoldt n : ℂ) * ee (α * n)‖ ≤
      2 * (X : ℝ) ^ (4 / 5 : ℝ) * Real.log X ^ 2 := by
  have hdiff : Ssum m α - ∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime),
        (vonMangoldt n : ℂ) * ee (α * n) =
      ∑ n ∈ Finset.range (m + 1),
        (((vonMangoldt n - if n.Prime then vonMangoldt n else 0 : ℝ)) : ℂ) * ee (α * n) := by
    unfold Ssum
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
    have hsub : (∑ n ∈ Finset.Icc 1 m,
        (((vonMangoldt n - if n.Prime then vonMangoldt n else 0 : ℝ)) : ℂ) * ee (α * n)) =
        ∑ n ∈ Finset.range (m + 1),
        (((vonMangoldt n - if n.Prime then vonMangoldt n else 0 : ℝ)) : ℂ) * ee (α * n) := by
      apply Finset.sum_subset
      · intro x hx
        simp only [Finset.mem_Icc] at hx
        simp only [Finset.mem_range]
        omega
      · intro x hx hx'
        have hx0 : x = 0 := by
          simp only [Finset.mem_range, Finset.mem_Icc] at hx hx'
          omega
        subst hx0
        simp
    rw [← hsub]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hp : n.Prime <;> simp [hp]
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hXp : (0 : ℝ) < X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hnorm : ‖Ssum m α - ∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime),
        (vonMangoldt n : ℂ) * ee (α * n)‖ ≤ Chebyshev.psi m - Chebyshev.theta m := by
    rw [hdiff, ← nonprime_mass_eq384]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl ?_))
    intro n _
    rw [norm_mul, ee_eq_library84, LeanLab.PNTPort.LargeSieve.norm_e, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    by_cases hp : n.Prime
    · simp [hp]
    · simp [hp, vonMangoldt_nonneg]
  refine hnorm.trans ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · simp [Chebyshev.psi, Chebyshev.theta]
    positivity
  by_cases hX4 : X < 4
  · have hm4 : m < 4 := by omega
    have : Chebyshev.psi m - Chebyshev.theta m = 0 := by
      rw [← nonprime_mass_eq384]
      apply Finset.sum_eq_zero
      intro n hn
      have hn4 : n < 4 := by simp at hn; omega
      interval_cases n <;> simp [vonMangoldt_apply_prime, Nat.prime_two, Nat.prime_three]
    rw [this]; positivity
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmX : (m : ℝ) ≤ X := by exact_mod_cast hm
  have h4 : (4 : ℝ) ≤ X := by exact_mod_cast (by omega : 4 ≤ X)
  have hlog1 : 1 ≤ Real.log X := by
    have := Real.add_one_le_exp 1
    rw [Real.le_log_iff_exp_le hXp]
    have : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    linarith
  have hsq : Real.sqrt m ≤ (X : ℝ) ^ (4 / 5 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc (m : ℝ) ^ (1 / 2 : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hmX (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hlm : Real.log m ≤ Real.log X := Real.log_le_log (by linarith) hmX
  have hlm0 : 0 ≤ Real.log m := Real.log_nonneg hm1'
  calc Chebyshev.psi m - Chebyshev.theta m ≤ 2 * Real.sqrt m * Real.log m :=
        Chebyshev.psi_sub_theta_le hm1'
    _ ≤ 2 * (X : ℝ) ^ (4 / 5 : ℝ) * (Real.log X * Real.log X) := by
        gcongr
        nlinarith
    _ = _ := by ring

/-- PROVED in this file, no sorry. P0029 page 27, proof of Lemma 7.3, display 7.8, minor arc
part, the transfer of the minor arc estimate from S to the smoothed sum S_phi by summation by
parts, for the prime restricted smoothed sum. For admissible phi with Lipschitz constant L, every
cutoff N at most X, and a nonnegative B bounding every prime restricted partial sum up to
m at most N, the prime restricted smoothed sum of length X at cutoff N has modulus at most
L times B. This is the prime analogue of the proved `Sphi_of_partial_bound261`; phi of n
over N vanishes for n at least N, so the length X plays no role. -/
theorem leaf_prime_parts_feed1122 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    {L : ℝ≥0} (hL : LipschitzWith L ϕ) {X N : ℕ} (hNX : N ≤ X) {α B : ℝ}
    (hB : 0 ≤ B)
    (hpartial : ∀ m ≤ N, ‖∑ n ∈ (Finset.Icc 1 m).filter (fun n => n.Prime),
        (vonMangoldt n : ℂ) * ee (α * n)‖ ≤ B) :
    ‖∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
        ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)‖ ≤ (L : ℝ) * B := by
  classical
  set a : ℕ → ℂ := fun n => if n.Prime then (vonMangoldt n : ℂ) * ee (α * n) else 0 with ha
  have hpart' : ∀ m ≤ N, ‖∑ k ∈ Finset.range (m + 1), a k‖ ≤ B := by
    intro m hm
    have hc : (∑ k ∈ (Finset.Icc 1 m).filter (fun n => n.Prime),
        (vonMangoldt k : ℂ) * ee (α * k)) = ∑ k ∈ Finset.range (m + 1), a k := by
      rw [Finset.sum_filter]
      apply Finset.sum_subset
      · intro x hx
        simp only [Finset.mem_Icc] at hx
        simp only [Finset.mem_range]
        omega
      · intro x _ hx
        have hx0 : x = 0 := by
          by_contra h0
          apply hx
          simp only [Finset.mem_Icc]
          constructor
          · omega
          · simp only [Finset.mem_range] at *
            omega
        subst hx0
        simp [ha, Nat.not_prime_zero]
    rw [← hc]
    exact hpartial m hm
  have hmain : (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
        ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) =
      ∑ n ∈ Finset.range (X + 1), ϕ ((n : ℝ) / N) • a n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hp : n.Prime
    · simp only [hp, ite_true, ha, Complex.real_smul]
      push_cast
      ring
    · simp [hp, ha]
  rw [hmain]
  by_cases hN : N = 0
  · subst N
    have h0 : ϕ 0 = 0 := by
      by_contra h
      have hs := hϕ.supp (subset_tsupport ϕ h)
      linarith [hs.1]
    simp [h0]
    positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have hcut : (∑ n ∈ Finset.range (X + 1), ϕ ((n : ℝ) / N) • a n) =
      ∑ n ∈ Finset.range (N + 1), ϕ ((n : ℝ) / N) • a n := by
    symm
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_range] at *
      omega
    · intro x _ hx
      simp only [Finset.mem_range, not_lt] at hx
      have h1 : (1 : ℝ) ≤ (x : ℝ) / N := by
        rw [le_div_iff₀ hNpos]
        have : (N : ℝ) + 1 ≤ x := by exact_mod_cast hx
        linarith
      rw [phi_zero_ge_one261 hϕ h1, zero_smul]
  rw [hcut]
  have hphi1 : ϕ ((N : ℝ) / N) = 0 := by
    rw [div_self hNpos.ne']
    exact phi_zero_ge_one261 hϕ le_rfl
  have hparts := Finset.sum_range_by_parts (fun n : ℕ => ϕ ((n : ℝ) / N)) a (N + 1)
  have hrepr : (∑ n ∈ Finset.range (N + 1), ϕ ((n : ℝ) / N) • a n) =
      -(∑ n ∈ Finset.range N, (ϕ (((n + 1 : ℕ) : ℝ) / N) - ϕ ((n : ℝ) / N)) •
        ∑ k ∈ Finset.range (n + 1), a k) := by
    simpa only [Nat.add_sub_cancel, hphi1, zero_smul, zero_sub] using hparts
  have hstep (n : ℕ) :
      |ϕ (((n + 1 : ℕ) : ℝ) / N) - ϕ ((n : ℝ) / N)| ≤ (L : ℝ) / N := by
    have h := hL.norm_sub_le (((n + 1 : ℕ) : ℝ) / N) ((n : ℝ) / N)
    simp only [Real.norm_eq_abs] at h
    have heq : ((n + 1 : ℕ) : ℝ) / N - (n : ℝ) / N = 1 / N := by push_cast; ring
    rw [heq, abs_of_pos (one_div_pos.mpr hNpos)] at h
    simpa only [div_eq_mul_inv, one_mul] using h
  rw [hrepr, norm_neg]
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        ‖(ϕ (((n + 1 : ℕ) : ℝ) / N) - ϕ ((n : ℝ) / N)) •
          ∑ k ∈ Finset.range (n + 1), a k‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, ((L : ℝ) / N) * B := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hstep n) (hpart' n (by simp only [Finset.mem_range] at hn; omega))
        (norm_nonneg _) (by positivity)
    _ = (L : ℝ) * B := by simp; field_simp

/-- LEAF: P0029 page 27, proof of Lemma 7.3, display 7.8, the family second moment over the
cutoff N with the minor arc supremum pulled out, for the prime restricted smoothed sum.
Class MEDIUM. For admissible phi there is a nonnegative K such that for every X at least two,
every measurable multiplier W bounded by B, and every U bounding the prime restricted smoothed
sum of length X at every cutoff n at most X wherever W is nonzero, the sum over N from one to
X of the squared modulus of the integral over the unit interval of the square of the prime
restricted smoothed sum at cutoff N times W times e of minus N alpha is at most K times B
squared times U squared times X times log X. This is the prime analogue of the proved
`supported_family_sharp261`, whose constant is 96 times L squared. -/
theorem leaf_prime_family_feed1122 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
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
  sorry

/-- Assembly: `prime_minor_multi_451` with exactly its statement, from the reused leaf
`split_leaf_ssum_minor_log2` and the three leaves above. -/
theorem prime_minor_multi_451_from_leaves {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
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
    have hD := leaf_nonprime_partial_feed1122 hX hmX α
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

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_nonprime_partial_feed1122
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_prime_parts_feed1122
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_prime_family_feed1122
#print axioms LeanLab.BhowmikGrimmelt2026.prime_minor_multi_451_from_leaves
