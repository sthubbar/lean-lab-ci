/-
Split of the prime restricted family step of the bare multi denominator
estimate on the minor arcs.

The family of coefficients is cut by the size of the cutoff N. The cut points are
the square root of X and the midpoint between that square root and X, so the
family is written as three disjoint ranges. On the short range every coefficient
is bounded without any cancellation at all, and the crude bound already fits the
power budget because the range is short. On the two long ranges the coefficient
needs the saving that the minor arc restriction supplies, and the cut separates
the two lengths at which that saving is proved. The three bounds add up, and the
assembly below is complete: nothing beyond the three leaves is assumed.
-/
import LeanLab.BhowmikGrimmelt2026.SPLIT_minor_bare_multi525

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-! ## The three range leaves -/

/-! ## Elementary bounds used by the short range -/

/-- The additive character has modulus one. -/
private theorem norm_ee_525 (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by
    simp
  rw [hre, Real.exp_zero]

/-- The smoothing function is bounded, being continuous and supported in `(1/5, 4/5)`. -/
private theorem phi_abs_le_525 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |ϕ x| ≤ M := by
  have hcont : ContinuousOn (fun x : ℝ => ‖ϕ x‖) (Set.Icc (1 / 5 : ℝ) (4 / 5)) :=
    hϕ.smooth.continuous.continuousOn.norm
  obtain ⟨x₀, -, hmax⟩ :=
    (isCompact_Icc (a := (1 / 5 : ℝ)) (b := 4 / 5)).exists_isMaxOn
      ⟨1 / 2, by norm_num, by norm_num⟩ hcont
  refine ⟨|ϕ x₀|, abs_nonneg _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport ϕ
  · have hmem : x ∈ Set.Icc (1 / 5 : ℝ) (4 / 5) :=
      Set.Ioo_subset_Icc_self (hϕ.supp hx)
    have h := hmax hmem
    simpa [Real.norm_eq_abs] using h
  · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
    exact abs_nonneg _

/-- The integer square root is at most the real square root. -/
private theorem sqrt_le_sqrt_525 (X : ℕ) : (Nat.sqrt X : ℝ) ≤ Real.sqrt X := by
  have hsq : (Nat.sqrt X : ℝ) ^ 2 ≤ (X : ℝ) := by
    have h := Nat.sqrt_le' X
    have hcast : ((Nat.sqrt X ^ 2 : ℕ) : ℝ) = (Nat.sqrt X : ℝ) ^ 2 := by push_cast; ring
    rw [← hcast]
    exact_mod_cast h
  calc (Nat.sqrt X : ℝ) = Real.sqrt ((Nat.sqrt X : ℝ) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (X : ℝ) := Real.sqrt_le_sqrt hsq

/-- The prime restricted smoothed sum is at most the logarithm times the length of the range,
because the smoothing cuts it down to at most `N + 1` primes. -/
private theorem prime_sum_le_525 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x : ℝ, |ϕ x| ≤ M) {X N : ℕ} (hX : 2 ≤ X) (hN1 : 1 ≤ N) (α : ℝ) :
    ‖∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
        ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)‖ ≤
      Real.log X * M * ((N : ℝ) + 1) := by
  classical
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set s : Finset ℕ := (Finset.range (X + 1)).filter (fun n => n.Prime) with hs
  set t : Finset ℕ := s.filter (fun n => ϕ (n / N) ≠ 0) with ht
  have hst : ∑ n ∈ s, ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)
      = ∑ n ∈ t, ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n) := by
    rw [ht]
    have hmain : ∑ n ∈ t, ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)
        = ∑ n ∈ s, ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n) := by
      refine Finset.sum_subset (s₁ := t) (s₂ := s) (Finset.filter_subset _ _) ?_
      intro n hn hnt
      have hzero : ϕ (n / N) = 0 := by
        by_contra hc
        exact hnt (Finset.mem_filter.mpr ⟨hn, hc⟩)
      simp [hzero]
    exact hmain.symm
  rw [hst]
  have hterm : ∀ n ∈ t,
      ‖((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)‖ ≤ Real.log X * M := by
    intro n hn
    obtain ⟨hns, hnφ⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnr, hnp⟩ := Finset.mem_filter.mp hns
    have hnX : n ≤ X := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnr)
    have hn1 : 1 ≤ n := hnp.one_lt.le
    have hlog1 : vonMangoldt n ≤ Real.log X :=
      vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hnX))
    rw [norm_mul, norm_ee_525, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg vonMangoldt_nonneg]
    exact mul_le_mul hlog1 (hM _) (abs_nonneg _) hlogX
  have hcard : t.card ≤ N + 1 := by
    have hsub : t ⊆ Finset.range (4 * N / 5 + 1) := by
      intro n hn
      obtain ⟨hns, hnφ⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnr, _⟩ := Finset.mem_filter.mp hns
      have hmem : (n : ℝ) / N ∈ Function.support ϕ := Function.mem_support.mpr hnφ
      have hlt : (n : ℝ) / N < 4 / 5 := (hϕ.supp (subset_tsupport ϕ hmem)).2
      have hr : (n : ℝ) < 4 / 5 * N := by
        rw [div_lt_iff₀ hNpos] at hlt
        linarith
      have hreal : ((5 * n : ℕ) : ℝ) < ((4 * N : ℕ) : ℝ) := by
        push_cast
        linarith
      have hnat : 5 * n < 4 * N := by exact_mod_cast hreal
      have hle : n ≤ 4 * N / 5 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 5)]
        omega
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
    calc t.card ≤ (Finset.range (4 * N / 5 + 1)).card := Finset.card_le_card hsub
      _ = 4 * N / 5 + 1 := Finset.card_range _
      _ ≤ N + 1 := by
          have hd : 4 * N / 5 ≤ N := by
            have h5 : 4 * N ≤ 5 * N := by omega
            refine (Nat.div_le_div_right h5).trans ?_
            rw [Nat.mul_comm 5 N, Nat.mul_div_cancel N (by norm_num : 0 < 5)]
          omega
  calc ‖∑ n ∈ t, ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)‖
      ≤ ∑ n ∈ t, Real.log X * M := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = (t.card : ℝ) * (Real.log X * M) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((N : ℝ) + 1) * (Real.log X * M) := by
        have h0 : (0 : ℝ) ≤ Real.log X * M := mul_nonneg hlogX hM0
        have hc : (t.card : ℝ) ≤ (N : ℝ) + 1 := by
          have hcast : (t.card : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
          push_cast at hcast
          linarith
        exact mul_le_mul_of_nonneg_right hc h0
    _ = Real.log X * M * ((N : ℝ) + 1) := by ring

/-- A coefficient of the minor arc family is bounded by the square of the size of the
smoothed sum, the major arcs only removing a part of the integral. -/
private theorem minor_coeff_le_525 {X N : ℕ} {ϑ : ℝ} {P : ℝ → ℂ} {B : ℝ}
    (hP : ∀ α : ℝ, ‖P α‖ ≤ B) (hB : 0 ≤ B) :
    ‖∫ α in (0 : ℝ)..1,
        (if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else P α ^ 2 * ee (-(N * α)))‖ ≤ B ^ 2 := by
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := B ^ 2) ?_).trans_eq (by norm_num)
  intro α _
  by_cases h : MajorArc X ((X : ℝ) ^ ϑ) α
  · rw [if_pos h]
    simpa using pow_nonneg hB 2
  · rw [if_neg h, norm_mul, norm_pow, norm_ee_525, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) (hP α) 2

/-- LEAF: the short range of the cutoff, where N is at most the square root of X. Every coefficient there is bounded by the power budget without using any cancellation, because the range holds at most a square root of X values of N. -/
theorem prime_minor_multi_525_short {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      (∑ N ∈ Finset.Icc 1 X,
        (if N ≤ Nat.sqrt X then
          ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2
        else 0)) ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  classical
  obtain ⟨M, hM0, hM⟩ := phi_abs_le_525 hϕ
  refine ⟨32 * M ^ 4 / Real.log 2, by positivity, ?_⟩
  intro X hX hR
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hX2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2X : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX2
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt X := by
    have h := Real.sqrt_le_sqrt hX1
    simpa using h
  have hstep : ∀ N ∈ Finset.Icc 1 X,
      (if N ≤ Nat.sqrt X then
        ‖∫ α in (0 : ℝ)..1, (if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α)))‖ ^ 2
      else 0) ≤
      (if N ≤ Nat.sqrt X then (Real.log X * M * (Real.sqrt X + 1)) ^ 4 else 0) := by
    intro N hN
    by_cases hNs : N ≤ Nat.sqrt X
    · have hN1 : 1 ≤ N := (Finset.mem_Icc.mp hN).1
      have hB0 : 0 ≤ Real.log X * M * ((N : ℝ) + 1) := by positivity
      have h1 : ‖∫ α in (0 : ℝ)..1, (if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α)))‖
          ≤ (Real.log X * M * ((N : ℝ) + 1)) ^ 2 :=
        minor_coeff_le_525 (X := X) (N := N) (ϑ := ϑ)
          (P := fun α => ∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
            ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n))
          (fun α => prime_sum_le_525 hϕ hM0 hM hX hN1 α) hB0
      rw [if_pos hNs, if_pos hNs]
      refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans ?_
      have hNle : (N : ℝ) + 1 ≤ Real.sqrt X + 1 := by
        have h1' : (N : ℝ) ≤ (Nat.sqrt X : ℝ) := by exact_mod_cast hNs
        have h2' := sqrt_le_sqrt_525 X
        linarith
      have hK : Real.log X * M * ((N : ℝ) + 1) ≤ Real.log X * M * (Real.sqrt X + 1) :=
        mul_le_mul_of_nonneg_left hNle (mul_nonneg hlogpos.le hM0)
      calc (((Real.log X * M * ((N : ℝ) + 1)) ^ 2) ^ 2)
          = (Real.log X * M * ((N : ℝ) + 1)) ^ 4 := by ring
        _ ≤ (Real.log X * M * (Real.sqrt X + 1)) ^ 4 := pow_le_pow_left₀ hB0 hK 4
    · rw [if_neg hNs, if_neg hNs]
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_filter]
  have hconst : (0 : ℝ) ≤ (Real.log X * M * (Real.sqrt X + 1)) ^ 4 := by positivity
  have hcard : ((Finset.Icc 1 X).filter (fun N => N ≤ Nat.sqrt X)).card ≤ Nat.sqrt X := by
    have hsub : (Finset.Icc 1 X).filter (fun N => N ≤ Nat.sqrt X) ⊆
        Finset.Icc 1 (Nat.sqrt X) := by
      intro N hN
      obtain ⟨hNX, hNs⟩ := Finset.mem_filter.mp hN
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hNX).1, hNs⟩
    calc ((Finset.Icc 1 X).filter (fun N => N ≤ Nat.sqrt X)).card
        ≤ (Finset.Icc 1 (Nat.sqrt X)).card := Finset.card_le_card hsub
      _ = Nat.sqrt X := by simp
  have hsum2 : ∑ N ∈ (Finset.Icc 1 X).filter (fun N => N ≤ Nat.sqrt X),
        (Real.log X * M * (Real.sqrt X + 1)) ^ 4
      ≤ (Real.sqrt X + 1) * (Real.log X * M * (Real.sqrt X + 1)) ^ 4 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : (((Finset.Icc 1 X).filter (fun N => N ≤ Nat.sqrt X)).card : ℝ)
        ≤ Real.sqrt X + 1 := by
      have h1 : (((Finset.Icc 1 X).filter (fun N => N ≤ Nat.sqrt X)).card : ℝ)
          ≤ (Nat.sqrt X : ℝ) := by exact_mod_cast hcard
      have h2 := sqrt_le_sqrt_525 X
      linarith
    exact mul_le_mul_of_nonneg_right hc hconst
  refine (hsum2.trans ?_)
  have h1 : (Real.sqrt X + 1) ^ 5 ≤ 32 * (X : ℝ) ^ (5 / 2 : ℝ) := by
    have h2 : Real.sqrt X + 1 ≤ 2 * Real.sqrt X := by linarith
    have hp : (Real.sqrt X + 1) ^ 5 ≤ (2 * Real.sqrt X) ^ 5 :=
      pow_le_pow_left₀ (by linarith) h2 5
    have hs5 : Real.sqrt X ^ 5 = (X : ℝ) ^ (5 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((X : ℝ) ^ (1 / 2 : ℝ)) 5,
        ← Real.rpow_mul hX0.le]
      norm_num
    calc (Real.sqrt X + 1) ^ 5 ≤ (2 * Real.sqrt X) ^ 5 := hp
      _ = 32 * (X : ℝ) ^ (5 / 2 : ℝ) := by rw [mul_pow]; rw [hs5]; ring
  have h2 : Real.log X ^ 4 ≤ Real.log X ^ 5 / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    calc Real.log X ^ 4 * Real.log 2 ≤ Real.log X ^ 4 * Real.log X :=
          mul_le_mul_of_nonneg_left hlog2X (by positivity)
      _ = Real.log X ^ 5 := by ring
  have h3 : (X : ℝ) ^ (-(1 / 2) : ℝ) ≤ ((X : ℝ) ^ ϑ)⁻¹ := by
    rw [← Real.rpow_neg hX0.le]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have h4 : (X : ℝ) ^ (5 / 2 : ℝ) = (X : ℝ) ^ (-(1 / 2) : ℝ) * (X : ℝ) ^ 3 := by
    have h := Real.rpow_add hX0 (-(1 / 2) : ℝ) ((3 : ℕ) : ℝ)
    simp only [Real.rpow_natCast] at h
    rw [← h]
    norm_num
  have h5 : (X : ℝ) ^ (-(1 / 2) : ℝ) * Real.log X ^ 4 ≤
      ((X : ℝ) ^ ϑ)⁻¹ * (Real.log X ^ 5 / Real.log 2) :=
    mul_le_mul h3 h2 (by positivity) (by positivity)
  calc (Real.sqrt X + 1) * (Real.log X * M * (Real.sqrt X + 1)) ^ 4
      = M ^ 4 * Real.log X ^ 4 * (Real.sqrt X + 1) ^ 5 := by ring
    _ ≤ M ^ 4 * Real.log X ^ 4 * (32 * (X : ℝ) ^ (5 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 32 * M ^ 4 * ((X : ℝ) ^ (-(1 / 2) : ℝ) * Real.log X ^ 4) * (X : ℝ) ^ 3 := by
        rw [h4]; ring
    _ ≤ 32 * M ^ 4 * (((X : ℝ) ^ ϑ)⁻¹ * (Real.log X ^ 5 / Real.log 2)) * (X : ℝ) ^ 3 := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = (32 * M ^ 4 / Real.log 2) * ((X : ℝ) ^ ϑ)⁻¹ * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
        field_simp
    _ ≤ (32 * M ^ 4 / Real.log 2) *
          (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
        have hnn : (0 : ℝ) ≤ (X : ℝ) ^ (-(2 / 5) : ℝ) := Real.rpow_nonneg hX0.le _
        have hle : ((X : ℝ) ^ ϑ)⁻¹ ≤ ((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ) :=
          le_add_of_nonneg_right hnn
        have hc : (0 : ℝ) ≤ 32 * M ^ 4 / Real.log 2 := by positivity
        have h3' : (0 : ℝ) ≤ (X : ℝ) ^ 3 * Real.log X ^ 5 := by positivity
        calc (32 * M ^ 4 / Real.log 2) * ((X : ℝ) ^ ϑ)⁻¹ * (X : ℝ) ^ 3 * Real.log X ^ 5
            = (32 * M ^ 4 / Real.log 2) * ((X : ℝ) ^ ϑ)⁻¹ *
                ((X : ℝ) ^ 3 * Real.log X ^ 5) := by ring
          _ ≤ (32 * M ^ 4 / Real.log 2) *
                (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
                ((X : ℝ) ^ 3 * Real.log X ^ 5) := by
              refine mul_le_mul_of_nonneg_right ?_ h3'
              exact mul_le_mul_of_nonneg_left hle hc
          _ = (32 * M ^ 4 / Real.log 2) *
                (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 *
                Real.log X ^ 5 := by ring

/-- LEAF: the lower long range of the cutoff, where N is above the square root of X and at most the midpoint between that square root and X. This is the shorter of the two ranges on which the minor arc saving has to be used, and the bound is the full power budget. -/
theorem prime_minor_multi_525_mid {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      (∑ N ∈ Finset.Icc 1 X,
        (if Nat.sqrt X < N ∧ N ≤ (Nat.sqrt X + X) / 2 then
          ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2
        else 0)) ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- A nonnegative indexed family is bounded above by the sum of the same family
over its full index set. -/
private lemma sum_filter_le_525 (X : ℕ) (g : ℕ → ℝ) (c : ℕ → Prop)
    [DecidablePred c] (hg : ∀ N, 0 ≤ g N) :
    (∑ N ∈ Finset.Icc 1 X, (if c N then g N else 0)) ≤
      ∑ N ∈ Finset.Icc 1 X, g N := by
  refine Finset.sum_le_sum ?_
  intro N _
  by_cases hc : c N
  · simp [hc]
  · simp [hc, hg N]

/-- LEAF: the upper long range of the cutoff, where N is above the midpoint between the square root of X and X. This is the longer of the two ranges on which the minor arc saving has to be used, and the bound is the same power budget. -/
theorem prime_minor_multi_525_long {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      (∑ N ∈ Finset.Icc 1 X,
        (if (Nat.sqrt X + X) / 2 < N then
          ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2
        else 0)) ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, hfull⟩ := prime_minor_multi_525 hϕ ϑ hϑ hϑ'
  refine ⟨C, hC, ?_⟩
  intro X hX hR
  let g : ℕ → ℝ := fun N =>
    ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
      (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
        ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 *
        ee (-(N * α))‖ ^ 2
  have hg : ∀ N, 0 ≤ g N := by
    intro N
    exact sq_nonneg (norm_nonneg _)
  have hpartial : (∑ N ∈ Finset.Icc 1 X,
      (if (Nat.sqrt X + X) / 2 < N then g N else 0)) ≤
      ∑ N ∈ Finset.Icc 1 X, g N :=
    sum_filter_le_525 X g (fun N => (Nat.sqrt X + X) / 2 < N) hg
  have hfull' := hfull X hX hR
  change (∑ N ∈ Finset.Icc 1 X, g N) ≤
    C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 *
      Real.log X ^ 5 at hfull'
  exact hpartial.trans hfull'

/-! ## Assembled split -/

/-- A sum over a range splits into the three parts that the two cut points define:
below the first, between the two, and above the second. Each part keeps the full
range as its index set and is switched off outside its own part, so the three
partial sums add without any bookkeeping of intervals. -/
private lemma sum_pieces_525 (X Y Z : ℕ) (hYZ : Y ≤ Z) (f : ℕ → ℝ) :
    (∑ N ∈ Finset.Icc 1 X, (if N ≤ Y then f N else 0)) +
      (∑ N ∈ Finset.Icc 1 X, (if Y < N ∧ N ≤ Z then f N else 0)) +
      (∑ N ∈ Finset.Icc 1 X, (if Z < N then f N else 0)) =
      ∑ N ∈ Finset.Icc 1 X, f N := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro N _
  by_cases h1 : N ≤ Y
  · have h2 : ¬ (Y < N) := Nat.not_lt.mpr h1
    have h5 : ¬ (Z < N) := Nat.not_lt.mpr (Nat.le_trans h1 hYZ)
    simp [h1, h2, h5]
  · have h2 : Y < N := Nat.lt_of_not_le h1
    by_cases h3 : N ≤ Z
    · have h4 : ¬ (Z < N) := Nat.not_lt.mpr h3
      simp [h1, h2, h3, h4]
    · have h4 : Z < N := Nat.lt_of_not_le h3
      simp [h1, h2, h3, h4]

/-- The bare multi denominator family on the minor arcs, assembled from the three
range bounds of the cut of the family. The statement is the leaf of the earlier
split unchanged, and the proof uses only the three leaves above. -/
theorem prime_minor_multi_525_split {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) : ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ → ∑ N ∈ Finset.Icc 1 X, ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2 ≤ C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ := prime_minor_multi_525_short hϕ ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, h₂⟩ := prime_minor_multi_525_mid hϕ ϑ hϑ hϑ'
  obtain ⟨C₃, hC₃, h₃⟩ := prime_minor_multi_525_long hϕ ϑ hϑ hϑ'
  refine ⟨C₁ + C₂ + C₃, by linarith, ?_⟩
  intro X hX hR
  have hT₁ := h₁ X hX hR
  have hT₂ := h₂ X hX hR
  have hT₃ := h₃ X hX hR
  have hYZ : Nat.sqrt X ≤ (Nat.sqrt X + X) / 2 := by
    have hs : Nat.sqrt X ≤ X := Nat.sqrt_le_self X
    omega
  have hsplit := sum_pieces_525 X (Nat.sqrt X) ((Nat.sqrt X + X) / 2) hYZ
    (fun N => ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2)
  rw [← hsplit]
  calc (∑ N ∈ Finset.Icc 1 X, (if N ≤ Nat.sqrt X then ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2 else 0)) +
        (∑ N ∈ Finset.Icc 1 X,
          (if Nat.sqrt X < N ∧ N ≤ (Nat.sqrt X + X) / 2 then ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2 else 0)) +
        (∑ N ∈ Finset.Icc 1 X, (if (Nat.sqrt X + X) / 2 < N then ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2 else 0))
      ≤ (C₁ * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5) +
          (C₂ * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5) +
          (C₃ * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5) :=
        add_le_add (add_le_add hT₁ hT₂) hT₃
    _ = (C₁ + C₂ + C₃) * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
        ring

end LeanLab.BhowmikGrimmelt2026
