/-
P0069, Section 5, page 51, display 5.17.
A quantitative rectangle rule for bounded variation functions.
This is the one dimensional quadrature inside the E4 integer sum.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentCells517
import Mathlib.Topology.EMetricSpace.BoundedVariation

namespace LeanLab.BHP1997.LowerShortC165
open MeasureTheory
open scoped BigOperators

/-- Page 51 display 5.17. The rectangle rule error for a bounded variation
function is at most the largest cell width times its total variation. -/
theorem four_exponent_bv_rectangle (f : ℝ → ℝ) (e : ℕ → ℝ) (he : Monotone e)
    (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmesh : ∀ i < N, e (i+1)-e i ≤ δ)
    (hi : IntervalIntegrable f volume (e 0) (e N))
    (hbv : BoundedVariationOn f (Set.Icc (e 0) (e N))) :
    |(∑ i ∈ Finset.range N, (e (i+1)-e i) * f (e i)) -
        ∫ t in (e 0)..(e N), f t| ≤
      δ * (eVariationOn f (Set.Icc (e 0) (e N))).toReal := by
  have hsub : ∀ i < N, Set.Icc (e i) (e (i+1)) ⊆ Set.Icc (e 0) (e N) := by
    intro i hi t ht
    exact ⟨(he (Nat.zero_le i)).trans ht.1,
      ht.2.trans (he (Nat.succ_le_of_lt hi))⟩
  have hic : ∀ i < N, IntervalIntegrable f volume (e i) (e (i+1)) := by
    intro i hiN
    apply hi.mono_set
    simpa only [Set.uIcc_of_le (he (Nat.le_succ i)),
      Set.uIcc_of_le (he (Nat.zero_le N))] using hsub i hiN
  have hbc : ∀ i < N, BoundedVariationOn f (Set.Icc (e i) (e (i+1))) :=
    fun i hiN => hbv.mono (hsub i hiN)
  have hcell : ∀ i < N,
      |(e (i+1)-e i) * f (e i) - ∫ t in (e i)..(e (i+1)), f t| ≤
        δ * (eVariationOn f (Set.Icc (e i) (e (i+1)))).toReal := by
    intro i hiN
    have heq : (∫ t in (e i)..(e (i+1)), f (e i)-f t) =
        (e (i+1)-e i) * f (e i) - ∫ t in (e i)..(e (i+1)), f t := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hic i hiN),
        intervalIntegral.integral_const, smul_eq_mul]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := e i) (b := e (i+1)) (f := fun t => f (e i)-f t)
      (C := (eVariationOn f (Set.Icc (e i) (e (i+1)))).toReal) (fun t ht => by
        rw [Set.uIoc_of_le (he (Nat.le_succ i))] at ht
        rw [Real.norm_eq_abs]
        simpa only [Real.dist_eq] using
          (hbc i hiN).dist_le ⟨le_rfl, he (Nat.le_succ i)⟩ ⟨ht.1.le, ht.2⟩)
    rw [heq, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (he (Nat.le_succ i)))] at hbound
    exact hbound.trans (by
      have h := mul_le_mul_of_nonneg_left (hmesh i hiN)
        (ENNReal.toReal_nonneg : 0 ≤ (eVariationOn f (Set.Icc (e i) (e (i+1)))).toReal)
      simpa only [mul_comm] using h)
  have hvar : (∑ i ∈ Finset.range N, (eVariationOn f (Set.Icc (e i) (e (i+1)))).toReal) =
      (eVariationOn f (Set.Icc (e 0) (e N))).toReal := by
    rw [← ENNReal.toReal_sum (fun i hiN => hbc i (Finset.mem_range.mp hiN))]
    exact congrArg ENNReal.toReal (eVariationOn.sum' f he)
  rw [← intervalIntegral.sum_integral_adjacent_intervals hic, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ i ∈ Finset.range N,
        |(e (i+1)-e i) * f (e i) - ∫ t in (e i)..(e (i+1)), f t| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, δ * (eVariationOn f (Set.Icc (e i) (e (i+1)))).toReal :=
      Finset.sum_le_sum (fun i hiN => hcell i (Finset.mem_range.mp hiN))
    _ = _ := by rw [← Finset.mul_sum, hvar]

/-- Page 51 display 5.17. Perturbing the exact cell widths adds only the
sample bound times the sum of the absolute weight discrepancies. -/
theorem four_exponent_bv_weighted_rectangle (f : ℝ → ℝ) (e : ℕ → ℝ)
    (he : Monotone e) (N : ℕ) (w : ℕ → ℝ) {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hmesh : ∀ i < N, e (i+1)-e i ≤ δ)
    (hf : ∀ i < N, |f (e i)| ≤ M)
    (hi : IntervalIntegrable f volume (e 0) (e N))
    (hbv : BoundedVariationOn f (Set.Icc (e 0) (e N))) :
    |(∑ i ∈ Finset.range N, w i * f (e i)) - ∫ t in (e 0)..(e N), f t| ≤
      M * (∑ i ∈ Finset.range N, |w i - (e (i+1)-e i)|) +
        δ * (eVariationOn f (Set.Icc (e 0) (e N))).toReal := by
  have hbase := four_exponent_bv_rectangle f e he N hδ hmesh hi hbv
  have hdiff : |(∑ i ∈ Finset.range N, w i * f (e i)) -
      ∑ i ∈ Finset.range N, (e (i+1)-e i) * f (e i)| ≤
      M * (∑ i ∈ Finset.range N, |w i - (e (i+1)-e i)|) := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ i ∈ Finset.range N, |w i * f (e i) - (e (i+1)-e i) * f (e i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range N, M * |w i - (e (i+1)-e i)| := by
        apply Finset.sum_le_sum
        intro i hiN
        rw [← sub_mul, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hf i (Finset.mem_range.mp hiN)) (abs_nonneg _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  exact (abs_sub_le _ (∑ i ∈ Finset.range N, (e (i+1)-e i) * f (e i)) _).trans
    (add_le_add hdiff hbase)

/-- Page 51 display 5.17. A shifted reciprocal square tail saves the
lower integer cutoff. This is Mathlib's finite tail bound reindexed. -/
theorem four_exponent_shifted_inv_sq_sum (L N : ℕ) (hL : 1 ≤ L) :
    (∑ i ∈ Finset.range N, (1 : ℝ) / ((L+i+1 : ℕ) : ℝ)^2) ≤ 1 / (L : ℝ) := by
  have hs : (∑ n ∈ Finset.Ioc L (L+N), ((n : ℝ)^2)⁻¹) ≤ (L : ℝ)⁻¹ :=
    (sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : L ≠ 0) (Nat.le_add_right L N)).trans
      (sub_le_self _ (by positivity))
  have heq : Finset.Ioc L (L+N) = Finset.Ico (L+1) (L+N+1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hlen : L+N+1-(L+1) = N := by omega
  rw [heq, Finset.sum_Ico_eq_sum_range, hlen] at hs
  simpa only [one_div, Nat.add_right_comm] using hs

/-- Page 51 display 5.17. The sum of the differences between the integer
mesh weights and their exact logarithmic cell widths saves the lower cutoff. -/
theorem four_exponent_log_weight_error {Z : ℝ} (hZ : 1 < Z)
    (L N : ℕ) (hL : 1 ≤ L) :
    (∑ i ∈ Finset.range N,
      |1 / (((L+i+1 : ℕ) : ℝ) * Real.log Z) -
        (Real.log (((L+i+1 : ℕ) : ℝ)+1) / Real.log Z -
          Real.log ((L+i+1 : ℕ) : ℝ) / Real.log Z)|) ≤
      1 / ((L : ℝ) * Real.log Z) := by
  have hlog : 0 < Real.log Z := Real.log_pos hZ
  calc _ ≤ ∑ i ∈ Finset.range N, 1 / (((L+i+1 : ℕ) : ℝ)^2 * Real.log Z) := by
        apply Finset.sum_le_sum
        intro i _
        obtain ⟨h0, h1⟩ := four_exponent_mesh_error hZ
          (show (0 : ℝ) < ((L+i+1 : ℕ) : ℝ) by positivity)
        rwa [abs_of_nonneg h0]
    _ = (∑ i ∈ Finset.range N, (1 : ℝ) / ((L+i+1 : ℕ) : ℝ)^2) / Real.log Z := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        rw [div_div]
    _ ≤ (1 / (L : ℝ)) / Real.log Z :=
      div_le_div_of_nonneg_right (four_exponent_shifted_inv_sq_sum L N hL) hlog.le
    _ = _ := by rw [div_div]

/-- Page 51 display 5.17. The integer logarithmic quadrature for any
bounded variation integrand saves its lower integer cutoff. -/
theorem four_exponent_log_bv_quadrature (f : ℝ → ℝ) {Z M : ℝ} (hZ : 1 < Z)
    (hM : 0 ≤ M) (L N : ℕ) (hL : 1 ≤ L)
    (hf : ∀ i < N, |f (Real.log ((L : ℝ)+(i : ℝ)+1) / Real.log Z)| ≤ M)
    (hi : IntervalIntegrable f volume (Real.log ((L : ℝ)+1) / Real.log Z)
      (Real.log ((L : ℝ)+(N : ℝ)+1) / Real.log Z))
    (hbv : BoundedVariationOn f (Set.Icc (Real.log ((L : ℝ)+1) / Real.log Z)
      (Real.log ((L : ℝ)+(N : ℝ)+1) / Real.log Z))) :
    |(∑ i ∈ Finset.range N,
        f (Real.log ((L : ℝ)+(i : ℝ)+1) / Real.log Z) /
          (((L : ℝ)+(i : ℝ)+1) * Real.log Z)) -
        ∫ t in (Real.log ((L : ℝ)+1) / Real.log Z)..
          (Real.log ((L : ℝ)+(N : ℝ)+1) / Real.log Z), f t| ≤
      (M + (eVariationOn f (Set.Icc (Real.log ((L : ℝ)+1) / Real.log Z)
        (Real.log ((L : ℝ)+(N : ℝ)+1) / Real.log Z))).toReal) /
          ((L : ℝ) * Real.log Z) := by
  let e : ℕ → ℝ := fun i => Real.log ((L : ℝ)+(i : ℝ)+1) / Real.log Z
  let w : ℕ → ℝ := fun i => 1 / (((L : ℝ)+(i : ℝ)+1) * Real.log Z)
  have hlog : 0 < Real.log Z := Real.log_pos hZ
  have hL0 : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast (show 0 < L by omega)
  have he : Monotone e := by
    intro i j hij
    apply div_le_div_of_nonneg_right _ hlog.le
    apply Real.log_le_log (by positivity)
    have h : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  have hmesh : ∀ i < N, e (i+1)-e i ≤ 1 / ((L : ℝ)*Real.log Z) := by
    intro i _
    have hn : (0 : ℝ) < (L : ℝ)+(i : ℝ)+1 := by positivity
    have h := (four_exponent_mesh_bounds hZ hn).2
    have h' : 1 / (((L : ℝ)+(i : ℝ)+1) * Real.log Z) ≤
        1 / ((L : ℝ)*Real.log Z) := by
      apply one_div_le_one_div_of_le (by positivity)
      apply mul_le_mul_of_nonneg_right _ hlog.le
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    simpa only [e, Nat.cast_add, Nat.cast_one, add_assoc] using h.trans h'
  have hw : (∑ i ∈ Finset.range N, |w i-(e (i+1)-e i)|) ≤
      1 / ((L : ℝ)*Real.log Z) := by
    simpa only [e, w, Nat.cast_add, Nat.cast_one, add_assoc] using
      four_exponent_log_weight_error hZ L N hL
  have hie : IntervalIntegrable f volume (e 0) (e N) := by
    simpa only [e, Nat.cast_zero, add_zero] using hi
  have hbve : BoundedVariationOn f (Set.Icc (e 0) (e N)) := by
    simpa only [e, Nat.cast_zero, add_zero] using hbv
  have hbase := four_exponent_bv_weighted_rectangle f e he N w
    (by positivity : 0 ≤ 1 / ((L : ℝ)*Real.log Z)) hM hmesh hf hie hbve
  have hout := hbase.trans (show
      M * (∑ i ∈ Finset.range N, |w i-(e (i+1)-e i)|) +
        1 / ((L : ℝ)*Real.log Z) * (eVariationOn f (Set.Icc (e 0) (e N))).toReal ≤
      (M + (eVariationOn f (Set.Icc (e 0) (e N))).toReal) / ((L : ℝ)*Real.log Z) from by
    calc _ ≤ M * (1 / ((L : ℝ)*Real.log Z)) +
          1 / ((L : ℝ)*Real.log Z) * (eVariationOn f (Set.Icc (e 0) (e N))).toReal :=
            add_le_add (mul_le_mul_of_nonneg_left hw hM) le_rfl
      _ = _ := by ring)
  simpa only [e, w, Nat.cast_zero, add_zero, one_div_mul_eq_div] using hout

#print axioms four_exponent_bv_rectangle
#print axioms four_exponent_bv_weighted_rectangle
#print axioms four_exponent_shifted_inv_sq_sum
#print axioms four_exponent_log_weight_error
#print axioms four_exponent_log_bv_quadrature
end LeanLab.BHP1997.LowerShortC165
