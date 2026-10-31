import LeanLab.Pintz2021.AdditiveVaughanTask08
import LeanLab.PNTPort.BV.TypeI

/-!
Type I helpers for P0054 Lemma 1, display 1.10, author copy page 3.
AI wrote the Lean code. Goldbach is open.
These are algebraic and geometric helpers for the Vaughan route.
They do not assume VaughanThm31.
-/

namespace LeanLab.Pintz2021.AdditiveTypeITask08

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.BV
open LeanLab.Pintz2021.AdditiveVaughanTask08
open LeanLab.Pintz2021.Lemma1U1369

/-- An additive convolution sum in hyperbolic coordinates. -/
theorem sum_conv_additive (F : ℕ × ℕ → ℝ) (N : ℕ) (α : ℝ) :
    ∑ n ∈ Icc 1 N, ((∑ p ∈ n.divisorsAntidiagonal, F p : ℝ) : ℂ) * e (n * α) =
      ∑ t ∈ Icc 1 N, ∑ r ∈ Icc 1 (N / t), (F (t, r) : ℂ) * e (r * (t * α)) := by
  rw [← sum_Icc_divisorsAntidiagonal
    (fun p => (F p : ℂ) * e ((p.2 : ℝ) * (p.1 * α)))]
  refine sum_congr rfl fun n _ => ?_
  rw [Complex.ofReal_sum, sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, Nat.cast_mul]
  congr 2
  ring

/-- The short convolution coefficient in the second Vaughan sum. -/
noncomputable def typeICoeff (u v t : ℕ) : ℝ :=
  ∑ y ∈ t.divisorsAntidiagonal,
    if y.1 ≤ u ∧ y.2 ≤ v then Λ y.1 * (μ y.2 : ℝ) else 0

/-- V2 as short coefficients times geometric sums. -/
theorem V2_factor (x α : ℝ) (u v : ℕ) :
    V2 x α u v = ∑ t ∈ Icc 1 ⌊x⌋₊, (typeICoeff u v t : ℂ) *
      ∑ r ∈ Icc 1 (⌊x⌋₊ / t), e (r * (t * α)) := by
  unfold V2
  rw [sum_conv_additive]
  refine sum_congr rfl fun t _ => ?_
  rw [mul_sum]
  rfl

/-- Coefficient size and support, including t equal to zero. -/
theorem typeICoeff_bound (u v t : ℕ) :
    |typeICoeff u v t| ≤ if t ≤ u * v then Real.log t else 0 := by
  unfold typeICoeff
  split_ifs with ht
  · calc |∑ y ∈ t.divisorsAntidiagonal,
          if y.1 ≤ u ∧ y.2 ≤ v then Λ y.1 * (μ y.2 : ℝ) else 0|
        ≤ ∑ y ∈ t.divisorsAntidiagonal,
          |if y.1 ≤ u ∧ y.2 ≤ v then Λ y.1 * (μ y.2 : ℝ) else 0| :=
            abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ t.divisorsAntidiagonal, (Λ y.1 : ℝ) := by
        refine sum_le_sum fun y _ => ?_
        split_ifs
        · rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
          refine mul_le_of_le_one_right vonMangoldt_nonneg ?_
          exact_mod_cast abs_moebius_le_one
        · simpa only [abs_zero] using (vonMangoldt_nonneg (n := y.1) : (0 : ℝ) ≤ Λ y.1)
      _ = Real.log t := by
        rw [Nat.sum_divisorsAntidiagonal (fun a _ => (Λ a : ℝ)), vonMangoldt_sum]
  · have hz : ∑ y ∈ t.divisorsAntidiagonal,
        (if y.1 ≤ u ∧ y.2 ≤ v then (Λ y.1 : ℝ) * (μ y.2 : ℝ) else 0) = 0 := by
      refine sum_eq_zero fun y hy => ?_
      rw [ite_eq_right]
      intro h
      exact ht ((Nat.mem_divisorsAntidiagonal.mp hy).1 ▸ Nat.mul_le_mul h.1 h.2)
    rw [hz, abs_zero]

/-- The geometric majorant retains the trivial bound at integer frequencies. -/
noncomputable def geomBound (N : ℕ) (θ : ℝ) : ℝ :=
  if dist0 θ = 0 then N else min (N : ℝ) (1 / (2 * dist0 θ))

/-- The positive-index geometric sum bound at every real frequency. -/
theorem norm_geom_Icc_le (N : ℕ) (θ : ℝ) :
    ‖∑ r ∈ Icc 1 N, e (r * θ)‖ ≤ geomBound N θ := by
  have heq : ∑ r ∈ Icc 1 N, e (r * θ) =
      e θ * ∑ k ∈ range N, e (k * θ) := by
    rw [sum_Icc_one_eq_range, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, e_add]
    exact mul_comm _ _
  have htriv : ‖∑ r ∈ Icc 1 N, e (r * θ)‖ ≤ (N : ℝ) := by
    calc _ ≤ ∑ r ∈ Icc 1 N, ‖e (r * θ)‖ := norm_sum_le _ _
      _ = N := by simp [norm_e]
  unfold geomBound
  split_ifs with hz
  · exact htriv
  · refine le_min htriv ?_
    rw [heq, norm_mul, norm_e, one_mul]
    exact norm_geom_le N (lt_of_le_of_ne (dist0_nonneg θ) (Ne.symm hz))

/-- The coefficient support shortens V2 to t at most uv. -/
theorem V2_short (x α : ℝ) (u v : ℕ) :
    V2 x α u v = ∑ t ∈ Icc 1 (min ⌊x⌋₊ (u * v)), (typeICoeff u v t : ℂ) *
      ∑ r ∈ Icc 1 (⌊x⌋₊ / t), e (r * (t * α)) := by
  rw [V2_factor]
  symm
  apply sum_subset (Icc_subset_Icc le_rfl (min_le_left _ _))
  intro t ht hn
  have htuv : ¬ t ≤ u * v := by
    simp only [mem_Icc] at ht hn
    omega
  have hb := typeICoeff_bound u v t
  rw [ite_eq_right htuv] at hb
  have hz : typeICoeff u v t = 0 := abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
  simp [hz]

/-- The geometric Type I estimate for V2 before Diophantine summation. -/
theorem norm_V2_le {x : ℝ} (hx : 1 ≤ x) (α : ℝ) (u v : ℕ) :
    ‖V2 x α u v‖ ≤ Real.log x *
      ∑ t ∈ Icc 1 (min ⌊x⌋₊ (u * v)), geomBound (⌊x⌋₊ / t) (t * α) := by
  rw [V2_short, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun t ht => ?_)
  have ht1 := (mem_Icc.mp ht).1
  have htN := (le_min_iff.mp (mem_Icc.mp ht).2).1
  have htuv := (le_min_iff.mp (mem_Icc.mp ht).2).2
  have hc := typeICoeff_bound u v t
  rw [ite_eq_left htuv] at hc
  have hlog : Real.log (t : ℝ) ≤ Real.log x :=
    log_nat_le hx ((by exact_mod_cast htN : (t : ℝ) ≤ ⌊x⌋₊).trans
      (Nat.floor_le (by linarith)))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (hc.trans hlog) (norm_geom_Icc_le _ _)
    (norm_nonneg _) (Real.log_nonneg hx)

/-- Abel summation for the logarithmically weighted geometric sum. -/
theorem norm_log_geom_Icc_le (Y : ℕ) (θ : ℝ) :
    ‖∑ r ∈ Icc 1 Y, (Real.log r : ℂ) * e (r * θ)‖ ≤
      2 * Real.log Y * geomBound Y θ := by
  have hmono : ∀ k : ℕ, k ≤ Y → geomBound k θ ≤ geomBound Y θ := by
    intro k hk
    unfold geomBound
    split_ifs
    · exact_mod_cast hk
    · exact min_le_min (by exact_mod_cast hk) le_rfl
  have hB : ∀ k : ℕ, k ≤ Y →
      ‖∑ j ∈ range k, e (((j + 1 : ℕ) : ℝ) * θ)‖ ≤ geomBound Y θ := by
    intro k hk
    rw [← sum_Icc_one_eq_range (fun r : ℕ => e (r * θ)) k]
    exact (norm_geom_Icc_le k θ).trans (hmono k hk)
  have hlog : 0 ≤ Real.log (Y : ℝ) := Real.log_natCast_nonneg Y
  rw [sum_Icc_one_eq_range]
  have h := abel_range (fun r => Real.log (r : ℝ)) (fun r => e (r * θ)) Y
  rw [h]
  calc _ ≤ ‖(Real.log (Y : ℝ) : ℂ) * ∑ j ∈ range Y, e (((j + 1 : ℕ) : ℝ) * θ)‖ +
      ‖∑ r ∈ range Y, ((Real.log ((r + 1 : ℕ) : ℝ) - Real.log (r : ℝ) : ℝ) : ℂ) *
        ∑ j ∈ range r, e (((j + 1 : ℕ) : ℝ) * θ)‖ := norm_sub_le _ _
    _ ≤ Real.log Y * geomBound Y θ + ∑ r ∈ range Y,
        (Real.log ((r + 1 : ℕ) : ℝ) - Real.log (r : ℝ)) * geomBound Y θ := by
      refine add_le_add ?_ ?_
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog]
        exact mul_le_mul_of_nonneg_left (hB Y le_rfl) hlog
      · refine (norm_sum_le _ _).trans (sum_le_sum fun r hr => ?_)
        have hm := sub_nonneg.mpr (log_nat_mono r)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hm]
        exact mul_le_mul_of_nonneg_left (hB r (Nat.le_of_lt (mem_range.mp hr))) hm
    _ = 2 * Real.log Y * geomBound Y θ := by
      rw [← sum_mul, sum_range_sub (fun r : ℕ => Real.log (r : ℝ))]
      simp only [Nat.cast_zero, Real.log_zero, sub_zero]
      ring

/-- The third Vaughan sum in short hyperbolic form. -/
theorem V3_factor (x α : ℝ) (v : ℕ) :
    V3 x α v = ∑ d ∈ Icc 1 (min ⌊x⌋₊ v), ((μ d : ℝ) : ℂ) *
      ∑ r ∈ Icc 1 (⌊x⌋₊ / d), (Real.log r : ℂ) * e (r * (d * α)) := by
  unfold V3
  rw [sum_conv_additive]
  have hfull : ∑ d ∈ Icc 1 ⌊x⌋₊, ∑ r ∈ Icc 1 (⌊x⌋₊ / d),
      ((if d ≤ v then (μ d : ℝ) * Real.log r else 0 : ℝ) : ℂ) * e (r * (d * α)) =
      ∑ d ∈ Icc 1 ⌊x⌋₊, if d ≤ v then ((μ d : ℝ) : ℂ) *
        ∑ r ∈ Icc 1 (⌊x⌋₊ / d), (Real.log r : ℂ) * e (r * (d * α)) else 0 := by
    refine sum_congr rfl fun d _ => ?_
    by_cases hd : d ≤ v
    · simp only [hd, ite_true, Complex.ofReal_mul, mul_sum, mul_assoc]
    · simp [hd]
  rw [hfull]
  have hs : ∑ d ∈ Icc 1 (min ⌊x⌋₊ v),
      (if d ≤ v then ((μ d : ℝ) : ℂ) *
        ∑ r ∈ Icc 1 (⌊x⌋₊ / d), (Real.log r : ℂ) * e (r * (d * α)) else 0) =
      ∑ d ∈ Icc 1 ⌊x⌋₊, if d ≤ v then ((μ d : ℝ) : ℂ) *
        ∑ r ∈ Icc 1 (⌊x⌋₊ / d), (Real.log r : ℂ) * e (r * (d * α)) else 0 := by
    apply sum_subset (Icc_subset_Icc le_rfl (min_le_left _ _))
    intro d hd hn
    have hdv : ¬ d ≤ v := by simp only [mem_Icc] at hd hn; omega
    simp [hdv]
  rw [← hs]
  refine sum_congr rfl fun d hd => ?_
  rw [ite_eq_left ((le_min_iff.mp (mem_Icc.mp hd).2).2)]

/-- The geometric Type I estimate for V3 before Diophantine summation. -/
theorem norm_V3_le {x : ℝ} (hx : 1 ≤ x) (α : ℝ) (v : ℕ) :
    ‖V3 x α v‖ ≤ 2 * Real.log x *
      ∑ d ∈ Icc 1 (min ⌊x⌋₊ v), geomBound (⌊x⌋₊ / d) (d * α) := by
  rw [V3_factor, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun d _ => ?_)
  have hYN : ((⌊x⌋₊ / d : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    exact_mod_cast Nat.div_le_self ⌊x⌋₊ d
  have hYx : ((⌊x⌋₊ / d : ℕ) : ℝ) ≤ x := hYN.trans (Nat.floor_le (by linarith))
  have hlog : Real.log ((⌊x⌋₊ / d : ℕ) : ℝ) ≤ Real.log x := log_nat_le hx hYx
  have hG0 : 0 ≤ geomBound (⌊x⌋₊ / d) (d * α) :=
    (norm_nonneg _).trans (norm_geom_Icc_le _ _)
  have hs := (norm_log_geom_Icc_le (⌊x⌋₊ / d) (d * α)).trans
    (mul_le_mul_of_nonneg_right (show 2 * Real.log ((⌊x⌋₊ / d : ℕ) : ℝ) ≤
      2 * Real.log x by linarith) hG0)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc _ ≤ 1 * (2 * Real.log x * geomBound (⌊x⌋₊ / d) (d * α)) :=
      mul_le_mul (by exact_mod_cast abs_moebius_le_one) hs (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The first Vaughan sum costs at most the Chebyshev bound at u. -/
theorem norm_V1_le (x α : ℝ) (u : ℕ) :
    ‖V1 x α u‖ ≤ (Real.log 4 + 4) * u := by
  unfold V1
  calc _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, (if n ≤ u then (Λ n : ℝ) else 0) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
        have h0 : 0 ≤ (if n ≤ u then (Λ n : ℝ) else 0) := by
          split_ifs <;> simp [vonMangoldt_nonneg]
        rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_of_nonneg h0]
    _ ≤ ∑ n ∈ Icc 1 u, (Λ n : ℝ) := by
      rw [← sum_filter]
      refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => vonMangoldt_nonneg
      intro n hn
      simp only [mem_filter, mem_Icc] at hn ⊢
      omega
    _ = Chebyshev.psi u := by rw [Chebyshev.psi, Nat.floor_natCast]; rfl
    _ ≤ _ := Chebyshev.psi_le_const_mul_self (by positivity)

/-- Reduction of the full sum to geometric Type I sums and the remaining V4. -/
theorem norm_VS_TypeI {x : ℝ} (hx : 1 ≤ x) (α : ℝ) (u v : ℕ) (hv : 1 ≤ v) :
    ‖VS x α‖ ≤ (Real.log 4 + 4) * u +
      Real.log x * (∑ t ∈ Icc 1 (min ⌊x⌋₊ (u * v)), geomBound (⌊x⌋₊ / t) (t * α)) +
      2 * Real.log x * (∑ d ∈ Icc 1 (min ⌊x⌋₊ v), geomBound (⌊x⌋₊ / d) (d * α)) +
      ‖V4 x α u v‖ := by
  rw [VS_decomp x α u v hv]
  calc _ ≤ ‖V1 x α u - V2 x α u v + V3 x α v‖ + ‖V4 x α u v‖ := norm_sub_le _ _
    _ ≤ (‖V1 x α u - V2 x α u v‖ + ‖V3 x α v‖) + ‖V4 x α u v‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ((‖V1 x α u‖ + ‖V2 x α u v‖) + ‖V3 x α v‖) + ‖V4 x α u v‖ :=
      add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
    _ ≤ _ := by
      gcongr
      · exact norm_V1_le x α u
      · exact norm_V2_le hx α u v
      · exact norm_V3_le hx α v

end LeanLab.Pintz2021.AdditiveTypeITask08

#print axioms LeanLab.Pintz2021.AdditiveTypeITask08.sum_conv_additive
#print axioms LeanLab.Pintz2021.AdditiveTypeITask08.V2_factor
#print axioms LeanLab.Pintz2021.AdditiveTypeITask08.typeICoeff_bound
#print axioms LeanLab.Pintz2021.AdditiveTypeITask08.norm_geom_Icc_le
#print axioms LeanLab.Pintz2021.AdditiveTypeITask08.V2_short
#print axioms LeanLab.Pintz2021.AdditiveTypeITask08.norm_V2_le
#print axioms LeanLab.Pintz2021.AdditiveTypeITask08.norm_log_geom_Icc_le
#print axioms LeanLab.Pintz2021.AdditiveTypeITask08.V3_factor
#print axioms LeanLab.Pintz2021.AdditiveTypeITask08.norm_V3_le
#print axioms LeanLab.Pintz2021.AdditiveTypeITask08.norm_V1_le
#print axioms LeanLab.Pintz2021.AdditiveTypeITask08.norm_VS_TypeI
