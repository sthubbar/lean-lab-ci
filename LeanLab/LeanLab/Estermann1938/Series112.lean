import LeanLab.Estermann1938.Decay112

/-!
Estermann 1938, P0091, pages 308 and 312, displays 7 and 39.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Estermann1938.Series112
open scoped BigOperators
open Decomp112 Ramanujan112 Decay112 Parseval112 Prime112

/-- The real coefficient μ squared divided by totient squared in display 7. -/
noncomputable def factor (q : ℕ) : ℝ :=
  (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2

/-- Estermann's infinite sum g3, display 7, with the zero term equal to zero. -/
noncomputable def g3 (n : ℕ) (x : ℝ) : ℂ :=
  ∑' q : ℕ, (factor q : ℂ) * g2 n x q

/-- The coefficients of display 7 are nonnegative. -/
theorem factor_nonneg (q : ℕ) : 0 ≤ factor q := by unfold factor; positivity

/-- Discarding μ squared bounds the coefficient by reciprocal totient squared. -/
theorem factor_le_inv_totient_sq (q : ℕ) : factor q ≤ ((q.totient : ℝ)⁻¹) ^ 2 := by
  have hmu : (ArithmeticFunction.moebius q : ℝ) ^ 2 ≤ 1 := by
    rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;> simp [h]
  unfold factor
  rw [div_eq_mul_inv, inv_pow]
  simpa using mul_le_mul_of_nonneg_right hmu (sq_nonneg ((q.totient : ℝ)⁻¹))

/-- The normalized estimate in display 39 also bounds each term in display 7. -/
theorem term_norm_le (n q : ℕ) (x : ℝ) :
    ‖(factor q : ℂ) * g2 n x q‖ ≤ ‖g2 n x q / (q.totient : ℂ) ^ 2‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (factor_nonneg q)]
  calc
    factor q * ‖g2 n x q‖ ≤ ((q.totient : ℝ)⁻¹) ^ 2 * ‖g2 n x q‖ :=
      mul_le_mul_of_nonneg_right (factor_le_inv_totient_sq q) (norm_nonneg _)
    _ = _ := by
      rw [norm_div, norm_pow, Complex.norm_natCast, div_eq_mul_inv, inv_pow]
      ring

/-- Absolute convergence of the infinite sum in display 7 follows from display 39. -/
theorem g3_summable (n : ℕ) (x : ℝ) :
    Summable (fun q : ℕ => (factor q : ℂ) * g2 n x q) := by
  obtain ⟨A, hA, hbound⟩ := display39
  have hp : Summable (fun q : ℕ => (q : ℝ) ^ (-(3 : ℝ) / 2)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply (hp.mul_left (A * (n : ℝ) ^ 2)).of_norm_bounded
  intro q
  by_cases hq : q = 0
  · subst q
    simp [g2, residues]
  · exact (term_norm_le n q x).trans (hbound n x q (by omega))

/-- The real singular series S in display 44, page 313. -/
noncomputable def S (m : ℕ) : ℝ := ∑' q : ℕ, factor q * (c q m).re

/-- Each Ramanujan sum is the inclusion of its real part. -/
theorem c_eq_re (q m : ℕ) : ((c q m).re : ℂ) = c q m := by
  by_cases hq : q = 0
  · subst q
    simp [c, residues]
  · rw [c_eq_ramanujan (by omega : 1 ≤ q)]
    simp

/-- The real singular series in display 44 agrees with the complex sum of its real terms. -/
theorem S_cast (m : ℕ) : (S m : ℂ) = ∑' q : ℕ, (factor q : ℂ) * c q m := by
  unfold S
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro q
  rw [Complex.ofReal_mul, c_eq_re]

/-- Absolute convergence of display 44 at every positive frequency. -/
theorem singular_summable (m : ℕ) (hm : 1 ≤ m) :
    Summable (fun q : ℕ => (factor q : ℂ) * c q m) := by
  let B : ℝ := 9 * Real.exp 1 * (1 + (Real.log 2)⁻¹)
  have hB : 0 < B := by dsimp [B]; positivity
  have hp : Summable (fun q : ℕ => (q : ℝ) ^ (-(13 : ℝ) / 8)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply (hp.mul_left (9 * (m : ℝ) * B ^ 2)).of_norm_bounded
  intro q
  by_cases hq : q = 0
  · subst q
    simp [c, residues]
  · have hq1 : 1 ≤ q := by omega
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
    have hg : (Nat.gcd q m : ℝ) ≤ m := by exact_mod_cast Nat.gcd_le_right q hm
    have hL : 0 ≤ 1 + Real.log q := by have := Real.log_natCast_nonneg q; positivity
    have hc : ‖c q m‖ ≤ (m : ℝ) * (9 * (q : ℝ) ^ ((1 : ℝ) / 8)) := by
      calc
        ‖c q m‖ ≤ (Nat.gcd q m : ℝ) * (1 + Real.log q) := c_norm_le_gcd_log hq1 m
        _ ≤ (m : ℝ) * (1 + Real.log q) := mul_le_mul_of_nonneg_right hg hL
        _ ≤ _ := mul_le_mul_of_nonneg_left (log_factor_le hq1) (Nat.cast_nonneg m)
    have hi : (q.totient : ℝ)⁻¹ ≤ B * (q : ℝ) ^ ((1 : ℝ) / 8) / q := inv_totient_le hq1
    have hf : factor q ≤ (B * (q : ℝ) ^ ((1 : ℝ) / 8) / q) ^ 2 :=
      (factor_le_inv_totient_sq q).trans
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹) hi 2)
    have he : ((q : ℝ) ^ ((1 : ℝ) / 8)) ^ 3 / (q : ℝ) ^ 2 =
        (q : ℝ) ^ (-(13 : ℝ) / 8) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hqR.le]
      norm_num
      rw [← Real.rpow_two, ← Real.rpow_sub hqR]
      norm_num
    calc
      ‖(factor q : ℂ) * c q m‖ = factor q * ‖c q m‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (factor_nonneg q)]
      _ ≤ (B * (q : ℝ) ^ ((1 : ℝ) / 8) / q) ^ 2 *
          ((m : ℝ) * (9 * (q : ℝ) ^ ((1 : ℝ) / 8))) :=
        mul_le_mul hf hc (norm_nonneg _) (sq_nonneg _)
      _ = (9 * (m : ℝ) * B ^ 2) *
          (((q : ℝ) ^ ((1 : ℝ) / 8)) ^ 3 / (q : ℝ) ^ 2) := by ring
      _ = _ := by rw [he]

/-- Display 45, page 313: the actual infinite g3 sum equals its finite Fourier expansion. -/
theorem display45 (n : ℕ) (x : ℝ) :
    g3 n x = ∑ m ∈ Finset.Icc 1 (2 * n), ((b n m * S m : ℝ) : ℂ) * phase x m := by
  let F (m q : ℕ) : ℂ := (b n m : ℂ) * ((factor q : ℂ) * c q m) * phase x m
  have hs : ∀ m ∈ Finset.Icc 1 (2 * n), Summable (F m) := by
    intro m hm
    exact ((singular_summable m (Finset.mem_Icc.mp hm).1).mul_left (b n m : ℂ)).mul_right (phase x m)
  have hexp (q : ℕ) : (factor q : ℂ) * g2 n x q = ∑ m ∈ Finset.Icc 1 (2 * n), F m q := by
    by_cases hq : q = 0
    · subst q
      simp [factor, F]
    · rw [display37 n x (by omega : 1 ≤ q), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      dsimp [F]
      ring
  calc
    g3 n x = ∑' q : ℕ, ∑ m ∈ Finset.Icc 1 (2 * n), F m q := by
      unfold g3
      exact tsum_congr hexp
    _ = ∑ m ∈ Finset.Icc 1 (2 * n), ∑' q : ℕ, F m q := Summable.tsum_finsetSum hs
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      dsimp [F]
      rw [tsum_mul_right, tsum_mul_left, ← S_cast]
      push_cast
      ring

/-- Display 47, page 313: Parseval for the exact prime sum minus the exact infinite g3 sum. -/
theorem display47 (n : ℕ) :
    (∫ x in (0 : ℝ)..1, ‖f n x ^ 2 - g3 n x‖ ^ 2) =
      ∑ m ∈ Finset.Icc 1 (2 * n), ((a n m : ℝ) - b n m * S m) ^ 2 := by
  have hexp (x : ℝ) : f n x ^ 2 - g3 n x =
      ∑ m ∈ Finset.Icc 1 (2 * n),
        (((a n m : ℝ) - b n m * S m : ℝ) : ℂ) * phase x m := by
    rw [display46, display45, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    push_cast
    ring
  simp_rw [hexp]
  have h := parseval_nat (Finset.Icc 1 (2 * n))
    (fun m => (((a n m : ℝ) - b n m * S m : ℝ) : ℂ))
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

#print axioms c_eq_re
#print axioms S_cast
#print axioms singular_summable
#print axioms display45
#print axioms display47

#print axioms factor_nonneg
#print axioms factor_le_inv_totient_sq
#print axioms term_norm_le
#print axioms g3_summable

end LeanLab.Estermann1938.Series112
