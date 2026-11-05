import LeanLab.ChirreHagen2025.Decomp272c

/-!
P0075 page 3 boundary estimate after equation 2.1.
Schoenfeld 1976 pages 337 to 339 Theorem 10 equation 6.2 and its proof.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp358b
open MeasureTheory ArithmeticFunction Filter Topology

/-- LEAF. Schoenfeld 1976 page 339 proof of Theorem 10 equation 6.2.
Below exp 16 the proof uses Rosser and Schoenfeld's tables and Gram's table,
without RH. The range starts strictly above 73.2 as needed by P0075 page 3. -/
theorem schoenfeld_psi_small (y : ℝ) (hy : 73.2 < y) (hytop : y < Real.exp 16) :
    |Chebyshev.psi y - y| ≤ Real.sqrt y * Real.log y ^ 2 / (8 * Real.pi) := by
  sorry

/-- LEAF. Schoenfeld 1976 pages 337 to 339 proof of Theorem 10 equation 6.2.
Above exp 16 the zero-sum argument gives the RH estimate.
This is the analytic range and contains no finite range extension. -/
theorem schoenfeld_psi_large (hRH : RiemannHypothesis) (y : ℝ)
    (hy : Real.exp 16 ≤ y) :
    |Chebyshev.psi y - y| ≤ Real.sqrt y * Real.log y ^ 2 / (8 * Real.pi) := by
  sorry

/-- Schoenfeld 1976 page 337 Theorem 10 equation 6.2.
CONDITIONAL ON its separate finite and analytic range leaves. -/
theorem schoenfeld_psi (hRH : RiemannHypothesis) (y : ℝ) (hy : 73.2 < y) :
    |Chebyshev.psi y - y| ≤ Real.sqrt y * Real.log y ^ 2 / (8 * Real.pi) := by
  by_cases hlarge : Real.exp 16 ≤ y
  · exact schoenfeld_psi_large hRH y hlarge
  · exact schoenfeld_psi_small y hy (lt_of_not_ge hlarge)

/-- LEAF. P0075 page 3 equation 2.1, meaning of psi at N minus.
This finite step identity has no RH or analytic estimate. -/
theorem psi_left_limit (N : ℕ) (hN : 0 < N) :
    Tendsto Chebyshev.psi (𝓝[<] (N : ℝ))
      (𝓝 (∑ n ∈ Finset.Icc 1 (N - 1), vonMangoldt n)) := by
  have hlow : (N : ℝ) - 1 < (N : ℝ) := by linarith
  have heq : ∀ᶠ y in 𝓝[<] (N : ℝ),
      Chebyshev.psi y = ∑ n ∈ Finset.Icc 1 (N - 1), vonMangoldt n := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlow),
      self_mem_nhdsWithin] with y hylo hyhi
    simp only [Set.mem_Ioi, Set.mem_Iio] at hylo hyhi
    have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub hN, Nat.cast_one]
    have hy0 : 0 ≤ y := by
      have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hfloor : ⌊y⌋₊ = N - 1 := by
      apply (Nat.floor_eq_iff hy0).2
      constructor
      · rw [hcast]
        exact hylo.le
      · rw [hcast]
        simpa using hyhi
    rw [Chebyshev.psi_eq_sum_Icc, hfloor]
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Icc] at *
      omega
    · intro n hn hn'
      have hn0 : n = 0 := by
        simp only [Finset.mem_Icc] at *
        omega
      subst n
      simp
  exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)

/-- P0075 page 3 boundary estimate, before division by the complex power.
CONDITIONAL ON Schoenfeld's psi estimate. The left limit includes prime powers. -/
theorem psi_left_error (hRH : RiemannHypothesis) (N : ℕ) (hN : 74 ≤ N) :
    |(∑ n ∈ Finset.Icc 1 (N - 1), vonMangoldt n) - (N : ℝ)| ≤
      Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2 / (8 * Real.pi) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN73 : (73.2 : ℝ) < N := by
    have h : (74 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hl := ((psi_left_limit N (by omega)).sub nhdsWithin_le_nhds).abs
  have hr : Tendsto (fun y : ℝ => Real.sqrt y * Real.log y ^ 2 / (8 * Real.pi))
      (𝓝[<] (N : ℝ))
      (𝓝 (Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2 / (8 * Real.pi))) := by
    have hc : ContinuousAt (fun y : ℝ => Real.sqrt y * Real.log y ^ 2 / (8 * Real.pi))
        (N : ℝ) := by fun_prop
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hN73)] with y hy
  exact schoenfeld_psi hRH y hy

/-- P0075 page 3. Exact target statement from Decomp272c.
CONDITIONAL ON Schoenfeld's psi estimate and the finite left limit. -/
theorem psi_boundary_bound (hRH : RiemannHypothesis) (σ t : ℝ)
    (hσ : 1 < σ) (hσtop : σ < 2) (ht : 100 ≤ |t|) (N : ℕ) (hN : 74 ≤ N) :
    ‖(((∑ n ∈ Finset.Icc 1 (N - 1), vonMangoldt n) - (N : ℝ) : ℝ) : ℂ) /
      (N : ℂ) ^ ((σ : ℂ) + t * Complex.I)‖ ≤
        Real.log (N : ℝ) ^ 2 / (8 * Real.pi * Real.sqrt (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have herr := psi_left_error hRH N hN
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hN0]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hexp : (N : ℝ) ≤ (N : ℝ) ^ σ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 hσ.le
  calc
    _ ≤ (Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2 / (8 * Real.pi)) /
        (N : ℝ) ^ σ := div_le_div_of_nonneg_right herr (by positivity)
    _ ≤ (Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2 / (8 * Real.pi)) / (N : ℝ) := by
      exact div_le_div_of_nonneg_left (by positivity) hN0 hexp
    _ = _ := by
      have hs : Real.sqrt (N : ℝ) ≠ 0 := by positivity
      field_simp
      nlinarith [Real.sq_sqrt hN0.le]

end LeanLab.ChirreHagen2025.Decomp358b
