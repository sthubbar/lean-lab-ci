import LeanLab.ChirreHagen2025.Decomp272c

/-!
P0075 page 3 equation 2.1. Backlund 1916 pages 345 to 346 gives the
Dirichlet series and partial integration route. The Mangoldt version is
written in P0075. AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp358a
open MeasureTheory ArithmeticFunction

/-- P0075 page 3 equation 2.1, absolute convergence under linear growth.
This is the dominated-integrability component of the partial summation argument. -/
theorem linear_growth_kernel_integrable (f : ℝ → ℝ) (hf : Measurable f)
    (s : ℂ) (hs : 1 < s.re) (N C : ℝ) (hN : 0 < N)
    (hbound : ∀ y : ℝ, N < y → |f y| ≤ C * y) :
    IntegrableOn (fun y : ℝ => (f y : ℂ) / (y : ℂ) ^ (s + 1)) (Set.Ioi N) := by
  have hc : Continuous (fun y : ℝ => (y : ℂ) ^ (s + 1)) :=
    Complex.continuous_ofReal_cpow_const (by simp; linarith)
  have hm : Measurable (fun y : ℝ => (f y : ℂ) / (y : ℂ) ^ (s + 1)) :=
    (Complex.continuous_ofReal.measurable.comp hf).div hc.measurable
  have hg := (integrableOn_Ioi_rpow_of_lt (show -s.re < -1 by linarith) hN).const_mul C
  apply hg.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : 0 < y := hN.trans hy
  have hp0 : y ^ s.re ≠ 0 := (Real.rpow_pos_of_pos hy0 _).ne'
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hy0]
  simp only [Complex.add_re, Complex.one_re]
  calc
    _ ≤ (C * y) / y ^ (s.re + 1) :=
      div_le_div_of_nonneg_right (hbound y hy) (by positivity)
    _ = C * y ^ (-s.re) := by
      rw [Real.rpow_add hy0, Real.rpow_one, Real.rpow_neg hy0.le]
      field_simp

/-- LEAF. P0075 page 3 equation 2.1, convergence before partial summation.
These are the uncentered psi kernel and the elementary linear kernel.
There is no zeta identity or explicit RH estimate in this leaf. -/
theorem psi_kernel_integrable (s : ℂ) (hs : 1 < s.re) (N : ℕ) (hN : 0 < N) :
    IntegrableOn (fun y : ℝ => (Chebyshev.psi y : ℂ) / (y : ℂ) ^ (s + 1))
      (Set.Ioi (N : ℝ)) ∧
    IntegrableOn (fun y : ℝ => (y : ℂ) / (y : ℂ) ^ (s + 1))
      (Set.Ioi (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · apply linear_growth_kernel_integrable Chebyshev.psi Chebyshev.psi_mono.measurable
      s hs (N : ℝ) (Real.log 4 + 4) hN0
    intro y hy
    rw [abs_of_nonneg (Chebyshev.psi_nonneg y)]
    exact Chebyshev.psi_le_const_mul_self (hN0.trans hy).le
  · apply linear_growth_kernel_integrable id measurable_id s hs (N : ℝ) 1 hN0
    intro y hy
    simp only [id_eq, one_mul, abs_of_pos (hN0.trans hy), le_refl]

/-- LEAF. P0075 page 3 equation 2.1, the partial summation step alone.
This identity concerns the Mangoldt Dirichlet series and an uncentered psi
integral. It has neither the zeta derivative nor the pole correction. -/
theorem mangoldt_partial_summation (s : ℂ) (hs : 1 < s.re)
    (N : ℕ) (hN : 0 < N) :
    LSeries (fun n => (vonMangoldt n : ℂ)) s =
      (∑ n ∈ Finset.Icc 1 (N - 1), (vonMangoldt n : ℂ) / (n : ℂ) ^ s) -
      ((∑ n ∈ Finset.Icc 1 (N - 1), vonMangoldt n : ℝ) : ℂ) / (N : ℂ) ^ s +
      s * ∫ y in Set.Ioi (N : ℝ), (Chebyshev.psi y : ℂ) / (y : ℂ) ^ (s + 1) := by
  sorry

/-- LEAF. P0075 page 3 equation 2.1, integration of the subtracted linear term.
This is an elementary complex power integral with no arithmetic input. -/
theorem linear_kernel_integral (s : ℂ) (hs : 1 < s.re) (N : ℝ) (hN : 0 < N) :
    s * (∫ y in Set.Ioi N, (y : ℂ) / (y : ℂ) ^ (s + 1)) =
      (N : ℂ) / (N : ℂ) ^ s + (N : ℂ) ^ (1 - s) / (s - 1) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have heq : (∫ y in Set.Ioi N, (y : ℂ) / (y : ℂ) ^ (s + 1)) =
      ∫ y in Set.Ioi N, (y : ℂ) ^ (-s) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (hN.trans hy).ne'
    dsimp only
    rw [show -s = (1 : ℂ) - (s + 1) by ring, Complex.cpow_sub _ _ hy0,
      Complex.cpow_one]
  rw [heq, integral_Ioi_cpow_of_lt (by simpa using (show -s.re < -1 by linarith)) hN]
  have hs0 : s - 1 ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    simp at hreal
    linarith
  rw [show -s + 1 = (1 : ℂ) - s by ring]
  rw [Complex.cpow_sub _ _ hN0, Complex.cpow_one]
  have hp0 : (N : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hN0)
  rw [show (1 : ℂ) - s = -(s - 1) by ring]
  field_simp [hs0, hp0]
  <;> ring

/-- P0075 page 3 equation 2.1. Exact target statement from Decomp272c.
CONDITIONAL ON the smaller Mangoldt partial summation leaf. -/
theorem backlund_identity (σ t : ℝ) (hσ : 1 < σ) (hσtop : σ < 2)
    (ht : 100 ≤ |t|) (N : ℕ) (hN : 74 ≤ N) :
    IntegrableOn
      (fun y : ℝ => ((Chebyshev.psi y - y : ℝ) : ℂ) /
        (y : ℂ) ^ ((σ : ℂ) + t * Complex.I + 1)) (Set.Ioi (N : ℝ)) ∧
    -(deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)) =
      (∑ n ∈ Finset.Icc 1 (N - 1),
        (vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * Complex.I)) -
      (((∑ n ∈ Finset.Icc 1 (N - 1), vonMangoldt n) - (N : ℝ) : ℝ) : ℂ) /
        (N : ℂ) ^ ((σ : ℂ) + t * Complex.I) +
      (N : ℂ) ^ (1 - ((σ : ℂ) + t * Complex.I)) /
        ((σ : ℂ) + t * Complex.I - 1) +
      ((σ : ℂ) + t * Complex.I) *
        ∫ y in Set.Ioi (N : ℝ), ((Chebyshev.psi y - y : ℝ) : ℂ) /
          (y : ℂ) ^ ((σ : ℂ) + t * Complex.I + 1)  := by
  let s : ℂ := (σ : ℂ) + t * Complex.I
  have hs : 1 < s.re := by simpa [s] using hσ
  have hN0 : 0 < N := by omega
  have hi := psi_kernel_integrable s hs N hN0
  have hsub : IntegrableOn
      (fun y : ℝ => ((Chebyshev.psi y - y : ℝ) : ℂ) / (y : ℂ) ^ (s + 1))
      (Set.Ioi (N : ℝ)) := by
    convert hi.1.sub hi.2 using 1
    ext y
    simp only [Complex.ofReal_sub, sub_div, Pi.sub_apply]
  refine ⟨hsub, ?_⟩
  have hds := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hp := mangoldt_partial_summation s hs N hN0
  have hl := linear_kernel_integral s hs (N : ℝ) (by positivity)
  have heq : (∫ y in Set.Ioi (N : ℝ),
      ((Chebyshev.psi y - y : ℝ) : ℂ) / (y : ℂ) ^ (s + 1)) =
      (∫ y in Set.Ioi (N : ℝ), (Chebyshev.psi y : ℂ) / (y : ℂ) ^ (s + 1)) -
      ∫ y in Set.Ioi (N : ℝ), (y : ℂ) / (y : ℂ) ^ (s + 1) := by
    simp only [Complex.ofReal_sub, sub_div]
    exact integral_sub hi.1 hi.2
  change -(deriv riemannZeta s / riemannZeta s) = _
  rw [neg_div] at hds
  rw [← hds, hp]
  change _ = _ - (((∑ n ∈ Finset.Icc 1 (N - 1), vonMangoldt n) - (N : ℝ) : ℝ) : ℂ) / (N : ℂ) ^ s + (N : ℂ) ^ (1 - s) / (s - 1) + s * (∫ y in Set.Ioi (N : ℝ), ((Chebyshev.psi y - y : ℝ) : ℂ) / (y : ℂ) ^ (s + 1))
  rw [heq, mul_sub, hl]
  push_cast
  ring

end LeanLab.ChirreHagen2025.Decomp358a
