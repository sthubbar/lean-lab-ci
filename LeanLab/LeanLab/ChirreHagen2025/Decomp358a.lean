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
  have psi_mellin (s : ℂ) (hs : 1 < s.re) :
      LSeries (fun n => (vonMangoldt n : ℂ)) s =
        s * ∫ y in Set.Ioi (1 : ℝ), (Chebyshev.psi y : ℂ) / (y : ℂ) ^ (s + 1) := by
    have hset (n : ℕ) : Finset.Icc 1 n = Finset.Ioc 0 n := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hp (y : ℝ) : (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, vonMangoldt n) = Chebyshev.psi y := by
      rw [hset, Chebyshev.psi]
    have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, vonMangoldt k) =O[Filter.atTop]
        (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
      apply Asymptotics.IsBigO.of_bound (Real.log 4 + 4)
      filter_upwards [] with n
      have h := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) n)
      have hpn : (∑ k ∈ Finset.Icc 1 n, vonMangoldt k) = Chebyshev.psi n := by
        simpa using hp (n : ℝ)
      simpa only [hpn, Real.norm_eq_abs, abs_of_nonneg (Chebyshev.psi_nonneg _),
        Real.rpow_one, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using h
    have h := LSeries_eq_mul_integral_of_nonneg vonMangoldt (by norm_num) hs hO
      (fun n => vonMangoldt_nonneg)
    rw [h]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hc : (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (vonMangoldt n : ℂ)) = (Chebyshev.psi y : ℂ) := by
      rw [← hp]
      simp
    dsimp only
    rw [hc, Complex.cpow_neg]
    rfl
  have finite_cutoff (s : ℂ) (hs : 1 < s.re) (N : ℕ) (hN : 0 < N) :
      s * (∫ y in (1 : ℝ)..(N : ℝ), (Chebyshev.psi y : ℂ) / (y : ℂ) ^ (s + 1)) =
        (∑ n ∈ Finset.Icc 1 (N - 1), (vonMangoldt n : ℂ) / (n : ℂ) ^ s) -
        ((∑ n ∈ Finset.Icc 1 (N - 1), vonMangoldt n : ℝ) : ℂ) / (N : ℂ) ^ s := by
    have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
    have hsn : -s ≠ 0 := neg_ne_zero.mpr hs0
    let f : ℝ → ℂ := fun y => (y : ℂ) ^ (-s)
    have hd (y : ℝ) (hy : y ∈ Set.Icc (1 : ℝ) N) : DifferentiableAt ℝ f y := by
      exact (hasDerivAt_ofReal_cpow_const (by have : 1 ≤ y := hy.1; linarith) hsn).differentiableAt
    have hi : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) N) := by
      apply ContinuousOn.integrableOn_Icc
      intro y hy
      have hy0 : y ≠ 0 := by have : 1 ≤ y := hy.1; linarith
      have hder : deriv f y = -s * (y : ℂ) ^ (-s - 1) := Complex.deriv_ofReal_cpow_const hy0 hsn
      have hc : ContinuousAt (fun y : ℝ => -s * (y : ℂ) ^ (-s - 1)) y :=
        (Complex.continuousAt_ofReal_cpow_const y (-s - 1) (Or.inr hy0)).const_mul _
      have hsame : deriv f =ᶠ[nhds y] (fun y : ℝ => -s * (y : ℂ) ^ (-s - 1)) := by
        filter_upwards [eventually_ne_nhds hy0] with z hz
        exact Complex.deriv_ofReal_cpow_const hz hsn
      exact (hc.congr_of_eventuallyEq hsame).continuousWithinAt
    have ha := sum_mul_eq_sub_sub_integral_mul' (fun n => (vonMangoldt n : ℂ))
      (f := f) (show 1 ≤ N by omega)
      (by simpa only [Nat.cast_one] using hd) (by simpa only [Nat.cast_one] using hi)
    norm_num only [Nat.cast_one] at ha
    have hp (y : ℝ) : (∑ n ∈ Finset.Icc 0 ⌊y⌋₊, (vonMangoldt n : ℂ)) =
        (Chebyshev.psi y : ℂ) := by
      rw [Chebyshev.psi_eq_sum_Icc]
      simp
    have hpN : (∑ n ∈ Finset.Icc 0 N, (vonMangoldt n : ℂ)) = (Chebyshev.psi N : ℂ) := by
      simpa using hp (N : ℝ)
    have hp1 : (∑ n ∈ Finset.Icc 0 1, (vonMangoldt n : ℂ)) = 0 := by
      norm_num [Finset.sum_Icc_succ_top]
    rw [hpN, hp1, mul_zero, sub_zero] at ha
    have heq : (∫ t in Set.Ioc (1 : ℝ) N,
        deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (vonMangoldt k : ℂ)) =
        -s * (∫ t in (1 : ℝ)..(N : ℝ), (Chebyshev.psi t : ℂ) / (t : ℂ) ^ (s + 1)) := by
      rw [intervalIntegral.integral_of_le (by exact_mod_cast (show 1 ≤ N by omega)),
        ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      dsimp only
      rw [Complex.deriv_ofReal_cpow_const (by have : 1 < t := ht.1; linarith) hsn, hp]
      rw [show -s - 1 = -(s + 1) by ring, Complex.cpow_neg]
      ring
    rw [heq] at ha
    have hl : (∑ k ∈ Finset.Ioc 1 N, f k * (vonMangoldt k : ℂ)) =
        ∑ k ∈ Finset.Icc 1 N, (vonMangoldt k : ℂ) / (k : ℂ) ^ s := by
      calc
        _ = ∑ k ∈ Finset.Ioc 1 N, (vonMangoldt k : ℂ) / (k : ℂ) ^ s := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [f, Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]
          ring
        _ = _ := by
          apply Finset.sum_subset
          · intro k hk
            simp only [Finset.mem_Ioc, Finset.mem_Icc] at *
            omega
          · intro k hk hkn
            have hk1 : k = 1 := by
              simp only [Finset.mem_Ioc, Finset.mem_Icc] at *
              omega
            subst k
            simp
    rw [hl] at ha
    have hset : Finset.Icc 1 N = insert N (Finset.Icc 1 (N - 1)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : N ∉ Finset.Icc 1 (N - 1) := by simp; omega
    have hpNm : (Chebyshev.psi N : ℂ) =
        (vonMangoldt N : ℂ) + ((∑ n ∈ Finset.Icc 1 (N - 1), vonMangoldt n : ℝ) : ℂ) := by
      have hset1 : Finset.Icc 1 N = Finset.Ioc 0 N := by ext k; simp; omega
      simp only [Chebyshev.psi, Nat.floor_natCast]
      rw [← hset1, hset, Finset.sum_insert hnot]
      push_cast
      rfl
    rw [hset, Finset.sum_insert hnot, hpNm] at ha
    dsimp only [f] at ha
    rw [Complex.cpow_neg] at ha
    simp only [Complex.ofReal_natCast] at ha
    linear_combination -ha
  have hi1 := (Decomp358a.psi_kernel_integrable s hs 1 (by norm_num)).1
  have hiN := (Decomp358a.psi_kernel_integrable s hs N hN).1
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi1 hiN
  norm_num only [Nat.cast_one] at hsplit
  rw [psi_mellin s hs, ← hsplit, mul_add, finite_cutoff s hs N hN]

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
The finite Abel identity and the linear power integral are proved above. -/
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
