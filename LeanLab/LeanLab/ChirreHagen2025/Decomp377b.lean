import LeanLab.ChirreHagen2025.Decomp358a

/-!
P0075 page 3 equation 2.1, splitting the Mangoldt partial summation input.
The full half plane integral is supplied by Mathlib Abel summation.
The finite cutoff step is a separate leaf with no improper limit.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp377b
open MeasureTheory ArithmeticFunction Filter

/-- P0075 page 3 equation 2.1, the full Mangoldt Mellin integral before the cutoff. -/
theorem psi_mellin (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (vonMangoldt n : ℂ)) s =
      s * ∫ y in Set.Ioi (1 : ℝ), (Chebyshev.psi y : ℂ) / (y : ℂ) ^ (s + 1) := by
  have hset (n : ℕ) : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hp (y : ℝ) : (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, vonMangoldt n) = Chebyshev.psi y := by
    rw [hset, Chebyshev.psi]
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, vonMangoldt k) =O[atTop]
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

/-- LEAF. P0075 page 3 equation 2.1, finite Abel summation on one to N.
Only a finite interval and finite sums occur. The term at N cancels
between the inclusive endpoint sum and its boundary coefficient. -/
theorem finite_cutoff (s : ℂ) (hs : 1 < s.re) (N : ℕ) (hN : 0 < N) :
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

/-- P0075 page 3 equation 2.1, exact Decomp358a partial summation statement.
The finite interval identity is proved by Mathlib finite Abel summation. -/
theorem mangoldt_partial_summation (s : ℂ) (hs : 1 < s.re)
    (N : ℕ) (hN : 0 < N) :
    LSeries (fun n => (vonMangoldt n : ℂ)) s =
      (∑ n ∈ Finset.Icc 1 (N - 1), (vonMangoldt n : ℂ) / (n : ℂ) ^ s) -
      ((∑ n ∈ Finset.Icc 1 (N - 1), vonMangoldt n : ℝ) : ℂ) / (N : ℂ) ^ s +
      s * ∫ y in Set.Ioi (N : ℝ), (Chebyshev.psi y : ℂ) / (y : ℂ) ^ (s + 1) := by
  have hi1 := (Decomp358a.psi_kernel_integrable s hs 1 (by norm_num)).1
  have hiN := (Decomp358a.psi_kernel_integrable s hs N hN).1
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi1 hiN
  norm_num only [Nat.cast_one] at hsplit
  rw [psi_mellin s hs, ← hsplit, mul_add, finite_cutoff s hs N hN]

/-- P0075 page 3 equation 2.1, exact Decomp272c Backlund identity.
This replacement has no cited quantitative input and no OPEN leaf. -/
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
  have hi := Decomp358a.psi_kernel_integrable s hs N hN0
  have hsub : IntegrableOn
      (fun y : ℝ => ((Chebyshev.psi y - y : ℝ) : ℂ) / (y : ℂ) ^ (s + 1))
      (Set.Ioi (N : ℝ)) := by
    convert hi.1.sub hi.2 using 1
    ext y
    simp only [Complex.ofReal_sub, sub_div, Pi.sub_apply]
  refine ⟨hsub, ?_⟩
  have hds := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hp := mangoldt_partial_summation s hs N hN0
  have hl := Decomp358a.linear_kernel_integral s hs (N : ℝ) (by positivity)
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


end LeanLab.ChirreHagen2025.Decomp377b
