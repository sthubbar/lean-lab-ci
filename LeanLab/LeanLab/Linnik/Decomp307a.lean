/-
Gallagher 1970 pp.333 to 335, Theorem 5 displays 20 to 23.
The arithmetic series, localization and calculus are separate obligations.
AI wrote the Lean code. Codex task307. Goldbach is open.
Source https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0011/LOG_0035.pdf
-/
import LeanLab.Linnik.Decomp1532b
-- ONE IMPORT EXCEPTION: closes Decomp307a.poisson_series_detector_of_turan from the proved
-- LeanLab.Linnik.Decomp335a.poisson_series_detector_of_turan (statement byte-identical).
-- Decomp335a and its only new dependency Decomp335c have 0 sorry; no cycle.
import LeanLab.Linnik.Decomp335a

open Finset MeasureTheory Complex
open scoped Classical
open LeanLab.Linnik.Decomp1532b LeanLab.Linnik.Decomp1532b2

namespace LeanLab.Linnik.Decomp307a

/-- Gallagher p.335 the smoothing kernel is smooth on the real line. -/
theorem contDiff_poissonKernel (k : ℕ) : ContDiff ℝ 2 (Decomp1532b2.poissonKernel k) := by
  unfold Decomp1532b2.poissonKernel
  fun_prop

/-- Gallagher p.335 chain rule for the logarithmic smoothing kernel. -/
theorem poisson_log_hasDerivAt (k : ℕ) (r : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => (Decomp1532b2.poissonKernel k (r * Real.log u) : ℂ))
      ((deriv (Decomp1532b2.poissonKernel k) (r * Real.log t) * (r / t) : ℝ) : ℂ) t := by
  have hk : DifferentiableAt ℝ (Decomp1532b2.poissonKernel k) (r * Real.log t) :=
    ((contDiff_poissonKernel k).differentiable (by norm_num)).differentiableAt
  convert (hk.hasDerivAt.comp t ((Real.hasDerivAt_log ht.ne').const_mul r)).ofReal_comp using 1 <;> congr 1

/-- Gallagher p.335 the logarithmic smoothing derivative is bounded by r over t. -/
theorem norm_deriv_poisson_log_le (k : ℕ) {r t : ℝ} (hr : 0 ≤ r) (ht : 1 ≤ t) :
    ‖deriv (fun u : ℝ => (Decomp1532b2.poissonKernel k (r * Real.log u) : ℂ)) t‖ ≤ r / t := by
  have ht0 : 0 < t := by linarith
  rw [(poisson_log_hasDerivAt k r ht0).deriv, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (div_nonneg hr ht0.le)]
  simpa using mul_le_mul_of_nonneg_right
    (abs_deriv_poissonKernel_le_one k (mul_nonneg hr (Real.log_nonneg ht)))
    (div_nonneg hr ht0.le)

/-- Gallagher p.335 integrability of the smoothing derivative on a positive interval. -/
theorem integrableOn_deriv_poisson_log (k : ℕ) (r : ℝ) {x y : ℝ} (hx : 0 < x) :
    IntegrableOn (deriv (fun u : ℝ => (Decomp1532b2.poissonKernel k (r * Real.log u) : ℂ)))
      (Set.Icc x y) := by
  have hl : ContDiffOn ℝ 2 Real.log (Set.Ioi 0) :=
    Real.contDiffOn_log.mono (by intro t ht; simpa using ht.ne')
  have hp : ContDiffOn ℝ 2 (fun u : ℝ => Decomp1532b2.poissonKernel k (r * Real.log u)) (Set.Ioi 0) :=
    (contDiff_poissonKernel k).comp_contDiffOn (contDiffOn_const.mul hl)
  have hc : ContDiffOn ℝ 2 (fun u : ℝ => (Decomp1532b2.poissonKernel k (r * Real.log u) : ℂ)) (Set.Ioi 0) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hp
  exact ((hc.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono
    (by intro t ht; exact hx.trans_le ht.1)).integrableOn_Icc

/-- Gallagher p.335 the supported partial sum norm divided by height is integrable. -/
theorem integrableOn_partial_sum_norm_div (a : ℕ → ℂ) {x y : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => ‖∑ n ∈ Icc 0 ⌊t⌋₊, a n‖ / t) (Set.Icc x y) := by
  have hi : IntegrableOn (fun t : ℝ => ((1 / t : ℝ) : ℂ)) (Set.Icc x y) := by
    exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.div continuousOn_id (by intro t ht; exact (hx.trans_le ht.1).ne'))).integrableOn_Icc
  have hh : IntegrableOn (fun t : ℝ => ‖((1 / t : ℝ) : ℂ) * ∑ n ∈ Icc 0 ⌊t⌋₊, a n‖)
      (Set.Icc x y) := (integrableOn_mul_sum_Icc (m := 0) a hx.le hi).norm
  apply hh.congr_fun _ measurableSet_Icc
  intro t ht
  dsimp only
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (hx.trans_le ht.1))]
  ring

/-- Gallagher p.335 partial summation with its endpoint term retained.
This calculus statement has no zero or character hypothesis. -/
theorem poisson_partial_summation_bound (a : ℕ → ℂ) (k : ℕ) {r x y : ℝ}
    (hr : 0 ≤ r) (hx : 1 ≤ x) (hxy : x ≤ y)
    (ha : ∀ n ≤ ⌊x⌋₊, a n = 0) :
    ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) * a n‖ -
        Decomp1532b2.poissonKernel k (r * Real.log y) * ‖∑ n ∈ Icc 0 ⌊y⌋₊, a n‖ ≤
      r * ∫ t in x..y, ‖∑ n ∈ Icc 0 ⌊t⌋₊, a n‖ / t := by
  have hx0 : 0 < x := by linarith
  have hh := detector_partial_summation_lower a
    (fun t : ℝ => (Decomp1532b2.poissonKernel k (r * Real.log t) : ℂ)) hx0 hxy ha
    (fun t ht => (poisson_log_hasDerivAt k r (hx0.trans_le ht.1)).differentiableAt)
    (integrableOn_deriv_poisson_log k r hx0)
    (show ‖(Decomp1532b2.poissonKernel k (r * Real.log y) : ℂ)‖ ≤ Decomp1532b2.poissonKernel k (r * Real.log y) by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
        (poissonKernel_nonneg k (mul_nonneg hr (Real.log_nonneg (hx.trans hxy))))])
    (fun t ht => norm_deriv_poisson_log_le k hr (hx.trans ht.1.le))
    ((integrableOn_partial_sum_norm_div a hx0).mono_set Set.Ioc_subset_Icc_self)
    (le_refl _)
  rw [intervalIntegral.integral_of_le hxy]
  linarith

/-- Gallagher p.333 the prime coefficients extended by zero below the window. -/
noncomputable def primeWindowCoefficient {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x v : ℝ) (n : ℕ) : ℂ :=
  if ⌊x⌋₊ < n ∧ n.Prime then
    (Real.log n / (n : ℝ) : ℂ) * χ n * Complex.exp (-((Real.log n * v : ℝ) : ℂ) * I)
  else 0

/-- Gallagher p.333 the supported coefficient sum is exactly the prime detector. -/
theorem sum_primeWindowCoefficient {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x y v : ℝ) :
    (∑ n ∈ Icc 0 ⌊y⌋₊, primeWindowCoefficient χ x v n) = primeDetector χ x y v := by
  classical
  unfold primeWindowCoefficient primeDetector
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨⟨hl, hu⟩, hn, hp⟩
    exact ⟨⟨hn, hu⟩, hp⟩
  · rintro ⟨⟨hn, hu⟩, hp⟩
    exact ⟨⟨by omega, hu⟩, hn, hp⟩

/-- Gallagher p.335 the full von Mangoldt reciprocal mass has logarithmic size. -/
theorem mangoldt_reciprocal_sum_le_log : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
    (∑ n ∈ Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) ≤ Real.log x + C := by
  obtain ⟨C, hC, htail⟩ := prime_power_reciprocal_tail
  refine ⟨C + 7, by positivity, ?_⟩
  have hnat (N : ℕ) (hN : 1 ≤ N) :
      (∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) ≤ Real.log N + (C + 7) := by
    have hp : (∑ n ∈ (Icc 1 N).filter Nat.Prime,
        ArithmeticFunction.vonMangoldt n / (n : ℝ)) = LeanLab.PNTSieve.Mertens.C N := by
      simp only [sum_filter, LeanLab.PNTSieve.Mertens.C, LeanLab.PNTSieve.Mertens.c]
      apply sum_congr rfl
      intro n hn
      by_cases hnp : n.Prime <;> simp [hnp, ArithmeticFunction.vonMangoldt_apply_prime]
    have hn : (∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime),
        ArithmeticFunction.vonMangoldt n / (n : ℝ)) =
        ∑ n ∈ (Ioc 1 N).filter (fun n => ¬n.Prime), ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
      symm
      apply sum_subset
      · intro n hn
        obtain ⟨hn, hnp⟩ := mem_filter.mp hn
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Ioc.mp hn).1.le, (mem_Ioc.mp hn).2⟩, hnp⟩
      · intro n hn hnot
        obtain ⟨hn, hnp⟩ := mem_filter.mp hn
        have hnlo : 1 ≤ n := (mem_Icc.mp hn).1
        have hn1 : n = 1 := by
          by_contra hne
          exact hnot (mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, (mem_Icc.mp hn).2⟩, hnp⟩)
        subst n
        simp
    have ht := htail 1 (N : ℝ) (by norm_num) (by exact_mod_cast hN)
    norm_num only [Nat.floor_one, Nat.floor_natCast, Real.sqrt_one, div_one] at ht
    rw [← sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime
      (fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ)), hp, hn]
    linarith [LeanLab.PNTSieve.Mertens.C_le N hN]
  intro x hx
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff _).mpr hx
  have hlog : Real.log ⌊x⌋₊ ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊x⌋₊)) (Nat.floor_le (by linarith))
  exact (hnat ⌊x⌋₊ hN).trans (by linarith)

/-- Gallagher p.335 the finite small Poisson tail, with a von Mangoldt majorant. -/
theorem poisson_small_cutoff_norm : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : ℝ, 0 < D →
    ∃ B₁ : ℝ, 0 < B₁ ∧ ∀ (a : ℕ → ℂ) (k : ℕ) (r x : ℝ),
      0 ≤ r → 1 ≤ x → r * Real.log x ≤ B₁ * k →
      (∀ n ∈ Icc 1 ⌊x⌋₊, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ)) →
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, a n * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)‖ ≤
        (1 / (2 * D)) ^ k * (Real.log x + C) := by
  obtain ⟨C, hC, hmass⟩ := mangoldt_reciprocal_sum_le_log
  refine ⟨C, hC, ?_⟩
  intro D hD
  obtain ⟨B₁, hB₁, htail⟩ := poissonKernel_small_tail D hD
  refine ⟨B₁, hB₁, ?_⟩
  intro a k r x hr hx hscale ha
  calc
    _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊,
        ‖a n * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt n / (n : ℝ)) * (1 / (2 * D)) ^ k := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hnx : (n : ℝ) ≤ x :=
        (show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast (mem_Icc.mp hn).2).trans
          (Nat.floor_le (by linarith))
      have hu : 0 ≤ r * Real.log n := mul_nonneg hr (Real.log_natCast_nonneg n)
      have hscale' : r * Real.log n ≤ B₁ * k :=
        (mul_le_mul_of_nonneg_left (Real.log_le_log hn0 hnx) hr).trans hscale
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (poissonKernel_nonneg k hu)]
      exact mul_le_mul (ha n hn) (htail k _ hu hscale') (poissonKernel_nonneg k hu)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
    _ = (1 / (2 * D)) ^ k *
        ∑ n ∈ Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hmass x hx) (by positivity)

/-- Gallagher p.335 the positive real Dirichlet series majorant for the upper tail. -/
theorem mangoldt_rpow_series_bound : ∃ A : ℝ, 1 ≤ A ∧ ∀ d : ℝ, 0 < d → d < 1 →
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + d)) ∧
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + d)) ≤ 1 / d + A := by
  obtain ⟨A, hA, hbound⟩ := _root_.ShiftZeroBound
  refine ⟨A, hA, ?_⟩
  intro d hd hd1
  have hs : 1 < ((1 + d : ℝ) : ℂ).re := by simp; linarith
  have hm := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have he (n : ℕ) :
      (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((1 + d : ℝ) : ℂ) n).re =
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + d) := by
    by_cases hn : n = 0
    · subst n
      simp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hcp : (n : ℂ) ^ ((1 + d : ℝ) : ℂ) = (((n : ℝ) ^ (1 + d) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
    rw [LSeries.term_of_ne_zero hn, hcp, ← Complex.ofReal_div, Complex.ofReal_re]
  have hsum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + d)) :=
    (Complex.reCLM.summable hm).congr he
  refine ⟨hsum, ?_⟩
  have ht : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + d)) =
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((1 + d : ℝ) : ℂ)).re := by
    rw [LSeries, Complex.re_tsum hm]
    exact tsum_congr (fun n => (he n).symm)
  rw [ht, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  simpa only [Complex.ofReal_add, Complex.ofReal_one, neg_div, neg_re] using hbound d ⟨hd, hd1⟩

/-- Gallagher p.335 the infinite upper Poisson tail, with absolute convergence. -/
theorem poisson_large_cutoff_norm : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : ℝ, 0 < D →
    ∃ B₂ : ℝ, 0 < B₂ ∧ ∀ (a : ℕ → ℂ) (k : ℕ) (r x : ℝ),
      0 < r → r ≤ 1 → 1 ≤ x → B₂ * k ≤ r * Real.log x →
      (∀ n : ℕ, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ)) →
      Summable (fun n : ℕ => if x < (n : ℝ) then
        a n * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) else 0) ∧
      ‖∑' n : ℕ, if x < (n : ℝ) then
        a n * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) else 0‖ ≤
        (1 / (2 * D)) ^ k * ((C : ℝ) / r) := by
  obtain ⟨A, hA, hseries⟩ := mangoldt_rpow_series_bound
  have hA0 : 0 ≤ A := by linarith
  refine ⟨A + 2, by positivity, ?_⟩
  intro D hD
  obtain ⟨B₂, hB₂, htail⟩ := poissonKernel_large_tail D hD
  refine ⟨B₂, hB₂, ?_⟩
  intro a k r x hr hr1 hx hscale ha
  obtain ⟨hsum, hmass⟩ := hseries (r / 2) (by positivity) (by linarith)
  have hmass' : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r / 2)) ≤
      (A + 2) / r := by
    have he : 1 / (r / 2) = 2 / r := by ring
    rw [he] at hmass
    apply hmass.trans
    apply (le_div_iff₀ hr).mpr
    rw [add_mul, div_mul_cancel₀ _ hr.ne']
    nlinarith [mul_le_mul_of_nonneg_left hr1 hA0]
  let b : ℕ → ℝ := fun n => (1 / (2 * D)) ^ k *
    (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r / 2))
  have hb : Summable b := hsum.mul_left _
  have hnorm (n : ℕ) : ‖if x < (n : ℝ) then
      a n * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) else 0‖ ≤ b n := by
    dsimp only [b]
    split_ifs with hnx
    · have hn0 : (0 : ℝ) < n := by linarith
      have hu : 0 ≤ r * Real.log n := mul_nonneg hr.le (Real.log_nonneg (by linarith))
      have hscale' : B₂ * k ≤ r * Real.log n :=
        hscale.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hnx.le) hr.le)
      have he : (ArithmeticFunction.vonMangoldt n / (n : ℝ)) * Real.exp (-(r * Real.log n) / 2) =
          ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r / 2) := by
        rw [Real.rpow_add hn0, Real.rpow_one, Real.rpow_def_of_pos hn0]
        rw [show -(r * Real.log n) / 2 = -(Real.log n * (r / 2)) by ring, Real.exp_neg]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (poissonKernel_nonneg k hu)]
      calc
        _ ≤ (ArithmeticFunction.vonMangoldt n / (n : ℝ)) *
            ((1 / (2 * D)) ^ k * Real.exp (-(r * Real.log n) / 2)) :=
          mul_le_mul (ha n) (htail k _ hu hscale') (poissonKernel_nonneg k hu)
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
        _ = _ := by rw [mul_left_comm, he]
    · rw [norm_zero]
      positivity
  have hf := hb.of_norm_bounded hnorm
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, b n := (norm_tsum_le_tsum_norm hf.norm).trans (hf.norm.tsum_le_tsum hnorm hb)
    _ = (1 / (2 * D)) ^ k *
        ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r / 2) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass' (by positivity)

/-- Gallagher p.334 principal Euler factors add no zeros in the positive half plane. -/
theorem principal_zero_iff_zeta (q : ℕ) [NeZero q] {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (1 : DirichletCharacter ℂ q).LFunction s = 0 ↔ riemannZeta s = 0 := by
  change DirichletCharacter.LFunctionTrivChar q s = 0 ↔ _
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1]
  have hprod : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    intro he
    have hpone : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp he).symm
    rw [hpone, norm_one] at hlt
    exact (lt_irrefl (1 : ℝ)) hlt
  simp only [mul_eq_zero, hprod, false_or]

/-- LEAF. Gallagher 1970 p.334 display 22, following display 21.
The full arithmetic Poisson series is large at an order in a prescribed dyadic range.
This includes the principal Euler factors and the uniform height parameter.
There is no prime window or integration assertion in this leaf. -/
theorem poisson_series_detector_of_turan
    (hpower : ∀ n M : ℕ, 0 < n → n ≤ M → ∀ z : Fin n → ℂ, (∃ i, 1 ≤ ‖z i‖) →
      ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖∑ i, z i ^ ν‖) :
    ∃ r₀ E D η : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ E ∧ 1 ≤ D ∧ 0 < η ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ M : ℕ, E * r * Real.log T ≤ M →
          ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
            η / (D ^ k * r) ≤
              ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
                (n : ℂ) ^ (1 + I * v)) * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)‖ := by
  exact LeanLab.Linnik.Decomp335a.poisson_series_detector_of_turan hpower

set_option maxHeartbeats 4000000

/-- The `n`-th factor `χ n · n^{-I v}` has norm at most one, so the prime power removal applies. -/
theorem norm_chi_cpow_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (v : ℝ) (n : ℕ) :
    ‖χ n * (n : ℂ) ^ (-(I * v))‖ ≤ 1 := by
  have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
  have hn : ‖(n : ℂ) ^ (-(I * v))‖ ≤ 1 := by
    rcases eq_or_ne n 0 with h | h
    · subst h
      by_cases hv : v = 0
      · subst hv; simp
      · have hz : (-(I * (v : ℂ))) ≠ 0 := by
          simp [Complex.ext_iff, hv]
        rw [Nat.cast_zero, Complex.zero_cpow hz]
        simp
    · have hpos : 0 < n := Nat.pos_of_ne_zero h
      rw [Complex.norm_natCast_cpow_of_pos hpos]
      simp
  rw [norm_mul]
  exact mul_le_one₀ hχ (norm_nonneg _) hn

/-- `n ^ (-(1 + I v)) = n ^ (-(I v)) / n`, the bridge between the leaf's series term and the
coefficient shape of `poisson_weighted_prime_power_removal`. -/
theorem cpow_neg_one_add {n : ℕ} (hn : n ≠ 0) (v : ℝ) :
    (n : ℂ) ^ (-(1 + I * v)) = (n : ℂ) ^ (-(I * v)) / (n : ℂ) := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have h1 : (-(1 + I * v) : ℂ) = (-(I * v)) + (-1) := by
    push_cast
    ring
  rw [h1, Complex.cpow_add _ _ hnc, Complex.cpow_neg_one, div_eq_mul_inv]

/-- The leaf's series term, written with the coefficient `χ n · n^{-I v}` that the prime power
removal of `Decomp1532b2` consumes. -/
theorem seriesTerm_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (v r : ℝ) (k : ℕ) {n : ℕ}
    (hn : n ≠ 0) :
    (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * v)) *
        (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)
      = (χ n * (n : ℂ) ^ (-(I * v))) *
        (((ArithmeticFunction.vonMangoldt n / (n : ℝ)) *
          Decomp1532b2.poissonKernel k (r * Real.log n) : ℝ) : ℂ) := by
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [div_eq_mul_inv, ← Complex.cpow_neg, cpow_neg_one_add hn v]
  push_cast
  field_simp

/-- The full Poisson series of the leaf is summable, given the tail bound. -/
theorem summable_series {q : ℕ} (χ : DirichletCharacter ℂ q) (v r : ℝ) (k : ℕ)
    {x' : ℝ} (hx' : 1 ≤ x')
    (htail : Summable (fun n : ℕ => if x' < (n : ℝ) then
      (χ n * (n : ℂ) ^ (-(I * v))) *
        (((ArithmeticFunction.vonMangoldt n / (n : ℝ)) *
          Decomp1532b2.poissonKernel k (r * Real.log n) : ℝ) : ℂ) else 0)) :
    Summable (fun n : ℕ => (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * v)) *
      (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)) := by
  let F : ℕ → ℂ := fun n =>
    (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * v)) *
      (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)
  let G : ℕ → ℂ := fun n => if x' < (n : ℝ) then
      (χ n * (n : ℂ) ^ (-(I * v))) *
        (((ArithmeticFunction.vonMangoldt n / (n : ℝ)) *
          Decomp1532b2.poissonKernel k (r * Real.log n) : ℝ) : ℂ) else 0
  have htail' : Summable G := htail
  have hgs : Summable (fun n : ℕ => G (n + (⌊x'⌋₊ + 1))) :=
    (summable_nat_add_iff _).mpr htail'
  have hfs : Summable (fun n : ℕ => F (n + (⌊x'⌋₊ + 1))) := by
    refine hgs.congr (fun n => ?_)
    have hne : n + (⌊x'⌋₊ + 1) ≠ 0 := by omega
    have hlt : x' < ((n + (⌊x'⌋₊ + 1) : ℕ) : ℝ) := by
      have h1 : x' < (⌊x'⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x'
      have h2 : (⌊x'⌋₊ : ℝ) + 1 ≤ ((n + (⌊x'⌋₊ + 1) : ℕ) : ℝ) := by
        push_cast
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    show G (n + (⌊x'⌋₊ + 1)) = F (n + (⌊x'⌋₊ + 1))
    dsimp only [G, F]
    rw [if_pos hlt, seriesTerm_eq χ v r k hne]
  exact (summable_nat_add_iff _).mp hfs

/-- The three way split of the leaf's full series: below `⌊x⌋`, the window, and above `⌊y⌋`. -/
theorem tsum_three_split {q : ℕ} (χ : DirichletCharacter ℂ q) (v r : ℝ) (k : ℕ)
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    ∀ (F : ℕ → ℂ),
      (∀ n : ℕ, F n = (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
          (n : ℂ) ^ (1 + I * v)) *
          (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)) →
      Summable F →
      (∑' n : ℕ, F n)
        = (∑ n ∈ Icc 0 ⌊x⌋₊, F n) + (∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, F n)
          + ∑' n : ℕ, (if ⌊y⌋₊ < n then F n else 0) := by
  have hfy : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  intro F hF hsum
  have hh : Summable (fun n : ℕ => if n ≤ ⌊y⌋₊ then F n else 0) :=
    summable_of_ne_finset_zero (s := Icc 0 ⌊y⌋₊) (fun b hb => by
      rw [if_neg]
      intro hle
      exact hb (mem_Icc.mpr ⟨Nat.zero_le b, hle⟩))
  have hfg : F = fun n => (if n ≤ ⌊y⌋₊ then F n else 0)
      + (if ⌊y⌋₊ < n then F n else 0) := by
    funext n
    by_cases h : n ≤ ⌊y⌋₊
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  have hg : Summable (fun n : ℕ => if ⌊y⌋₊ < n then F n else 0) := by
    refine (hsum.sub hh).congr (fun n => ?_)
    show F n - (if n ≤ ⌊y⌋₊ then F n else 0) = (if ⌊y⌋₊ < n then F n else 0)
    by_cases h : n ≤ ⌊y⌋₊
    · rw [if_pos h, if_neg (by omega), sub_self]
    · rw [if_neg h, if_pos (by omega), sub_zero]
  have htsum : (∑' n : ℕ, (if n ≤ ⌊y⌋₊ then F n else 0)) = ∑ n ∈ Icc 0 ⌊y⌋₊, F n := by
    rw [tsum_eq_sum (s := Icc 0 ⌊y⌋₊)]
    · apply sum_congr rfl
      intro b hb
      rw [if_pos (mem_Icc.mp hb).2]
    · intro b hb
      rw [if_neg]
      intro hle
      exact hb (mem_Icc.mpr ⟨Nat.zero_le b, hle⟩)
  have hset : Icc 0 ⌊y⌋₊ = Icc 0 ⌊x⌋₊ ∪ Ioc ⌊x⌋₊ ⌊y⌋₊ := by
    ext n
    simp only [mem_Icc, mem_Ioc, mem_union]
    omega
  have hdisj : Disjoint (Icc 0 ⌊x⌋₊) (Ioc ⌊x⌋₊ ⌊y⌋₊) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [mem_Icc] at ha
    simp only [mem_Ioc] at hb
    omega
  have hset' : (∑ n ∈ Icc 0 ⌊y⌋₊, F n)
      = (∑ n ∈ Icc 0 ⌊x⌋₊, F n) + (∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, F n) := by
    rw [hset, sum_union hdisj]
  conv_lhs => rw [hfg]
  rw [Summable.tsum_add hh hg, htsum, hset']

/-- The prime detector has at most logarithmic mass. -/
theorem detector_norm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (x y v : ℝ), 1 ≤ x → x ≤ y →
      ‖primeDetector χ x y v‖ ≤ Real.log y + C := by
  obtain ⟨C, hC, hmass⟩ := mangoldt_reciprocal_sum_le_log
  refine ⟨C, hC, fun q χ x y v hx hxy => ?_⟩
  have hx1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hsub : (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime ⊆ Icc 1 ⌊y⌋₊ := by
    intro n hn
    obtain ⟨hnw, hnp⟩ := mem_filter.mp hn
    exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hnw).1; omega, (mem_Ioc.mp hnw).2⟩
  unfold primeDetector
  calc ‖∑ p ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
        (Real.log p / (p : ℝ) : ℂ) * χ p * Complex.exp (-((Real.log p * v : ℝ) : ℂ) * I)‖
      ≤ ∑ p ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
          ‖(Real.log p / (p : ℝ) : ℂ) * χ p * Complex.exp (-((Real.log p * v : ℝ) : ℂ) * I)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
          ArithmeticFunction.vonMangoldt p / (p : ℝ) := by
        apply sum_le_sum
        intro p hp
        have hpp : Nat.Prime p := (mem_filter.mp hp).2
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        have hlog : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
        rw [norm_mul, norm_mul, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hlog hp0.le), ArithmeticFunction.vonMangoldt_apply_prime hpp]
        have hre : (-((Real.log p * v : ℝ) : ℂ) * I).re = 0 := by
          rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]
          ring
        have hexp : ‖Complex.exp (-((Real.log p * v : ℝ) : ℂ) * I)‖ = 1 := by
          rw [Complex.norm_exp, hre, Real.exp_zero]
        rw [hexp, mul_one]
        calc Real.log ↑p / ↑p * ‖χ p‖ ≤ Real.log ↑p / ↑p * 1 := by
              exact mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one χ (p : ZMod q))
                (div_nonneg hlog hp0.le)
          _ = Real.log ↑p / ↑p := mul_one _
    _ ≤ ∑ n ∈ Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi1 hi2 => ?_)
        exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg i)
    _ ≤ Real.log y + C := hmass y (by linarith)

/-- The window sum of `primeWindowCoefficient` is the prime detector. -/
theorem sum_windowCoefficient {q : ℕ} (χ : DirichletCharacter ℂ q) (x y v : ℝ) :
    (∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, primeWindowCoefficient χ x v n) = primeDetector χ x y v := by
  classical
  unfold primeDetector
  rw [sum_filter]
  apply sum_congr rfl
  intro n hn
  have hlt : ⌊x⌋₊ < n := (mem_Ioc.mp hn).1
  by_cases hnp : n.Prime
  · simp [primeWindowCoefficient, hlt, hnp]
  · simp [primeWindowCoefficient, hnp]

/-- Absorption: for `k ≥ t / B₁` the kernel decay `(1/2)^k` beats any linear growth `t + S`,
uniformly for `t` past an explicit threshold. No smallness of `B₁` is needed. -/
theorem absorption {η B1 S : ℝ} (hη : 0 < η) (hB1 : 0 < B1) (hS : 0 ≤ S) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ t : ℝ, A ≤ t → ∀ k : ℕ, t ≤ B1 * k →
      (1 / 2 : ℝ) ^ k * (t + S) ≤ η / 8 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2h : (1 / 2 : ℝ) ≤ Real.log 2 := by nlinarith [Real.log_two_gt_d9]
  refine ⟨16 + 16 * S + 4 * Real.sqrt S + 128 * B1 ^ 2 + 8 * B1 * Real.sqrt S +
      max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) + 1, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ 16 * S := by linarith
    have h2 : (0:ℝ) ≤ 4 * Real.sqrt S := by positivity
    have h3 : (0:ℝ) ≤ 128 * B1 ^ 2 := by positivity
    have h4 : (0:ℝ) ≤ 8 * B1 * Real.sqrt S := by positivity
    have h5 : (0:ℝ) ≤ max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) := le_max_left _ _
    linarith
  intro t ht k hk
  have hA1 : 8 ≤ t := by
    have h1 : (0:ℝ) ≤ 16 * S := by linarith
    have h2 : (0:ℝ) ≤ 4 * Real.sqrt S := by positivity
    have h3 : (0:ℝ) ≤ 128 * B1 ^ 2 := by positivity
    have h4 : (0:ℝ) ≤ 8 * B1 * Real.sqrt S := by positivity
    have h5 : (0:ℝ) ≤ max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) := le_max_left _ _
    linarith
  have hAS : 16 * S ≤ t := by
    have h2 : (0:ℝ) ≤ 4 * Real.sqrt S := by positivity
    have h3 : (0:ℝ) ≤ 128 * B1 ^ 2 := by positivity
    have h4 : (0:ℝ) ≤ 8 * B1 * Real.sqrt S := by positivity
    have h5 : (0:ℝ) ≤ max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) := le_max_left _ _
    linarith
  have hAsqrt : 4 * Real.sqrt S ≤ t := by
    have h1 : (0:ℝ) ≤ 16 * S := by linarith
    have h3 : (0:ℝ) ≤ 128 * B1 ^ 2 := by positivity
    have h4 : (0:ℝ) ≤ 8 * B1 * Real.sqrt S := by positivity
    have h5 : (0:ℝ) ≤ max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) := le_max_left _ _
    linarith
  have hAB1 : 128 * B1 ^ 2 ≤ t := by
    have h1 : (0:ℝ) ≤ 16 * S := by linarith
    have h2 : (0:ℝ) ≤ 4 * Real.sqrt S := by positivity
    have h4 : (0:ℝ) ≤ 8 * B1 * Real.sqrt S := by positivity
    have h5 : (0:ℝ) ≤ max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) := le_max_left _ _
    linarith
  have hAB1S : 8 * B1 * Real.sqrt S ≤ t := by
    have h1 : (0:ℝ) ≤ 16 * S := by linarith
    have h2 : (0:ℝ) ≤ 4 * Real.sqrt S := by positivity
    have h3 : (0:ℝ) ≤ 128 * B1 ^ 2 := by positivity
    have h5 : (0:ℝ) ≤ max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) := le_max_left _ _
    linarith
  have hAlog : 2 * Real.log (8 / η) * B1 / Real.log 2 ≤ t := by
    have h1 : (0:ℝ) ≤ 16 * S := by linarith
    have h2 : (0:ℝ) ≤ 4 * Real.sqrt S := by positivity
    have h3 : (0:ℝ) ≤ 128 * B1 ^ 2 := by positivity
    have h4 : (0:ℝ) ≤ 8 * B1 * Real.sqrt S := by positivity
    have h5 : 2 * Real.log (8 / η) * B1 / Real.log 2 ≤
        max 0 (2 * Real.log (8 / η) * B1 / Real.log 2) := le_max_right _ _
    linarith
  have hpow : (1 / 2 : ℝ) ^ k = Real.exp (-((k : ℝ) * Real.log 2)) := by
    have h1 : (1 / 2 : ℝ) = Real.exp (Real.log (1 / 2)) := (Real.exp_log (by norm_num)).symm
    rw [h1, ← Real.exp_nat_mul]
    congr 1
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    push_cast
    ring
  have hkB : t / B1 ≤ (k : ℝ) := by
    rw [div_le_iff₀ hB1]
    simpa [mul_comm] using hk
  have hexp : Real.exp (-((k : ℝ) * Real.log 2)) ≤ Real.exp (-(t / B1 * Real.log 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [hpow]
  refine le_trans (mul_le_mul_of_nonneg_right hexp (by linarith : (0:ℝ) ≤ t + S)) ?_
  have hsplit : Real.exp (-(t / B1 * Real.log 2)) * (t + S)
      = Real.exp (-(t / B1 * Real.log 2) / 2)
        * (Real.exp (-(t / B1 * Real.log 2) / 2) * (t + S)) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hsplit]
  have hc1 : Real.exp (-(t / B1 * Real.log 2) / 2) ≤ η / 8 := by
    rw [show η / 8 = Real.exp (Real.log (η / 8)) from (Real.exp_log (by positivity)).symm]
    apply Real.exp_le_exp.mpr
    have hb : Real.log (η / 8) = -Real.log (8 / η) := by
      rw [Real.log_div hη.ne' (by norm_num), Real.log_div (by norm_num) hη.ne']
      ring
    rw [hb]
    have hstep : t * (Real.log 2 / B1) ≥ 2 * Real.log (8 / η) := by
      have hpos : 0 < Real.log 2 / B1 := by positivity
      have heq : 2 * Real.log (8 / η) * B1 / Real.log 2 * (Real.log 2 / B1) =
          2 * Real.log (8 / η) := by
        field_simp
      calc 2 * Real.log (8 / η)
          = (2 * Real.log (8 / η) * B1 / Real.log 2) * (Real.log 2 / B1) := heq.symm
        _ ≤ t * (Real.log 2 / B1) := mul_le_mul_of_nonneg_right hAlog hpos.le
    have hrew : -(t / B1 * Real.log 2) / 2 = -(t * (Real.log 2 / B1)) / 2 := by
      field_simp
    rw [hrew]
    linarith
  have hc2 : Real.exp (-(t / B1 * Real.log 2) / 2) * (t + S) ≤ 1 := by
    have hcpos : 0 < Real.log 2 / B1 := by positivity
    have hquad : (t / B1 * Real.log 2 / 2) ^ 2 / 2 ≤ Real.exp (t / B1 * Real.log 2 / 2) := by
      have h := Real.pow_div_factorial_le_exp (t / B1 * Real.log 2 / 2) (by positivity) 2
      simpa using h
    have hbig : t + S ≤ (t / B1 * Real.log 2 / 2) ^ 2 / 2 := by
      -- `t ≤ c²t²/8` and `2S ≤ c²t²/8`, with `c = log2 / B1`
      have hconv : (t / B1 * Real.log 2 / 2) ^ 2 / 2 = (t * (Real.log 2 / B1)) ^ 2 / 8 := by
        field_simp
        ring
      rw [hconv]
      have hB1sq : B1 ^ 2 * (Real.log 2 / B1) ^ 2 = (Real.log 2) ^ 2 := by
        field_simp
      have hcoef : (0:ℝ) ≤ (Real.log 2 / B1) ^ 2 := by positivity
      have hct : 16 ≤ t * (Real.log 2 / B1) ^ 2 := by
        have h4 := mul_le_mul_of_nonneg_right hAB1 hcoef
        rw [mul_assoc, hB1sq] at h4
        have h5 : 4 * (Real.log 2) ^ 2 ≥ 1 := by nlinarith [hlog2h]
        nlinarith
      have hcS : 16 * S ≤ t ^ 2 * (Real.log 2 / B1) ^ 2 := by
        have h5 : 4 * Real.sqrt S ≤ t * (Real.log 2 / B1) := by
          have h9 : (0:ℝ) < Real.log 2 / B1 := hcpos
          have h11 : 8 * B1 * Real.sqrt S * (Real.log 2 / B1) ≤ t * (Real.log 2 / B1) :=
            mul_le_mul_of_nonneg_right hAB1S h9.le
          have h12 : 8 * B1 * Real.sqrt S * (Real.log 2 / B1) =
              8 * Real.sqrt S * Real.log 2 := by
            field_simp
          have h13 : 4 * Real.sqrt S ≤ 8 * Real.sqrt S * Real.log 2 := by
            have h14 : (0:ℝ) ≤ Real.sqrt S := Real.sqrt_nonneg S
            nlinarith [hlog2h]
          linarith
        have h9 : (0:ℝ) ≤ 4 * Real.sqrt S := by positivity
        have h11 : (4 * Real.sqrt S) ^ 2 ≤ (t * (Real.log 2 / B1)) ^ 2 :=
          pow_le_pow_left₀ h9 h5 2
        have h12 : (4 * Real.sqrt S) ^ 2 = 16 * S := by
          rw [mul_pow, Real.sq_sqrt hS]; norm_num
        rw [h12, mul_pow] at h11
        exact h11
      have htpos : (0:ℝ) < t := by linarith
      have hsq : t ^ 2 * (Real.log 2 / B1) ^ 2 = t * (t * (Real.log 2 / B1) ^ 2) := by ring
      have hgt : 8 * t ≤ t ^ 2 * (Real.log 2 / B1) ^ 2 := by
        rw [hsq]
        have := mul_le_mul_of_nonneg_left hct htpos.le
        linarith
      rw [mul_pow]
      nlinarith [hgt, hcS]
    have hexp3 : Real.exp (-(t / B1 * Real.log 2) / 2)
        = (Real.exp (t / B1 * Real.log 2 / 2))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [hexp3, inv_mul_le_iff₀ (Real.exp_pos _), mul_one]
    exact hbig.trans hquad
  exact le_trans (mul_le_mul hc1 hc2 (by positivity) (by positivity)) (by norm_num)

/-- The floor threshold and the real threshold agree at natural numbers. -/
theorem floor_lt_iff {y : ℝ} {n : ℕ} (hy : 0 ≤ y) : y < (n : ℝ) ↔ ⌊y⌋₊ < n := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have h1 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
    have h2 : (n : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hcon
    have h3 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
    linarith
  · intro h
    have h1 : (⌊y⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt h
    have h2 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
    linarith



/-! ## Numeric lemmas for the assembly

Each of these has a small goal on purpose: the previous pass died of elaboration cost when the
whole assembly's numeric goal was attacked at once. `set_option maxHeartbeats` is inherited from
the head of this file. -/

/-- The kernel decay `(1/2)^k` against `D ^ k` with a `1 / r` in the tail term. -/
theorem kernel_engine1 {D η r Z : ℝ} (hD : 0 < D) (hr : 0 < r) (hη : 0 < η) (k : ℕ)
    (h : (1 / 2 : ℝ) ^ k * Z ≤ η / 8) :
    (1 / (2 * D)) ^ k * (Z / r) ≤ η / (8 * (D ^ k * r)) := by
  have hb : (1:ℝ) / (2 * D) = (1 / 2) * (1 / D) := by field_simp
  have hZ : (0:ℝ) ≤ (1 / D) ^ k := by positivity
  have h1 : (1 / 2) ^ k * Z * r⁻¹ * (1 / D) ^ k ≤ η / 8 * r⁻¹ * (1 / D) ^ k := by
    apply mul_le_mul_of_nonneg_right _ hZ
    exact mul_le_mul_of_nonneg_right h (by positivity)
  have hgoal : (1 / (2 * D)) ^ k * (Z / r) = (1 / 2) ^ k * Z * r⁻¹ * (1 / D) ^ k := by
    rw [hb, mul_pow, div_eq_mul_inv]
    ring
  have h2 : η / 8 * r⁻¹ * (1 / D) ^ k = η / (8 * (D ^ k * r)) := by
    rw [one_div, inv_pow]
    field_simp
  rw [hgoal]
  exact h1.trans h2.le

/-- The kernel decay against `D ^ k` with no `1 / r` factor. -/
theorem kernel_engine2 {D η r Z : ℝ} (hD : 0 < D) (hr : 0 < r) (hr2 : r ≤ 2) (hη : 0 < η)
    (k : ℕ) (h : (1 / 2 : ℝ) ^ k * Z ≤ η / 16) :
    (1 / (2 * D)) ^ k * Z ≤ η / (8 * (D ^ k * r)) := by
  have hb : (1:ℝ) / (2 * D) = (1 / 2) * (1 / D) := by field_simp
  have hZ : (0:ℝ) ≤ (1 / D) ^ k := by positivity
  have h1 : (1 / 2) ^ k * Z * (1 / D) ^ k ≤ η / 16 * (1 / D) ^ k :=
    mul_le_mul_of_nonneg_right h hZ
  have hgoal : (1 / (2 * D)) ^ k * Z = (1 / 2) ^ k * Z * (1 / D) ^ k := by
    rw [hb, mul_pow]; ring
  have h2 : η / 16 * (1 / D) ^ k ≤ η / (8 * (D ^ k * r)) := by
    have h3 : η / 16 ≤ η / (8 * r) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    have h4 : η / 16 * (1 / D) ^ k ≤ η / (8 * r) * (1 / D) ^ k :=
      mul_le_mul_of_nonneg_right h3 hZ
    have h5 : η / (8 * r) * (1 / D) ^ k = η / (8 * (D ^ k * r)) := by
      rw [one_div, inv_pow]
      field_simp
    linarith
  rw [hgoal]
  exact h1.trans h2

/-- The kernel decay against `D ^ k` in the `1 / r` shape needed by the small part. -/
theorem kernel_engine3 {D η r Z : ℝ} (hD : 0 < D) (hr : 0 < r) (hη : 0 < η) (k : ℕ)
    (h : (1 / 2 : ℝ) ^ k * Z ≤ η / (8 * r)) :
    (1 / (2 * D)) ^ k * Z ≤ η / (8 * (D ^ k * r)) := by
  have hb : (1:ℝ) / (2 * D) = (1 / 2) * (1 / D) := by field_simp
  have hZ : (0:ℝ) ≤ (1 / D) ^ k := by positivity
  have h1 : (1 / 2) ^ k * Z * (1 / D) ^ k ≤ η / (8 * r) * (1 / D) ^ k :=
    mul_le_mul_of_nonneg_right h hZ
  have hgoal : (1 / (2 * D)) ^ k * Z = (1 / 2) ^ k * Z * (1 / D) ^ k := by
    rw [hb, mul_pow]; ring
  have h2 : η / (8 * r) * (1 / D) ^ k = η / (8 * (D ^ k * r)) := by
    rw [one_div, inv_pow]
    field_simp
  rw [hgoal]
  exact h1.trans h2.le

/-- `D ^ k` against an exponential once `k log D` is bounded. -/
theorem pow_le_exp_of_log {D : ℝ} (hD : 0 < D) (k : ℕ) {X : ℝ}
    (h : (k : ℝ) * Real.log D ≤ X) : D ^ k ≤ Real.exp X := by
  have h1 : D ^ k = Real.exp ((k : ℝ) * Real.log D) := by
    rw [Real.exp_nat_mul, Real.exp_log hD]
  rw [h1]
  exact Real.exp_le_exp.mpr h

/-- `t ^ 2` against the exponential once `t` is past `8` and the rate is at least one. -/
theorem sq_le_exp {Cc t : ℝ} (hCc : 1 ≤ Cc) (ht : 8 ≤ t) :
    t ^ 2 ≤ 32 * Real.exp (Cc * t / 2) := by
  have h1 : (0:ℝ) ≤ Cc * t / 2 := by nlinarith
  have h2 := Real.pow_div_factorial_le_exp (Cc * t / 2) h1 2
  have h3 : (0:ℝ) ≤ t := by linarith
  have h4 : t / 2 ≤ Cc * t / 2 := by nlinarith
  have h5 : (t / 2) ^ 2 / 2 ≤ (Cc * t / 2) ^ 2 / 2 := by
    have h6 : (0:ℝ) ≤ t / 2 := by linarith
    nlinarith
  have h7 : t ^ 2 ≤ 32 * ((t / 2) ^ 2 / 2) := by nlinarith
  have h8 : 32 * ((t / 2) ^ 2 / 2) ≤ 32 * ((Cc * t / 2) ^ 2 / 2) := by linarith
  linarith [h2, h7, h8]

/-- `k log D ≤ Cc t / 2`: the index bound `k ≤ 2 t (Mx + 1)` against `Cc`. -/
theorem k_logD_le {k t Ld Mx Cc logD : ℝ} (h : k ≤ 2 * t * (Mx + 1)) (ht : 1 ≤ t)
    (hlogD : logD ≤ Ld) (hlogD0 : 0 ≤ logD) (hLd0 : 0 ≤ Ld) (hMx1 : 1 ≤ Mx)
    (hCc : Cc = 8 * Ld * (Mx + 1) + 1) : k * logD ≤ Cc * t / 2 := by
  have h1 : k * logD ≤ (2 * t * (Mx + 1)) * Ld := by
    have h2 : (0:ℝ) ≤ logD := hlogD0
    have h3 : (0:ℝ) ≤ 2 * t * (Mx + 1) := by nlinarith
    nlinarith
  have h4 : Cc * t / 2 = (4 * Ld * (Mx + 1) + 1 / 2) * t := by
    rw [hCc]; ring
  have h5 : (0:ℝ) ≤ t := by linarith
  have h6 : (0:ℝ) ≤ Ld * (Mx + 1) := by positivity
  rw [h4]
  nlinarith

/-- `Lb * k ≤ Bc * t`: the large cutoff scale against `Bc`. -/
theorem lb_k_le {k t Lb Mx Bc : ℝ} (h : k ≤ 2 * t * (Mx + 1)) (ht : 1 ≤ t) (hLb0 : 0 ≤ Lb)
    (hMx1 : 1 ≤ Mx) (hBc : Bc = 16 + 32 * Lb * (Mx + 1)) : Lb * k ≤ Bc * t := by
  have h1 : (0:ℝ) ≤ t := by linarith
  have h2 : (0:ℝ) ≤ Lb * (Mx + 1) := by positivity
  rw [hBc]
  nlinarith

/-- The scaled final comparison: `e ^ (-(Cc t)) t ^ 2 D ^ k ≤ 32`. -/
theorem final_scaled {Cc t Dk : ℝ} (hDk : Dk ≤ Real.exp (Cc * t / 2))
    (ht2 : t ^ 2 ≤ 32 * Real.exp (Cc * t / 2)) :
    Real.exp (-(Cc * t)) * t ^ 2 * Dk ≤ 32 := by
  have h5 : (0:ℝ) ≤ Real.exp (-(Cc * t)) * t ^ 2 := by positivity
  have h4 : Real.exp (-(Cc * t)) * t ^ 2 * Dk ≤ Real.exp (-(Cc * t)) * t ^ 2 *
      Real.exp (Cc * t / 2) := mul_le_mul_of_nonneg_left hDk h5
  refine h4.trans ?_
  have heq : Real.exp (-(Cc * t)) * t ^ 2 * Real.exp (Cc * t / 2)
      = (Real.exp (-(Cc * t)) * Real.exp (Cc * t / 2)) * t ^ 2 := by ring
  rw [heq]
  have h2 : Real.exp (-(Cc * t)) * Real.exp (Cc * t / 2) = Real.exp (-(Cc * t / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h2]
  have h7 : (0:ℝ) ≤ Real.exp (-(Cc * t / 2)) := (Real.exp_pos _).le
  have h8 := mul_le_mul_of_nonneg_left ht2 h7
  have h9 : Real.exp (-(Cc * t / 2)) * (32 * Real.exp (Cc * t / 2)) = 32 := by
    have h10 : Real.exp (-(Cc * t / 2)) * Real.exp (Cc * t / 2) = 1 := by
      rw [← Real.exp_add]
      have h11 : -(Cc * t / 2) + Cc * t / 2 = 0 := by ring
      rw [h11, Real.exp_zero]
    calc Real.exp (-(Cc * t / 2)) * (32 * Real.exp (Cc * t / 2))
        = 32 * (Real.exp (-(Cc * t / 2)) * Real.exp (Cc * t / 2)) := by ring
      _ = 32 := by rw [h10]; ring
  linarith [h8, h9]

/-- The division step: the scaled comparison gives the leaf's target term. -/
theorem final_div {η Cc t Dk r c Lg xs : ℝ} (hη : 0 < η) (hr : 0 < r) (hcc : c = η / 64)
    (ht : t = r * Lg) (hxs : xs = Real.exp (-(Cc * t))) (hDk : 0 < Dk)
    (hscaled : Real.exp (-(Cc * t)) * t ^ 2 * Dk ≤ 32) :
    c * xs * Lg ^ 2 * r ≤ η / (2 * (Dk * r)) := by
  have h2 : Real.exp (-(Cc * t)) * t ^ 2 ≤ 32 / Dk := by
    rw [le_div_iff₀ hDk]
    linarith
  have h1 : η / 64 * Real.exp (-(Cc * t)) * Lg ^ 2 * r
      = η / 64 * (Real.exp (-(Cc * t)) * t ^ 2) / r := by
    rw [ht]
    field_simp
  rw [hcc, hxs, h1]
  have h4 : η / 64 * (Real.exp (-(Cc * t)) * t ^ 2) / r ≤ η / 64 * (32 / Dk) / r := by
    apply div_le_div_of_nonneg_right _ hr.le
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  refine h4.trans ?_
  field_simp
  norm_num

/-- The leaf's series term at a prime above the window threshold is the window coefficient. -/
theorem seriesTerm_eq_coefficient {q : ℕ} (χ : DirichletCharacter ℂ q) (x v r : ℝ) (k : ℕ)
    {n : ℕ} (hn : n.Prime) (hk : ⌊x⌋₊ < n) :
    (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * v)) *
        (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)
      = (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) * primeWindowCoefficient χ x v n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn.pos
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne_zero
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (le_of_lt hn0)]
  have hpow : (n : ℂ) ^ (1 + I * v) =
      (n : ℂ) * Complex.exp (((Real.log n * v : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_add _ _ hnc, Complex.cpow_one, Complex.cpow_def_of_ne_zero hnc, hlog]
    congr 2
    push_cast
    ring
  have hinv : (Complex.exp (((Real.log n * v : ℝ) : ℂ) * I))⁻¹ =
      Complex.exp (-(((Real.log n * v : ℝ) : ℂ) * I)) := by
    rw [← Complex.exp_neg]
  have hΛ : (ArithmeticFunction.vonMangoldt n : ℂ) = (Real.log n : ℂ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime hn]
  rw [hpow, hΛ, div_eq_mul_inv, mul_inv, hinv]
  unfold primeWindowCoefficient
  rw [if_pos ⟨hk, hn⟩]
  push_cast
  field_simp

/-- A norm lower bound for a difference. -/
theorem norm_sub_ge (a b : ℂ) : ‖a‖ - ‖b‖ ≤ ‖a - b‖ :=
  (le_abs_self (‖a‖ - ‖b‖)).trans (abs_norm_sub_norm_le a b)



/-- Lower bound for the fourth of four pieces from an additive decomposition. -/
theorem norm_three_lower (a b c d : ℂ) (h : a = b + c + d) : ‖a‖ - ‖b‖ - ‖c‖ ≤ ‖d‖ := by
  have h1 : d = a - b - c := by rw [h]; abel
  have h2 : ‖a - b - c‖ ≥ ‖a - b‖ - ‖c‖ := norm_sub_ge _ _
  have h3 : ‖a - b‖ ≥ ‖a‖ - ‖b‖ := norm_sub_ge _ _
  rw [h1]
  linarith

/-- The closing arithmetic of the leaf: nine comparisons give the target term. -/
theorem chain_arith {η Dk r X Lx C1 C2 C0 Bc C3 sq Sn An Pn Wn Wc Ep : ℝ}
    (hr : 0 < r) (hDk : 0 < Dk) (hsq : 0 < sq)
    (h1 : η / (Dk * r) ≤ Sn) (h2 : Sn - An - Pn ≤ Wn) (h3 : Wn - C3 / sq ≤ Wc)
    (h4 : An ≤ X * (Lx + C1)) (h5 : Pn ≤ X * (C2 / r)) (h6 : Ep ≤ X * (Bc * Lx + C0))
    (h7 : X * (Lx + C1) ≤ η / (8 * (Dk * r)))
    (h8 : X * (C2 / r) ≤ η / (8 * (Dk * r)))
    (h9 : X * (Bc * Lx + C0) ≤ η / (8 * (Dk * r)))
    (h10 : C3 / sq ≤ η / (8 * (Dk * r))) :
    η / (2 * (Dk * r)) ≤ Wc - Ep := by
  have hbr : η / (8 * (Dk * r)) = η / (Dk * r) / 8 := by
    field_simp
  rw [hbr] at h7 h8 h9 h10
  have h11 : η / (2 * (Dk * r)) = η / (Dk * r) / 2 := by
    field_simp
  rw [h11]
  linarith

/-- The small part: shifting the sum from `Icc 1` to `Icc 0` costs nothing when `A 0 = 0`. -/
theorem small_part_le {D x C1 : ℝ} {k : ℕ} (A : ℕ → ℂ) (K : ℕ → ℂ) (hA0 : A 0 = 0)
    (h : ‖∑ n ∈ Icc 1 ⌊x⌋₊, A n * K n‖ ≤ (1 / (2 * D)) ^ k * (Real.log x + C1)) :
    ‖∑ n ∈ Icc 0 ⌊x⌋₊, A n * K n‖ ≤ (1 / (2 * D)) ^ k * (Real.log x + C1) := by
  have hset : Icc 0 ⌊x⌋₊ = insert 0 (Icc 1 ⌊x⌋₊) := by
    ext n
    simp only [mem_Icc, mem_insert]
    omega
  rw [hset, sum_insert (by simp), hA0, zero_mul, zero_add]
  exact h

/-- The tail part: the floor and real thresholds agree, so the tail bound transfers. -/
theorem tail_part_le {D x C2 Bc r0 : ℝ} {k : ℕ} (A : ℕ → ℂ) (K : ℕ → ℂ)
    (hx : 0 ≤ x ^ Bc)
    (h : ‖∑' n : ℕ, (if x ^ Bc < (n : ℝ) then A n * K n else 0)‖ ≤
      (1 / (2 * D)) ^ k * (C2 / r0)) :
    ‖∑' n : ℕ, (if ⌊x ^ Bc⌋₊ < n then A n * K n else 0)‖ ≤
      (1 / (2 * D)) ^ k * (C2 / r0) := by
  have hiff : ∀ n : ℕ, (x ^ Bc < (n : ℝ)) ↔ (⌊x ^ Bc⌋₊ < n) := fun n => floor_lt_iff hx
  have hcongr : (∑' n : ℕ, (if ⌊x ^ Bc⌋₊ < n then A n * K n else 0))
      = ∑' n : ℕ, (if x ^ Bc < (n : ℝ) then A n * K n else 0) := by
    apply tsum_congr
    intro n
    by_cases hh : ⌊x ^ Bc⌋₊ < n
    · simp only [if_pos hh, if_pos ((hiff n).mpr hh)]
    · simp only [if_neg hh, if_neg (fun h2 => hh ((hiff n).mp h2))]
  rw [hcongr]
  exact h

/-- The von Mangoldt coefficient of the leaf's series is majorised by `Λ n / n`. -/
theorem norm_series_coef {q : ℕ} (χ : DirichletCharacter ℂ q) (v : ℝ) (n : ℕ) :
    ‖χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * v)‖ ≤
      ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
  rcases eq_or_ne n 0 with hh | hh
  · subst hh
    simp
  · have hpos : 0 < n := Nat.pos_of_ne_zero hh
    have hΛ : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hnorm : ‖(n : ℂ) ^ (1 + I * v)‖ = (n : ℝ) := by
      rw [Complex.norm_natCast_cpow_of_pos hpos]; simp
    have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
    have hn0 : (0:ℝ) < n := by exact_mod_cast hpos
    have h1 : ‖χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * v)‖
        = ‖χ n‖ * ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
      rw [norm_div, norm_mul, hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
    rw [h1]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_left hΛ hχ) hn0.le

/-- The endpoint kernel is below the `k`-th kernel decay once its argument is past `Bk k`. -/
theorem kernel_endpoint_le {D Bk r y : ℝ} (hD : 0 < D) (hBk : 0 < Bk)
    (htail : ∀ k : ℕ, ∀ u : ℝ, 0 ≤ u → Bk * k ≤ u →
      Decomp1532b2.poissonKernel k u ≤ (1 / (2 * D)) ^ k * Real.exp (-u / 2))
    {k : ℕ} (hy : 0 ≤ r * Real.log y) (h : Bk * k ≤ r * Real.log y) :
    Decomp1532b2.poissonKernel k (r * Real.log y) ≤ (1 / (2 * D)) ^ k := by
  have h1 := htail k _ hy h
  have h2 : Real.exp (-(r * Real.log y) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ (1 / (2 * D)) ^ k)
  linarith [h1, h3]

/-- The endpoint term, from the kernel decay and the detector mass. -/
theorem endpoint_bound {D Kd Ly C0 : ℝ} {k : ℕ} (hD : 0 < D) (hKd : 0 ≤ Kd)
    (hk : Decomp1532b2.poissonKernel k Ly ≤ (1 / (2 * D)) ^ k) (hd : Kd ≤ Ly + C0) :
    Decomp1532b2.poissonKernel k Ly * Kd ≤ (1 / (2 * D)) ^ k * (Ly + C0) :=
  mul_le_mul hk hd hKd (by positivity)

/-- The prime power step: the window sum is within `C3 / sqrt x` of the von Mangoldt sum. -/
theorem pp_bound {C3 sq : ℝ} (Ww Wc : ℂ) (hpp : ‖Ww - Wc‖ ≤ C3 / sq) :
    ‖Ww‖ - C3 / sq ≤ ‖Wc‖ := by
  have h := norm_sub_ge Ww Wc
  linarith

/-- `8 C₃ r ≤ η` from the `r₁` bound. -/
theorem eight_C3_r_le {C3 r η : ℝ} (hC3 : 0 ≤ C3) (hr : 0 < r) (hr3 : r ≤ η / (8 * C3 + 1)) :
    8 * C3 * r ≤ η := by
  have h3C : (0:ℝ) < 8 * C3 + 1 := by linarith
  have h2 : r * (8 * C3 + 1) ≤ η := by
    have h := mul_le_mul_of_nonneg_right hr3 h3C.le
    have h4 : (η / (8 * C3 + 1)) * (8 * C3 + 1) = η := by field_simp
    linarith [h, h4]
  have h5 : 8 * C3 * r ≤ r * (8 * C3 + 1) := by
    have h7 : 8 * C3 * r = r * (8 * C3) := by ring
    rw [h7]
    exact mul_le_mul_of_nonneg_left (by linarith) hr.le
  linarith [h2, h5]

/-- `8 C₃ D^k r ≤ η √x` from `D^k ≤ √x` and `8 C₃ r ≤ η`. -/
theorem pp_scaled {C3 Dk r η s : ℝ} (hC3 : 0 ≤ C3) (hr : 0 ≤ r) (h8 : 8 * C3 * r ≤ η)
    (hDk : Dk ≤ s) (hs0 : 0 ≤ s) : 8 * C3 * Dk * r ≤ η * s := by
  have h1 : 8 * C3 * Dk ≤ 8 * C3 * s :=
    mul_le_mul_of_nonneg_left hDk (by linarith)
  have h2 : 8 * C3 * Dk * r ≤ 8 * C3 * s * r := mul_le_mul_of_nonneg_right h1 hr
  have h3 : 8 * C3 * s * r = (8 * C3 * r) * s := by ring
  have h4 : (8 * C3 * r) * s ≤ η * s := mul_le_mul_of_nonneg_right h8 hs0
  linarith [h2, h3, h4]

/-- The prime power term against the main term. -/
theorem pp_div {C3 Dk r η s : ℝ} (hs : 0 < s) (hDk : 0 < Dk) (hr : 0 < r)
    (h : 8 * C3 * Dk * r ≤ η * s) : C3 / s ≤ η / (8 * (Dk * r)) := by
  have h8D : (0:ℝ) < 8 * (Dk * r) := by
    have h1 : (0:ℝ) < Dk * r := mul_pos hDk hr
    linarith
  rw [div_le_div_iff₀ hs h8D]
  nlinarith [h]

/-- The prime power comparison of the assembly, in one step (this is where the closing `nlinarith`
used to time out). -/
theorem pp_comparison {C3 Dk r η s : ℝ} (hC3 : 0 ≤ C3) (hs : 0 < s) (hDk : 0 < Dk)
    (hr : 0 < r) (hr3 : r ≤ η / (8 * C3 + 1)) (hDkle : Dk ≤ s) :
    C3 / s ≤ η / (8 * (Dk * r)) := by
  refine pp_div hs hDk hr ?_
  exact pp_scaled hC3 hr.le (eight_C3_r_le hC3 hr hr3) hDkle hs.le

/-- `k log D ≤ (log x)/4` from `Cc r ≤ 1/2`. -/
theorem k_logD_quarter {k D Cc r x : ℝ} (hCcrmul : Cc * r ≤ 1 / 2) (hlogx : 0 ≤ Real.log x)
    (hkD : k * Real.log D ≤ Cc * (r * Real.log x) / 2) : k * Real.log D ≤ Real.log x / 4 := by
  have h1 : Cc * (r * Real.log x) = (Cc * r) * Real.log x := by ring
  have h2 : (Cc * r) * Real.log x ≤ (1 / 2) * Real.log x :=
    mul_le_mul_of_nonneg_right hCcrmul hlogx
  linarith [hkD, h1, h2]

/-- `D ^ k ≤ √x` from `k log D ≤ (log x)/4`. -/
theorem Dk_le_sqrt {D x : ℝ} (hD : 0 < D) (hx : 1 ≤ x) {k : ℕ}
    (h : (k : ℝ) * Real.log D ≤ Real.log x / 4) : D ^ k ≤ Real.sqrt x := by
  have h1 : D ^ k ≤ Real.exp (Real.log x / 4) := pow_le_exp_of_log hD k h
  have h2 : Real.exp (Real.log x / 4) ≤ Real.sqrt x := by
    have h3 : Real.sqrt x = Real.exp (Real.log x / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith : (0:ℝ) < x)]
      congr 1
      ring
    rw [h3]
    exact Real.exp_le_exp.mpr (by linarith [Real.log_nonneg hx])
  linarith

/-- The small-part comparison: the `r`-rescaling and the kernel engine in one step. -/
theorem comp_small {D η r Lx C1 : ℝ} (hD : 0 < D) (hr : 0 < r) (hr1 : r ≤ 1) (hη : 0 < η)
    {k : ℕ} (hL : 0 ≤ Lx) (hC1 : 0 ≤ C1) (h : (1 / 2 : ℝ) ^ k * (r * Lx + C1) ≤ η / 8) :
    (1 / (2 * D)) ^ k * (Lx + C1) ≤ η / (8 * (D ^ k * r)) := by
  apply kernel_engine3 hD hr hη k
  have h5 : Lx * r ≤ Lx := by nlinarith
  have h3 : (Lx + C1) * r ≤ r * Lx + C1 := by nlinarith [h5, hC1]
  have h2 : (1 / 2 : ℝ) ^ k * (Lx + C1) * r ≤ (1 / 2 : ℝ) ^ k * (r * Lx + C1) := by
    have h6 : (0:ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    calc (1 / 2 : ℝ) ^ k * (Lx + C1) * r = (1 / 2 : ℝ) ^ k * ((Lx + C1) * r) := by ring
      _ ≤ (1 / 2 : ℝ) ^ k * (r * Lx + C1) := mul_le_mul_of_nonneg_left h3 h6
  have h4 : (1 / 2 : ℝ) ^ k * (Lx + C1) * r ≤ η / 8 := h2.trans h
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 8 * r)]
  linarith

/-- The tail comparison. -/
theorem comp_tail {D η r Lx C2 : ℝ} (hD : 0 < D) (hr : 0 < r) (hη : 0 < η) {k : ℕ}
    (hL : 0 ≤ Lx) (h : (1 / 2 : ℝ) ^ k * (r * Lx + C2) ≤ η / 8) :
    (1 / (2 * D)) ^ k * (C2 / r) ≤ η / (8 * (D ^ k * r)) := by
  apply kernel_engine1 hD hr hη k
  have h4 : (0:ℝ) ≤ r * Lx := mul_nonneg hr.le hL
  have h3 : C2 ≤ r * Lx + C2 := by linarith
  exact (mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ (1 / 2 : ℝ) ^ k)).trans h

/-- The endpoint comparison. -/
theorem comp_endpoint {D η r Lx C0 Bc : ℝ} (hD : 0 < D) (hr : 0 < r) (hr1 : r ≤ 1)
    (hη : 0 < η) {k : ℕ} (hL : 0 ≤ Lx) (hBc : 1 ≤ Bc) (hC0 : 0 ≤ C0)
    (h : (1 / 2 : ℝ) ^ k * (r * Lx + C0) ≤ η / (8 * Bc)) :
    (1 / (2 * D)) ^ k * (Bc * Lx + C0) ≤ η / (8 * (D ^ k * r)) := by
  apply kernel_engine3 hD hr hη k
  have h5 : Bc * (r * Lx + C0) = Bc * (r * Lx) + Bc * C0 := by ring
  have h6 : (Bc * Lx + C0) * r ≤ Bc * (r * Lx + C0) := by
    have h7 : (Bc * Lx + C0) * r = Bc * (Lx * r) + C0 * r := by ring
    have h8 : Bc * (Lx * r) = Bc * (r * Lx) := by ring
    have h9 : C0 * r ≤ Bc * C0 := by
      have h10 : C0 * r ≤ C0 * Bc := mul_le_mul_of_nonneg_left (le_trans hr1 hBc) hC0
      linarith
    have h12 : Bc * (r * Lx) + Bc * C0 = Bc * (r * Lx + C0) := by ring
    linarith [h7, h8, h9, h12]
  have h4 : (1 / 2 : ℝ) ^ k * (Bc * Lx + C0) * r ≤
      Bc * ((1 / 2 : ℝ) ^ k * (r * Lx + C0)) := by
    have h10 : (0:ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    calc (1 / 2 : ℝ) ^ k * (Bc * Lx + C0) * r
        = (1 / 2 : ℝ) ^ k * ((Bc * Lx + C0) * r) := by ring
      _ ≤ (1 / 2 : ℝ) ^ k * (Bc * (r * Lx + C0)) := mul_le_mul_of_nonneg_left h6 h10
      _ = Bc * ((1 / 2 : ℝ) ^ k * (r * Lx + C0)) := by ring
  have h11 : Bc * ((1 / 2 : ℝ) ^ k * (r * Lx + C0)) ≤ Bc * (η / (8 * Bc)) :=
    mul_le_mul_of_nonneg_left h (by linarith)
  have h12 : Bc * (η / (8 * Bc)) = η / 8 := by field_simp
  have h13 : (1 / 2 : ℝ) ^ k * (Bc * Lx + C0) * r ≤ η / 8 := by
    linarith [h4, h11, h12]
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 8 * r)]
  linarith

theorem poisson_window_localization_proof :
    ∀ E D η : ℝ, 1 ≤ E → 1 ≤ D → 0 < η →
      ∃ r₁ A B C c : ℝ, 0 < r₁ ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
        ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
          |v| ≤ T → 1 / Real.log T ≤ r → r ≤ r₁ →
          (∀ M : ℕ, E * r * Real.log T ≤ M →
            ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
              η / (D ^ k * r) ≤
                ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
                  (n : ℂ) ^ (1 + I * v)) *
                  (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)‖) →
          ∀ x : ℝ, T ^ A ≤ x → ∃ k : ℕ,
            c * x ^ (-C * r) * Real.log x ^ 2 * r ≤
              ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ B⌋₊,
                (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) *
                  primeWindowCoefficient χ x v n‖ -
                Decomp1532b2.poissonKernel k (r * Real.log (x ^ B)) *
                  ‖primeDetector χ x (x ^ B) v‖ := by
  intro E D η hE hD hη
  obtain ⟨C1, hC1, hsmall⟩ := poisson_small_cutoff_norm
  obtain ⟨C2, hC2, hlarge⟩ := poisson_large_cutoff_norm
  obtain ⟨C3, hC3, hpp⟩ := Decomp1532b2.poisson_weighted_prime_power_removal
  obtain ⟨C0, hC0, hdet⟩ := detector_norm_le
  have hD0 : (0:ℝ) < D := by linarith
  obtain ⟨Bk, hBk, hBktail⟩ := poissonKernel_large_tail D hD0
  obtain ⟨Bs, hBs, hsmallB⟩ := hsmall D hD0
  obtain ⟨Bl, hBl, hlargeB⟩ := hlarge D hD0
  set Bcx : ℝ := 16 + 32 * (Bl + Bk) * (1 / Bs + E + 2 + 1) with hBcx
  set Ccx : ℝ := 8 * (max (Real.log D) 0) * (1 / Bs + E + 2 + 1) + 1 with hCcx
  have hBcaux : (0:ℝ) ≤ 32 * (Bl + Bk) * (1 / Bs + E + 2 + 1) := by positivity
  have hBcpos : (0:ℝ) ≤ Bcx := by rw [hBcx]; linarith
  have hBc1 : (1:ℝ) ≤ Bcx := by rw [hBcx]; linarith
  have hBc2 : (2:ℝ) ≤ Bcx := by linarith
  have hBcne : Bcx ≠ 0 := by linarith
  have hCcp : (0:ℝ) < Ccx := by rw [hCcx]; positivity
  have hCc1 : (1:ℝ) ≤ Ccx := by
    rw [hCcx]
    have h1 : (0:ℝ) ≤ 8 * (max (Real.log D) 0) * (1 / Bs + E + 2 + 1) := by positivity
    linarith
  obtain ⟨Aabs1, hAabs1b, hAabs1⟩ := absorption (η := η) (B1 := Bs) (S := C1) hη hBs hC1
  obtain ⟨Aabs2, hAabs2b, hAabs2⟩ := absorption (η := η) (B1 := Bs) (S := C2) hη hBs hC2
  obtain ⟨Aabs3, hAabs3b, hAabs3⟩ := absorption (η := η / Bcx) (B1 := Bs) (S := C0)
    (by positivity) hBs hC0
  refine ⟨1 / (4 + 2 * Ccx + (8 * C3 + 1) / η),
    Aabs1 + Aabs2 + Aabs3 + 8 + 1, Bcx, Ccx, η / 64, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (0:ℝ) < 4 + 2 * Ccx + (8 * C3 + 1) / η := by positivity
    positivity
  · linarith
  · linarith
  · linarith
  · positivity
  intro T hT q hq hqT χ v r hv hrlo hrhi hseries x hx
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hr : 0 < r := (one_div_pos.mpr hlT).trans_le hrlo
  have hrq : 1 ≤ r * Real.log T := by
    have h3 := mul_le_mul_of_nonneg_right hrlo hlT.le
    have h4 : (1 / Real.log T) * Real.log T = 1 := by field_simp
    linarith
  have hK0 : (0:ℝ) < (8 * C3 + 1) / η := by
    have h1 : (0:ℝ) < 8 * C3 + 1 := by linarith
    positivity
  have hsum3 : (0:ℝ) < 4 + 2 * Ccx + (8 * C3 + 1) / η := by linarith
  have hr1 : r ≤ 1 := by
    have h2 : r ≤ 1 / (4 + 2 * Ccx + (8 * C3 + 1) / η) := hrhi
    have h3 : (1:ℝ) / (4 + 2 * Ccx + (8 * C3 + 1) / η) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hsum3 (by norm_num)]
      linarith [hK0.le, hCcp.le]
    linarith
  have hrCc : r ≤ 1 / (2 * Ccx) := by
    have h2 : r ≤ 1 / (4 + 2 * Ccx + (8 * C3 + 1) / η) := hrhi
    have h3 : (1:ℝ) / (4 + 2 * Ccx + (8 * C3 + 1) / η) ≤ 1 / (2 * Ccx) := by
      rw [div_le_div_iff₀ hsum3 (by linarith)]
      linarith [hK0.le]
    linarith
  have hrC3 : r ≤ η / (8 * C3 + 1) := by
    have h2 : r ≤ 1 / (4 + 2 * Ccx + (8 * C3 + 1) / η) := hrhi
    have h3 : (1:ℝ) / (4 + 2 * Ccx + (8 * C3 + 1) / η) ≤ η / (8 * C3 + 1) := by
      rw [div_le_div_iff₀ hsum3 (by linarith)]
      have h4 : (8 * C3 + 1) / η * η = 8 * C3 + 1 := by field_simp
      nlinarith [h4, hK0, hCcp, hη]
    linarith
  have hxT : 1 ≤ T := by linarith
  have hx1 : 1 ≤ x := by
    have h1 : (1:ℝ) ≤ T ^ (Aabs1 + Aabs2 + Aabs3 + 8 + 1) := Real.one_le_rpow hxT (by linarith)
    linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogTle : Real.log T ≤ Real.log x := by
    have h1 : T ≤ x := by
      calc T = T ^ (1:ℝ) := (Real.rpow_one T).symm
        _ ≤ T ^ (Aabs1 + Aabs2 + Aabs3 + 8 + 1) :=
            Real.rpow_le_rpow_of_exponent_le hxT (by linarith)
        _ ≤ x := hx
    exact Real.log_le_log (by linarith) h1
  have ht1 : 1 ≤ r * Real.log x := hrq.trans (mul_le_mul_of_nonneg_left hlogTle hr.le)
  have hA_le_t : Aabs1 + Aabs2 + Aabs3 + 8 + 1 ≤ r * Real.log x := by
    have h1 : Real.log (T ^ (Aabs1 + Aabs2 + Aabs3 + 8 + 1)) ≤ Real.log x :=
      Real.log_le_log (by positivity) hx
    have h2 : Real.log (T ^ (Aabs1 + Aabs2 + Aabs3 + 8 + 1))
        = (Aabs1 + Aabs2 + Aabs3 + 8 + 1) * Real.log T :=
      Real.log_rpow (by linarith : (0:ℝ) < T) _
    rw [h2] at h1
    have h3 : r * ((Aabs1 + Aabs2 + Aabs3 + 8 + 1) * Real.log T) ≤ r * Real.log x :=
      mul_le_mul_of_nonneg_left h1 hr.le
    have h4 : (1:ℝ) ≤ r * Real.log T := hrq
    have h5 : (0:ℝ) ≤ r * Real.log T := le_trans (by norm_num) h4
    nlinarith [h3, h4, h5]
  have hA1t : Aabs1 ≤ r * Real.log x := by linarith [hAabs1b, hAabs2b, hAabs3b, hA_le_t]
  have hA2t : Aabs2 ≤ r * Real.log x := by linarith [hAabs1b, hAabs2b, hAabs3b, hA_le_t]
  have hA3t : Aabs3 ≤ r * Real.log x := by linarith [hAabs1b, hAabs2b, hAabs3b, hA_le_t]
  set M : ℕ := ⌈max (r * Real.log x / Bs) (E * r * Real.log T)⌉₊ with hM
  have hMcast : (M : ℝ) = (⌈max (r * Real.log x / Bs) (E * r * Real.log T)⌉₊ : ℝ) := by rw [hM]
  have hMceil : max (r * Real.log x / Bs) (E * r * Real.log T) ≤ (M : ℝ) := by
    have h := Nat.le_ceil (max (r * Real.log x / Bs) (E * r * Real.log T))
    linarith [hMcast]
  obtain ⟨k, hMk, hk2M, hser⟩ := hseries M ((le_max_right _ _).trans hMceil)
  have hkM : (M : ℝ) ≤ (k : ℝ) := by exact_mod_cast hMk
  have hkup : (k : ℝ) ≤ 2 * max (r * Real.log x / Bs) (E * r * Real.log T) + 2 := by
    have h6 : (⌈max (r * Real.log x / Bs) (E * r * Real.log T)⌉₊ : ℝ) ≤
        max (r * Real.log x / Bs) (E * r * Real.log T) + 1 :=
      (Nat.ceil_lt_add_one (le_trans (by positivity) (le_max_left _ _))).le
    have h7 : ((k : ℕ) : ℝ) < 2 * ((M : ℕ) : ℝ) := by exact_mod_cast hk2M
    linarith [hMcast]
  have hmax : max (r * Real.log x / Bs) (E * r * Real.log T) ≤
      (r * Real.log x) * (1 / Bs + E + 2) := by
    apply max_le
    · have h4 : r * Real.log x / Bs = (r * Real.log x) * (1 / Bs) := by ring
      rw [h4]
      have h5 : (0:ℝ) ≤ r * Real.log x := by positivity
      have h6 : (0:ℝ) ≤ r * Real.log x * E := by positivity
      nlinarith [h5, h6]
    · have h6 : (0:ℝ) ≤ r * Real.log x * (1 / Bs) := by positivity
      have h7 : (0:ℝ) ≤ r * Real.log x := by positivity
      have h8 : r * Real.log T ≤ r * Real.log x := mul_le_mul_of_nonneg_left hlogTle hr.le
      nlinarith [h6, h8]
  have hkt : (k : ℝ) ≤ 2 * (r * Real.log x) * (1 / Bs + E + 2 + 1) := by
    have h1 : (0:ℝ) ≤ r * Real.log x := by positivity
    have h2 : (0:ℝ) ≤ r * Real.log x * (1 / Bs + E + 2) := by positivity
    nlinarith [hkup, hmax, h1, ht1]
  have hsm : r * Real.log x ≤ Bs * (k : ℝ) := by
    have h2 : r * Real.log x / Bs ≤ (k : ℝ) :=
      (le_trans (le_max_left _ _) hMceil).trans hkM
    rw [div_le_iff₀ hBs] at h2
    linarith
  have hMx1 : (1:ℝ) ≤ 1 / Bs + E + 2 := by
    have h1 : (0:ℝ) < 1 / Bs := by positivity
    linarith
  have hkD : (k : ℝ) * Real.log D ≤ Ccx * (r * Real.log x) / 2 :=
    k_logD_le (k := (k : ℝ)) (t := r * Real.log x) (Ld := max (Real.log D) 0)
      (Mx := 1 / Bs + E + 2) (Cc := Ccx) (logD := Real.log D) hkt ht1
      (le_max_left (Real.log D) 0) (Real.log_nonneg hD) (le_max_right (Real.log D) 0) hMx1 hCcx.symm
  have hLb_k : (Bl + Bk) * (k : ℝ) ≤ Bcx * (r * Real.log x) :=
    lb_k_le (k := (k : ℝ)) (t := r * Real.log x) (Lb := Bl + Bk) (Mx := 1 / Bs + E + 2)
      (Bc := Bcx) hkt ht1 (by linarith) hMx1 hBcx.symm
  have hy1 : 1 ≤ x ^ Bcx := Real.one_le_rpow hx1 (by linarith)
  have hxy : x ≤ x ^ Bcx := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 hBc1
  have hlogy : Real.log (x ^ Bcx) = Bcx * Real.log x := Real.log_rpow (by linarith) Bcx
  have hlgB : (Bl + Bk) * (k : ℝ) ≤ r * Real.log (x ^ Bcx) := by
    have h6 : r * Real.log (x ^ Bcx) = r * Bcx * Real.log x := by rw [hlogy]; ring
    have h5 : r * Bcx * Real.log x = Bcx * (r * Real.log x) := by ring
    rw [h6, h5]
    exact hLb_k
  let Acoef : ℕ → ℂ := fun n =>
    χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (1 + I * v)
  let Kk : ℕ → ℂ := fun n => (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)
  have hAnorm : ∀ n : ℕ, ‖Acoef n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
    fun n => norm_series_coef χ v n
  have hAcoef0 : Acoef 0 = 0 := by
    dsimp only [Acoef]
    simp
  have hsmall' : ‖∑ n ∈ Icc 1 ⌊x⌋₊, Acoef n * Kk n‖ ≤
      (1 / (2 * D)) ^ k * (Real.log x + C1) :=
    hsmallB Acoef k r x hr.le hx1 hsm (fun n _ => hAnorm n)
  have hAb : ‖∑ n ∈ Icc 0 ⌊x⌋₊, Acoef n * Kk n‖ ≤
      (1 / (2 * D)) ^ k * (Real.log x + C1) :=
    small_part_le Acoef Kk hAcoef0 hsmall'
  have hlg : Bl * (k : ℝ) ≤ r * Real.log (x ^ Bcx) := by
    have hk0 : (0:ℝ) ≤ (k : ℝ) := by positivity
    have h1 : Bl * (k : ℝ) ≤ (Bl + Bk) * (k : ℝ) := by nlinarith [hBl.le, hBk.le, hk0]
    linarith [hlgB, h1]
  obtain ⟨hsumtail, htailb⟩ := hlargeB Acoef k r (x ^ Bcx) hr hr1 hy1 hlg hAnorm
  have hPb : ‖∑' n : ℕ, (if ⌊x ^ Bcx⌋₊ < n then Acoef n * Kk n else 0)‖ ≤
      (1 / (2 * D)) ^ k * (C2 / r) :=
    tail_part_le (Bc := Bcx) Acoef Kk (by positivity) htailb
  have htail'' : Summable (fun n : ℕ => if x ^ Bcx < (n : ℝ) then
      (χ n * (n : ℂ) ^ (-(I * v))) *
        (((ArithmeticFunction.vonMangoldt n / (n : ℝ)) *
          Decomp1532b2.poissonKernel k (r * Real.log n) : ℝ) : ℂ) else 0) := by
    refine hsumtail.congr (fun n => ?_)
    by_cases hh : x ^ Bcx < (n : ℝ)
    · rw [if_pos hh, if_pos hh]
      by_cases hn : n = 0
      · subst hn
        simp [Acoef, Kk, Complex.zero_cpow]
      · exact seriesTerm_eq χ v r k hn
    · rw [if_neg hh, if_neg hh]
  have hsumF : Summable (fun n : ℕ => Acoef n * Kk n) :=
    summable_series χ v r k hy1 htail''
  have hsplit := tsum_three_split χ v r k hx1 hxy (fun n => Acoef n * Kk n)
    (fun n => rfl) hsumF
  have hWrel : ‖∑' n : ℕ, Acoef n * Kk n‖ - ‖∑ n ∈ Icc 0 ⌊x⌋₊, Acoef n * Kk n‖ -
      ‖∑' n : ℕ, (if ⌊x ^ Bcx⌋₊ < n then Acoef n * Kk n else 0)‖ ≤
      ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊, Acoef n * Kk n‖ := by
    refine norm_three_lower _ _ _ _ ?_
    rw [hsplit]
    abel
  let aa : ℕ → ℂ := fun n => χ n * (n : ℂ) ^ (-(I * v))
  let Wc : ℂ := ∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊, Kk n * primeWindowCoefficient χ x v n
  let Ep : ℝ := Decomp1532b2.poissonKernel k (r * Real.log (x ^ Bcx)) *
    ‖primeDetector χ x (x ^ Bcx) v‖
  have hppw := hpp x (x ^ Bcx) r hx1 hxy hr.le k aa (fun n => norm_chi_cpow_le_one χ v n)
  have hS1 : (∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊, aa n *
      (((ArithmeticFunction.vonMangoldt n / (n : ℝ)) *
        Decomp1532b2.poissonKernel k (r * Real.log n) : ℝ) : ℂ))
      = ∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊, Acoef n * Kk n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      have h2 := (mem_Ioc.mp hn).1
      omega
    exact (seriesTerm_eq χ v r k hn0).symm
  have hS2 : (∑ n ∈ (Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊).filter Nat.Prime, aa n *
      (((Real.log n / (n : ℝ)) * Decomp1532b2.poissonKernel k (r * Real.log n) : ℝ) : ℂ))
      = Wc := by
    show _ = ∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊, Kk n * primeWindowCoefficient χ x v n
    rw [sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hnp : n.Prime
    · rw [if_pos hnp]
      have hlt : ⌊x⌋₊ < n := (mem_Ioc.mp hn).1
      have h1 := seriesTerm_eq_coefficient χ x v r k hnp hlt
      have h2 := seriesTerm_eq χ v r k hnp.ne_zero
      rw [ArithmeticFunction.vonMangoldt_apply_prime hnp] at h1 h2
      exact h2.symm.trans h1
    · rw [if_neg hnp]
      simp [primeWindowCoefficient, hnp]
  have hPw : ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊, Acoef n * Kk n‖ - C3 / Real.sqrt x ≤ ‖Wc‖ := by
    rw [← hS1, ← hS2]
    exact pp_bound _ _ hppw
  have hBk_le : Bk * (k : ℝ) ≤ r * Real.log (x ^ Bcx) := by
    have hk0 : (0:ℝ) ≤ (k : ℝ) := by positivity
    have h1 : Bk * (k : ℝ) ≤ (Bl + Bk) * (k : ℝ) := by nlinarith [hBl.le, hBk.le, hk0]
    linarith [hlgB, h1]
  have hkend := kernel_endpoint_le hD0 hBk hBktail (k := k) (r := r)
    (y := x ^ Bcx) (mul_nonneg hr.le (Real.log_nonneg hy1)) hBk_le
  have hdetb := hdet q χ x (x ^ Bcx) v hx1 hxy
  have hEp : Ep ≤ (1 / (2 * D)) ^ k * (Bcx * Real.log x + C0) := by
    show Decomp1532b2.poissonKernel k (r * Real.log (x ^ Bcx)) *
      ‖primeDetector χ x (x ^ Bcx) v‖ ≤ _
    have h2 : Decomp1532b2.poissonKernel k (r * Real.log (x ^ Bcx)) *
        ‖primeDetector χ x (x ^ Bcx) v‖ ≤
        (1 / (2 * D)) ^ k * (Real.log (x ^ Bcx) + C0) :=
      mul_le_mul hkend hdetb (norm_nonneg _) (by positivity)
    have h3 : Real.log (x ^ Bcx) + C0 ≤ Bcx * Real.log x + C0 := by rw [hlogy]
    exact h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  have hDkpos : (0:ℝ) < D ^ k := pow_pos hD0 k
  have hsqx : (0:ℝ) < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have h8r : (0:ℝ) < 8 * r := by linarith
  have hcomp1 := comp_small (D := D) (η := η) (r := r) (Lx := Real.log x) (C1 := C1)
    hD0 hr hr1 hη (k := k) hlogx hC1 (hAabs1 (r * Real.log x) hA1t k hsm)
  have hcomp2 := comp_tail (D := D) (η := η) (r := r) (Lx := Real.log x) (C2 := C2)
    hD0 hr hη (k := k) hlogx (hAabs2 (r * Real.log x) hA2t k hsm)
  have h3abs : (1 / 2 : ℝ) ^ k * (r * Real.log x + C0) ≤ η / (8 * Bcx) := by
    have h1 := hAabs3 (r * Real.log x) hA3t k hsm
    have h2 : η / Bcx / 8 = η / (8 * Bcx) := by field_simp
    rw [h2] at h1
    exact h1
  have hcomp3 := comp_endpoint (D := D) (η := η) (r := r) (Lx := Real.log x) (C0 := C0)
    (Bc := Bcx) hD0 hr hr1 hη (k := k) hlogx hBc1 hC0 h3abs
  have hCcrmul : Ccx * r ≤ 1 / 2 := by
    have h2 := mul_le_mul_of_nonneg_right hrCc hCcp.le
    have h3 : (1 / (2 * Ccx)) * Ccx = 1 / 2 := by field_simp
    rw [mul_comm Ccx r]
    linarith [h2, h3]
  have hkD4 : (k : ℝ) * Real.log D ≤ Real.log x / 4 :=
    k_logD_quarter hCcrmul hlogx hkD
  have hDk_le : D ^ k ≤ Real.sqrt x := Dk_le_sqrt hD0 hx1 hkD4
  have hcomp4 := pp_comparison (C3 := C3) (Dk := D ^ k) (r := r) (η := η)
    (s := Real.sqrt x) hC3 hsqx hDkpos hr hrC3 hDk_le
  have ht8 : (8:ℝ) ≤ r * Real.log x := by
    have h1 : (0:ℝ) ≤ Aabs1 := by linarith
    linarith [hA_le_t]
  have hDkexp : D ^ k ≤ Real.exp (Ccx * (r * Real.log x) / 2) :=
    pow_le_exp_of_log hD0 k (by linarith [hkD])
  have hscaled : Real.exp (-(Ccx * (r * Real.log x))) * (r * Real.log x) ^ 2 * D ^ k ≤ 32 :=
    final_scaled hDkexp (sq_le_exp hCc1 ht8)
  have hxs : x ^ (-Ccx * r) = Real.exp (-(Ccx * (r * Real.log x))) := by
    rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < x)]
    congr 1
    ring
  have hfin : η / 64 * x ^ (-Ccx * r) * Real.log x ^ 2 * r ≤ η / (2 * (D ^ k * r)) :=
    final_div hη hr rfl (by ring) hxs hDkpos hscaled
  exact ⟨k, hfin.trans (chain_arith (Dk := D ^ k) (r := r) (X := (1 / (2 * D)) ^ k)
    (Lx := Real.log x) (C1 := C1) (C2 := C2) (C0 := C0) (Bc := Bcx) (C3 := C3)
    (sq := Real.sqrt x) (Sn := ‖∑' n : ℕ, Acoef n * Kk n‖)
    (An := ‖∑ n ∈ Icc 0 ⌊x⌋₊, Acoef n * Kk n‖)
    (Pn := ‖∑' n : ℕ, (if ⌊x ^ Bcx⌋₊ < n then Acoef n * Kk n else 0)‖)
    (Wn := ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ Bcx⌋₊, Acoef n * Kk n‖)
    (Wc := ‖Wc‖) (Ep := Ep) hr hDkpos hsqx hser hWrel hPw hAb hPb hEp
    hcomp1 hcomp2 hcomp3 hcomp4)⟩

/-- LEAF, REPAIRED (U-1619, omos_tick 20261105T0144Z; changes only this statement).
Gallagher 1970 p.335 display 23 and the endpoint estimate below it.
Localization of a supplied dyadic Poisson series lower bound to a finite prime sum.
The endpoint term is subtracted before partial summation. No zero is assumed here.
REPAIR: `r` is bounded by a constant `r₁` chosen together with `A, B, C, c`. The old form allowed
`r ≤ 1/4` for every `D`, but this p.335 route removes the prime square terms by taking `k` about
`E r log T`, which needs `r log D` bounded (here `r ≤ r₁`), not `r ≤ 1/4`. See
`Linnik/Audit1619`. `gallagher_zero_detector_of_turan` below keeps its statement and takes
`min r₀ r₁`. -/
theorem poisson_window_localization :
    ∀ E D η : ℝ, 1 ≤ E → 1 ≤ D → 0 < η →
      ∃ r₁ A B C c : ℝ, 0 < r₁ ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
        ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
          |v| ≤ T → 1 / Real.log T ≤ r → r ≤ r₁ →
          (∀ M : ℕ, E * r * Real.log T ≤ M →
            ∃ k : ℕ, M ≤ k ∧ k < 2 * M ∧
              η / (D ^ k * r) ≤
                ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ) /
                  (n : ℂ) ^ (1 + I * v)) * (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ)‖) →
          ∀ x : ℝ, T ^ A ≤ x → ∃ k : ℕ,
            c * x ^ (-C * r) * Real.log x ^ 2 * r ≤
              ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊x ^ B⌋₊,
                (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) * primeWindowCoefficient χ x v n‖ -
                Decomp1532b2.poissonKernel k (r * Real.log (x ^ B)) * ‖primeDetector χ x (x ^ B) v‖ := by
  exact poisson_window_localization_proof

/-- Gallagher 1970 p.335 the calculus bound for the finite prime window.
The arithmetic lower bound and its zero hypothesis are absent. -/
theorem prime_poisson_partial_summation {q : ℕ} (χ : DirichletCharacter ℂ q)
    (k : ℕ) {r x y : ℝ} (v : ℝ) (hr : 0 ≤ r) (hx : 1 ≤ x) (hxy : x ≤ y) :
    ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊,
        (Decomp1532b2.poissonKernel k (r * Real.log n) : ℂ) * primeWindowCoefficient χ x v n‖ -
        Decomp1532b2.poissonKernel k (r * Real.log y) * ‖primeDetector χ x y v‖ ≤
      r * ∫ t in x..y, ‖primeDetector χ x t v‖ / t := by
  have ha : ∀ n ≤ ⌊x⌋₊, primeWindowCoefficient χ x v n = 0 := by
    intro n hn
    simp [primeWindowCoefficient, not_lt.mpr hn]
  simpa only [sum_primeWindowCoefficient] using
    poisson_partial_summation_bound (primeWindowCoefficient χ x v) k hr hx hxy ha

/-- Gallagher 1970 Theorem 5 display 20.
Exact sealed detector statement assembled from the two smaller arithmetic leaves.
CONDITIONAL ON those leaves. This theorem has no proof hole of its own. -/
theorem gallagher_zero_detector_of_turan
    (hpower : ∀ n M : ℕ, 0 < n → n ≤ M → ∀ z : Fin n → ℂ, (∃ i, 1 ≤ ‖z i‖) →
      ∃ ν : ℕ, M < ν ∧ ν ≤ 2 * M ∧ (1 / 50 : ℝ) ^ M ≤ ‖∑ i, z i ^ ν‖) :
    ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y := by
  obtain ⟨r₀, E, D, η, hr₀, hr₀hi, hE, hD, hη, hseries⟩ :=
    poisson_series_detector_of_turan hpower
  obtain ⟨r₁, A, B, C, c, hr₁, hA, hB, hC, hc, hwindow⟩ :=
    poisson_window_localization E D η hE hD hη
  refine ⟨min r₀ r₁, A, B, C, c, lt_min hr₀ hr₁, (min_le_left _ _).trans hr₀hi,
    hA, hB, hC, hc, ?_⟩
  intro T hT q hq hqT χ v r hv hχ hrlo hrhi hz x hx
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have hr : 0 < r := (one_div_pos.mpr hl).trans_le hrlo
  have hx1 : 1 ≤ x :=
    (Real.one_le_rpow (by linarith : 1 ≤ T) (by linarith : 0 ≤ A)).trans hx
  have hxy : x ≤ x ^ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 hB.le
  obtain ⟨k, hk⟩ := hwindow T hT q hqT χ v r hv hrlo (hrhi.trans (min_le_right _ _))
    (hseries T hT q hqT χ v r hv hχ hrlo (hrhi.trans (min_le_left _ _)) hz) x hx
  have hh := hk.trans (prime_poisson_partial_summation χ k v hr.le hx1 hxy)
  exact (mul_le_mul_iff_right₀ hr).mp (by simpa only [mul_comm r] using hh)

end LeanLab.Linnik.Decomp307a
