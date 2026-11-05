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
  sorry

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
