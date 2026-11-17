/-
Montgomery and Vaughan, Hilbert's inequality, 1974 page 73 display 1.3.
https://doi.org/10.1112/jlms/s2-8.1.73
The individual spacing input for Decomp1525b remains cited.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Decomp1525b2
import Mathlib
import LeanLab.Linnik.HilbertCosecant
import Mathlib.Analysis.Real.Pi.Bounds

open Finset Complex MeasureTheory
open scoped Classical ComplexConjugate Interval
noncomputable section

namespace LeanLab.SchnirelmannBounds.Decomp1525b

/-- LEAF. Montgomery and Vaughan 1974 page 73 Theorem 1 display 1.3.
For real points distinct modulo one and positive individual spacings no greater
than each distance to another point, the cosecant form has norm at most three
halves times the sum of squared coefficient norms divided by individual spacing.
The positive spacing and pairwise bounds express the paper's minimum condition.
This is also MV1973 page 122 display 2.2. This analytic input remains cited. -/
theorem mv1974_individual_cosecant {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (x δ : ι → ℝ)
    (hδ : ∀ r ∈ R, 0 < δ r)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s →
      δ r ≤ LeanLab.PNTPort.LargeSieve.dist0 (x r - x s))
    (u : ι → ℂ) :
    ‖∑ r ∈ R, ∑ s ∈ R.erase r,
      u r * (starRingEnd ℂ) (u s) / (Real.sin (Real.pi * (x r - x s)) : ℂ)‖ ≤
      3 / 2 * ∑ r ∈ R, ‖u r‖ ^ 2 / δ r := by
  sorry

/-
The finite eigen identity adapts LeanLab.Linnik.HilbertCosecant.eigen_identity.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under the Apache 2.0 license.
The matrix proof skeleton is adapted from anthropics/zeta-23-lean,
commit 16a5ce41304fcdaea4e0be7c132e1c361dc26da5,
zeta23/Zeta23/MV/Quadratic, EigenIdentity, Eigen and Duality.
https://github.com/anthropics/zeta-23-lean/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/zeta23/Zeta23/MV
-/

/-- The row eigen identity allows a different real frequency in each row.
MV1974 page 80 displays 3.10 to 3.14, before multiplication by individual spacing.
The imaginary term cancels separately in each row. -/
theorem mv1974_eigen_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K C : ι → ι → ℝ) (hK : ∀ m n, K n m = -K m n)
    (hprod : ∀ m n p, m ≠ n → m ≠ p → n ≠ p →
      K m n * K m p = K n p * (C m n - C m p))
    (u : ι → ℂ) (η : ι → ℝ)
    (heig : ∀ m, ∑ n ∈ univ.erase m, (K m n : ℂ) * u n = ((η m : ℝ) : ℂ) * I * u m)
    (m : ι) :
    η m ^ 2 * ‖u m‖ ^ 2 =
      (∑ n ∈ univ.erase m, K m n ^ 2 * ‖u n‖ ^ 2) +
        2 * ∑ n ∈ univ.erase m, C m n * K m n * (u m * conj (u n)).re := by
  classical
  let S := univ.erase m
  let R (n p : ι) := (u n * conj (u p)).re
  have hRs (n p : ι) : R n p = R p n := by simp [R, mul_re]; ring
  have hRd (n : ι) : R n n = ‖u n‖ ^ 2 := by
    simp only [R, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hA : η m ^ 2 * ‖u m‖ ^ 2 = ∑ n ∈ S, ∑ p ∈ S, K m n * K m p * R n p := by
    have hn (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have h1 : η m ^ 2 * ‖u m‖ ^ 2 = ‖((η m : ℝ) : ℂ) * I * u m‖ ^ 2 := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        mul_pow, Real.norm_eq_abs, sq_abs]
    rw [h1, ← heig m, hn, map_sum, sum_mul_sum, Complex.re_sum]
    apply sum_congr rfl
    intro n _
    rw [Complex.re_sum]
    apply sum_congr rfl
    intro p _
    simp only [map_mul, Complex.conj_ofReal]
    have hh : (K m n : ℂ) * u n * ((K m p : ℂ) * conj (u p)) =
        ((K m n * K m p : ℝ) : ℂ) * (u n * conj (u p)) := by push_cast; ring
    rw [hh, Complex.re_ofReal_mul]
  have hB : (∑ n ∈ S, ∑ p ∈ S, K m n * K m p * R n p) =
      (∑ n ∈ S, K m n ^ 2 * ‖u n‖ ^ 2) +
        ∑ n ∈ S, ∑ p ∈ S.erase n, K m n * K m p * R n p := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    rw [← add_sum_erase S _ hn, hRd]
    ring
  let G (n p : ι) := C m n * K n p * R n p
  have hF (n : ι) (hn : n ∈ S) (p : ι) (hp : p ∈ S.erase n) :
      K m n * K m p * R n p = G n p + G p n := by
    have hn' : m ≠ n := (mem_erase.mp hn).1.symm
    have hp' : m ≠ p := (mem_erase.mp (mem_erase.mp hp).2).1.symm
    have hnp : n ≠ p := (mem_erase.mp hp).1.symm
    rw [hprod m n p hn' hp' hnp]
    dsimp [G]
    rw [hK p n, hRs p n]
    ring
  have hOff : (∑ n ∈ S, ∑ p ∈ S.erase n, K m n * K m p * R n p) =
      2 * ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by
    have hswap : (∑ n ∈ S, ∑ p ∈ S.erase n, G p n) =
        ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by
      apply sum_comm'
      intro n p
      simp only [mem_erase]
      tauto
    calc
      _ = ∑ n ∈ S, ∑ p ∈ S.erase n, (G n p + G p n) := by
        apply sum_congr rfl
        intro n hn
        exact sum_congr rfl (fun p hp => hF n hn p hp)
      _ = (∑ n ∈ S, ∑ p ∈ S.erase n, G n p) +
          ∑ n ∈ S, ∑ p ∈ S.erase n, G p n := by simp only [sum_add_distrib]
      _ = _ := by rw [hswap]; ring
  have hInner (n : ι) (hn : n ∈ S) :
      (∑ p ∈ S.erase n, G n p) = C m n * K m n * R m n := by
    let W : ℂ := ∑ p ∈ S.erase n, (K n p : ℂ) * conj (u p)
    have hi : (∑ p ∈ S.erase n, G n p) = C m n * (u n * W).re := by
      simp only [W, mul_sum, Complex.re_sum]
      apply sum_congr rfl
      intro p _
      have hh : u n * ((K n p : ℂ) * conj (u p)) =
          (K n p : ℂ) * (u n * conj (u p)) := by ring
      rw [hh, Complex.re_ofReal_mul]
      dsimp [G, R]
      ring
    have hconj := congrArg conj (heig n)
    simp only [map_sum, map_mul, Complex.conj_ofReal, Complex.conj_I] at hconj
    have hmn : m ∈ univ.erase n := mem_erase.mpr ⟨(mem_erase.mp hn).1.symm, mem_univ _⟩
    have hsplit := add_sum_erase (univ.erase n)
      (fun p => (K n p : ℂ) * conj (u p)) hmn
    have hSS : (univ.erase n).erase m = S.erase n := by
      dsimp [S]
      rw [erase_right_comm]
    rw [hSS] at hsplit
    rw [← hsplit] at hconj
    have hW : W = -(((η n : ℝ) : ℂ) * I * conj (u n)) - (K n m : ℂ) * conj (u m) := by
      dsimp [W]
      linear_combination hconj
    have hkill : (u n * (-(((η n : ℝ) : ℂ) * I * conj (u n)))).re = 0 := by
      have hh : u n * (-(((η n : ℝ) : ℂ) * I * conj (u n))) =
          -(((η n : ℝ) : ℂ) * (u n * conj (u n))) * I := by ring
      rw [hh, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp [-Complex.ofReal_pow]
    rw [hi, hW, mul_sub, Complex.sub_re, hkill]
    have hh : u n * ((K n m : ℂ) * conj (u m)) =
        (K n m : ℂ) * (u n * conj (u m)) := by ring
    rw [hh, Complex.re_ofReal_mul, hK m n]
    change C m n * (0 - -K m n * R n m) = C m n * K m n * R m n
    rw [hRs n m]
    ring
  rw [hA, hB, hOff]
  congr 1
  congr 1
  apply sum_congr rfl
  intro n hn
  exact hInner n hn


/-- Normalized individual spacing eigenvectors give the exact weighted energy split.
MV1974 page 80 displays 3.10 to 3.17, after multiplication by individual spacing. -/
theorem mv1974_weighted_eigen_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K C : ι → ι → ℝ) (hK : ∀ m n, K n m = -K m n)
    (hprod : ∀ m n p, m ≠ n → m ≠ p → n ≠ p →
      K m n*K m p = K n p*(C m n-C m p))
    (δ : ι → ℝ) (hδ : ∀ m, 0 < δ m) (u : ι → ℂ) (μ : ℝ)
    (hnorm : ∑ m, ‖u m‖^2/δ m = 1)
    (heig : ∀ m, ∑ n ∈ univ.erase m, (K m n : ℂ)*u n =
      ((μ/δ m : ℝ) : ℂ)*I*u m) :
    μ^2 = (∑ m, δ m * ∑ n ∈ univ.erase m, K m n^2*‖u n‖^2) +
      2*∑ m, ∑ n ∈ univ.erase m,
        δ m*C m n*K m n*(u m*conj (u n)).re := by
  have hid (m : ι) := mv1974_eigen_identity K C hK hprod u (fun m => μ/δ m) heig m
  calc
    μ^2 = ∑ m, δ m*((μ/δ m)^2*‖u m‖^2) := by
      calc
        μ^2 = μ^2 * ∑ m, ‖u m‖^2/δ m := by rw [hnorm, mul_one]
        _ = _ := by
          rw [mul_sum]
          apply sum_congr rfl
          intro m hm
          field_simp [(hδ m).ne']
    _ = ∑ m, δ m*((∑ n ∈ univ.erase m, K m n^2*‖u n‖^2) +
        2*∑ n ∈ univ.erase m, C m n*K m n*(u m*conj (u n)).re) := by
      apply sum_congr rfl
      intro m hm
      rw [hid]
    _ = _ := by
      simp_rw [mul_add, mul_sum, sum_add_distrib]
      ring

/-- The quadratic estimate for T6 in MV1974 page 81 implies T6 at most 17 times k. -/
theorem mv1974_quadratic_bound {t k : ℝ} (hk : 0 ≤ k)
    (h : t^2 ≤ 14*k^2+16*k*t) : t ≤ 17*k := by
  by_contra hn
  have ht : 0 < t-17*k := by linarith
  have hp : 0 < t+k := by linarith
  nlinarith [mul_pos ht hp, sq_nonneg k]
/-- The last scalar step for individual spacing eigenvalues in MV1974 page 81.
The separate analytic estimates for T1 and T2 remain hypotheses. -/
theorem mv1974_normalized_bound {z a t : ℝ} (hz : 0 ≤ z)
    (h : z^2 ≤ a+t) (ha : a ≤ 4/Real.pi^2)
    (ht : t ≤ 17/Real.pi^2) : z ≤ 3/2 := by
  have hpi : 28/3 < Real.pi^2 := by nlinarith [Real.pi_gt_d2]
  have hsum : a+t ≤ 21/Real.pi^2 := by
    calc
      a+t ≤ 4/Real.pi^2+17/Real.pi^2 := add_le_add ha ht
      _ = _ := by ring
  have hsmall : 21/Real.pi^2 < (3/2:ℝ)^2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith
  nlinarith

/-- Weighted Cauchy in the normalization of MV1974 page 80 display 3.11. -/
theorem mv1974_weighted_cauchy {ι : Type*} (R : Finset ι)
    (δ a v : ι → ℝ) (hδ : ∀ r ∈ R, 0 < δ r)
    (hnorm : ∑ r ∈ R, a r^2/δ r = 1) :
    (∑ r ∈ R, a r*v r)^2 ≤ ∑ r ∈ R, δ r*v r^2 := by
  have hs := sum_mul_sq_le_sq_mul_sq R (fun r => a r/Real.sqrt (δ r))
    (fun r => Real.sqrt (δ r)*v r)
  have hleft : ∑ r ∈ R, a r/Real.sqrt (δ r)*(Real.sqrt (δ r)*v r) =
      ∑ r ∈ R, a r*v r := by
    apply sum_congr rfl
    intro r hr
    field_simp [(Real.sqrt_pos.mpr (hδ r hr)).ne']
  have hnorm' : ∑ r ∈ R, (a r/Real.sqrt (δ r))^2 = 1 := by
    convert hnorm using 1
    apply sum_congr rfl
    intro r hr
    rw [div_pow, Real.sq_sqrt (hδ r hr).le]
  have hright : ∑ r ∈ R, (Real.sqrt (δ r)*v r)^2 =
      ∑ r ∈ R, δ r*v r^2 := by
    apply sum_congr rfl
    intro r hr
    rw [mul_pow, Real.sq_sqrt (hδ r hr).le]
  simpa only [hleft, hnorm', hright, one_mul] using hs
/-- The fourth and mixed moment bounds imply the quadratic estimate on MV1974 page 81.
The two analytic kernel estimates remain explicit hypotheses. -/
theorem mv1974_mixed_moment_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ) (hK : ∀ r s, K s r^2 = K r s^2)
    (δ a : ι → ℝ) (hδ : ∀ r, 0 < δ r) (ha : ∀ r, 0 ≤ a r)
    (hnorm : ∑ r, a r^2/δ r = 1) (k : ℝ) (hk : 0 ≤ k)
    (hfourth : ∀ s, ∑ r, δ r*K r s^4 ≤ (7/2)*k^2/δ s^3)
    (hmixed : ∀ s t, s ≠ t →
      ∑ r, δ r*K r s^2*K r t^2 ≤ 4*k*(1/δ s+1/δ t)*K s t^2) :
    (∑ r, ∑ s, a r*a s*(δ r+δ s)*K r s^2)^2 ≤
      14*k^2+16*k*(∑ r, ∑ s, a r*a s*(δ r+δ s)*K r s^2) := by
  let v (r : ι) := ∑ s, a s*δ s*K r s^2
  let T := ∑ r, ∑ s, a r*a s*(δ r+δ s)*K r s^2
  let S := ∑ r, δ r*(v r)^2
  have hswap : (∑ r, ∑ s, a r*a s*δ r*K r s^2) =
      ∑ r, ∑ s, a r*a s*δ s*K r s^2 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro r hr
    apply sum_congr rfl
    intro s hs
    rw [hK]
    ring
  have hT : T = 2*∑ r, a r*v r := by
    calc
      T = (∑ r, ∑ s, a r*a s*δ r*K r s^2) +
          ∑ r, ∑ s, a r*a s*δ s*K r s^2 := by
        simp only [T, ← sum_add_distrib]
        apply sum_congr rfl
        intro r hr
        apply sum_congr rfl
        intro s hs
        ring
      _ = 2*∑ r, a r*v r := by
        rw [hswap, ← two_mul]
        congr 1
        dsimp [v]
        simp_rw [mul_sum]
        apply sum_congr rfl
        intro r hr
        apply sum_congr rfl
        intro s hs
        ring
  have hCS : (T/2)^2 ≤ S := by
    rw [hT]
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] using
      mv1974_weighted_cauchy univ δ a v (fun r _ => hδ r) hnorm
  have hS : S = ∑ s, ∑ t, a s*a t*δ s*δ t*
      ∑ r, δ r*K r s^2*K r t^2 := by
    calc
      S = ∑ r, ∑ s, ∑ t, a s*a t*δ s*δ t*(δ r*K r s^2*K r t^2) := by
        dsimp [S, v]
        simp only [sq, sum_mul, mul_sum]
        apply sum_congr rfl
        intro r hr
        apply sum_congr rfl
        intro s hs
        apply sum_congr rfl
        intro t ht
        ring
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro s hs
        rw [sum_comm]
        apply sum_congr rfl
        intro t ht
        rw [mul_sum]
  have hdiag (s : ι) :
      a s*a s*δ s*δ s*(∑ r, δ r*K r s^2*K r s^2) ≤
        (7/2)*k^2*(a s^2/δ s) := by
    have hker : (∑ r, δ r*K r s^2*K r s^2) = ∑ r, δ r*K r s^4 := by
      apply sum_congr rfl
      intro r hr
      ring
    rw [hker]
    have h := mul_le_mul_of_nonneg_left (hfourth s)
      (show 0 ≤ a s*a s*δ s*δ s by nlinarith [sq_nonneg (a s*δ s)])
    refine h.trans_eq ?_
    field_simp [(hδ s).ne']
  have hoff (s t : ι) (hne : t ≠ s) :
      a s*a t*δ s*δ t*(∑ r, δ r*K r s^2*K r t^2) ≤
        4*k*(a s*a t*(δ s+δ t)*K s t^2) := by
    have has := ha s
    have hat := ha t
    have hds := (hδ s).le
    have hdt := (hδ t).le
    have h := mul_le_mul_of_nonneg_left (hmixed s t hne.symm)
      (show 0 ≤ a s*a t*δ s*δ t by positivity)
    refine h.trans_eq ?_
    field_simp [(hδ s).ne', (hδ t).ne']
    ring
  have hbound : S ≤ (7/2)*k^2+4*k*T := by
    rw [hS]
    calc
      _ = ∑ s, (a s*a s*δ s*δ s*(∑ r, δ r*K r s^2*K r s^2) +
          ∑ t ∈ univ.erase s, a s*a t*δ s*δ t*(∑ r, δ r*K r s^2*K r t^2)) := by
        apply sum_congr rfl
        intro s hs
        exact (add_sum_erase univ _ (mem_univ s)).symm
      _ ≤ ∑ s, ((7/2)*k^2*(a s^2/δ s) +
          ∑ t ∈ univ.erase s, 4*k*(a s*a t*(δ s+δ t)*K s t^2)) := by
        apply sum_le_sum
        intro s hs
        apply add_le_add (hdiag s)
        exact sum_le_sum (fun t ht => hoff s t (ne_of_mem_erase ht))
      _ ≤ ∑ s, ((7/2)*k^2*(a s^2/δ s) +
          ∑ t, 4*k*(a s*a t*(δ s+δ t)*K s t^2)) := by
        apply sum_le_sum
        intro s hs
        apply add_le_add le_rfl
        apply sum_le_sum_of_subset_of_nonneg (erase_subset s univ)
        intro t ht hts
        have has := ha s
        have hat := ha t
        have hds := (hδ s).le
        have hdt := (hδ t).le
        positivity
      _ = _ := by
        rw [sum_add_distrib, ← mul_sum, hnorm, mul_one]
        dsimp [T]
        simp_rw [← mul_sum]
  change T^2 ≤ 14*k^2+16*k*T
  nlinarith

/-- MV1974 page 81 closes the normalized weighted eigenvalue estimate from
its second, fourth and mixed kernel moments. The moment estimates stay explicit. -/
theorem mv1974_weighted_eigen_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K C : ι → ι → ℝ) (hK : ∀ r s, K s r = -K r s)
    (hprod : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      K r s*K r t = K s t*(C r s-C r t))
    (hCK : ∀ r s, |C r s*K r s| ≤ K r s^2)
    (δ : ι → ℝ) (hδ : ∀ r, 0 < δ r) (u : ι → ℂ) (μ : ℝ)
    (hnorm : ∑ r, ‖u r‖^2/δ r = 1)
    (heig : ∀ r, ∑ s ∈ univ.erase r, (K r s : ℂ)*u s =
      ((μ/δ r : ℝ) : ℂ)*I*u r)
    (hsecond : ∀ s, ∑ r, δ r*K r s^2 ≤ (4/Real.pi^2)/δ s)
    (hfourth : ∀ s, ∑ r, δ r*K r s^4 ≤ (7/2)*(1/Real.pi^2)^2/δ s^3)
    (hmixed : ∀ s t, s ≠ t →
      ∑ r, δ r*K r s^2*K r t^2 ≤
        4*(1/Real.pi^2)*(1/δ s+1/δ t)*K s t^2) :
    |μ| ≤ 3/2 := by
  let a (r : ι) := ‖u r‖
  let T := ∑ r, ∑ s, a r*a s*(δ r+δ s)*K r s^2
  let D := ∑ r, δ r * ∑ s ∈ univ.erase r, K r s^2*‖u s‖^2
  let E := 2*∑ r, ∑ s ∈ univ.erase r,
    δ r*C r s*K r s*(u r*conj (u s)).re
  have hKsq (r s : ι) : K s r^2 = K r s^2 := by rw [hK, neg_sq]
  have hT : T ≤ 17*(1/Real.pi^2) :=
    mv1974_quadratic_bound (by positivity)
      (mv1974_mixed_moment_bound K hKsq δ a hδ (fun r => norm_nonneg _) hnorm
        (1/Real.pi^2) (by positivity) hfourth hmixed)
  have hD : D ≤ 4/Real.pi^2 := by
    calc
      D ≤ ∑ r, ∑ s, δ r*K r s^2*‖u s‖^2 := by
        dsimp [D]
        apply sum_le_sum
        intro r hr
        rw [mul_sum]
        simp_rw [← mul_assoc]
        apply sum_le_sum_of_subset_of_nonneg (erase_subset r univ)
        intro s hs hsr
        have hdr := (hδ r).le
        positivity
      _ = ∑ s, ‖u s‖^2 * ∑ r, δ r*K r s^2 := by
        rw [sum_comm]
        apply sum_congr rfl
        intro s hs
        rw [mul_sum]
        apply sum_congr rfl
        intro r hr
        ring
      _ ≤ ∑ s, ‖u s‖^2*((4/Real.pi^2)/δ s) := by
        exact sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hsecond s) (sq_nonneg _))
      _ = 4/Real.pi^2 := by
        calc
          _ = (4/Real.pi^2)*∑ s, ‖u s‖^2/δ s := by
            rw [mul_sum]
            apply sum_congr rfl
            intro s hs
            ring
          _ = _ := by rw [hnorm, mul_one]
  have hsym : (∑ r, ∑ s, a r*a s*δ r*K r s^2) =
      ∑ r, ∑ s, a r*a s*δ s*K r s^2 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro r hr
    apply sum_congr rfl
    intro s hs
    rw [hKsq]
    ring
  have hE : E ≤ T := by
    calc
      E ≤ 2*∑ r, ∑ s ∈ univ.erase r, a r*a s*δ r*K r s^2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply sum_le_sum
        intro r hr
        apply sum_le_sum
        intro s hs
        have hre : |(u r*conj (u s)).re| ≤ a r*a s := by
          simpa only [a, norm_mul, Complex.norm_conj] using
            Complex.abs_re_le_norm (u r*conj (u s))
        have hh : C r s*K r s*(u r*conj (u s)).re ≤ K r s^2*(a r*a s) := by
          calc
            _ ≤ |C r s*K r s*(u r*conj (u s)).re| := le_abs_self _
            _ = |C r s*K r s| * |(u r*conj (u s)).re| := abs_mul _ _
            _ ≤ _ := mul_le_mul (hCK r s) hre (abs_nonneg _) (sq_nonneg _)
        have hh' := mul_le_mul_of_nonneg_left hh (hδ r).le
        nlinarith only [hh']
      _ ≤ 2*∑ r, ∑ s, a r*a s*δ r*K r s^2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply sum_le_sum
        intro r hr
        apply sum_le_sum_of_subset_of_nonneg (erase_subset r univ)
        intro s hs hsr
        have hdr := (hδ r).le
        have har : 0 ≤ a r := norm_nonneg _
        have has : 0 ≤ a s := norm_nonneg _
        positivity
      _ = T := by
        calc
          _ = (∑ r, ∑ s, a r*a s*δ r*K r s^2) +
              ∑ r, ∑ s, a r*a s*δ s*K r s^2 := by rw [← hsym, two_mul]
          _ = T := by
            simp only [T, ← sum_add_distrib]
            apply sum_congr rfl
            intro r hr
            apply sum_congr rfl
            intro s hs
            ring
  have henergy : μ^2 = D+E := mv1974_weighted_eigen_energy K C hK hprod δ hδ u μ hnorm heig
  apply mv1974_normalized_bound (abs_nonneg μ) (a := D) (t := T)
  · rw [sq_abs, henergy]
    linarith
  · exact hD
  · simpa only [one_div, div_eq_mul_inv, one_mul] using hT

/-- The three individual spacing moment estimates imply the weighted skew form bound.
MV1974 pages 80 and 81, weighted spectral assembly for display 1.3.
The second, fourth and mixed kernel moment estimates remain explicit hypotheses. -/
theorem mv1974_weighted_form_of_moments {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K C : ι → ι → ℝ) (hK : ∀ r s, K s r = -K r s)
    (hprod : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      K r s*K r t = K s t*(C r s-C r t))
    (hCK : ∀ r s, |C r s*K r s| ≤ K r s^2)
    (δ : ι → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsecond : ∀ s, ∑ r, δ r*K r s^2 ≤ (4/Real.pi^2)/δ s)
    (hfourth : ∀ s, ∑ r, δ r*K r s^4 ≤ (7/2)*(1/Real.pi^2)^2/δ s^3)
    (hmixed : ∀ s t, s ≠ t →
      ∑ r, δ r*K r s^2*K r t^2 ≤
        4*(1/Real.pi^2)*(1/δ s+1/δ t)*K s t^2)
    (b : ι → ℂ) :
    ‖∑ r, ∑ s ∈ univ.erase r, b r*conj (b s)*(K r s : ℂ)‖ ≤
      3/2*∑ r, ‖b r‖^2/δ r := by
  let d (r : ι) : ℝ := Real.sqrt (δ r)
  let L (r s : ι) : ℝ := d r*d s*K r s
  have hd (r : ι) : 0 < d r := Real.sqrt_pos.mpr (hδ r)
  have hd2 (r : ι) : d r^2 = δ r := Real.sq_sqrt (hδ r).le
  have hdC (r : ι) : (d r : ℂ) ≠ 0 := by exact_mod_cast (hd r).ne'
  have hLs (r s : ι) : L s r = -L r s := by dsimp [L]; rw [hK]; ring
  have hL0 (r : ι) : L r r = 0 := by
    have h := hK r r
    have h0 : K r r = 0 := by linarith
    simp [L, h0]
  have hb (v : ι → ℂ) (hv : ∑ r, ‖v r‖^2 = 1) (μ : ℝ)
      (heig : ∀ r, ∑ s ∈ univ.erase r, (L r s : ℂ)*v s = (μ : ℂ)*I*v r) :
      |μ| ≤ 3/2 := by
    let u (r : ι) := (d r : ℂ)*v r
    have hu : ∑ r, ‖u r‖^2/δ r = 1 := by
      convert hv using 1
      apply sum_congr rfl
      intro r hr
      simp only [u, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hd r).le, mul_pow, hd2]
      field_simp [(hδ r).ne']
    have he (r : ι) : ∑ s ∈ univ.erase r, (K r s : ℂ)*u s =
        ((μ/δ r : ℝ) : ℂ)*I*u r := by
      apply mul_left_cancel₀ (hdC r)
      calc
        (d r : ℂ)*(∑ s ∈ univ.erase r, (K r s : ℂ)*u s) =
            ∑ s ∈ univ.erase r, (L r s : ℂ)*v s := by
          rw [mul_sum]
          apply sum_congr rfl
          intro s hs
          dsimp [L, u]
          push_cast
          ring
        _ = (μ : ℂ)*I*v r := heig r
        _ = _ := by
          dsimp [u]
          push_cast
          have hd2C : (d r : ℂ)^2 = (δ r : ℂ) := by exact_mod_cast hd2 r
          have hδC : (δ r : ℂ) ≠ 0 := by exact_mod_cast (hδ r).ne'
          field_simp [hδC]
          rw [← hd2C]
    exact mv1974_weighted_eigen_bound K C hK hprod hCK δ hδ u μ hu he hsecond hfourth hmixed
  have h := LeanLab.Linnik.HilbertCosecant.form_bound_of_eigen_bound L hLs hL0 hb
    (fun r => b r/(d r : ℂ))
  have hnorm : ∑ r, ‖b r/(d r : ℂ)‖^2 = ∑ r, ‖b r‖^2/δ r := by
    apply sum_congr rfl
    intro r hr
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hd r).le, div_pow, hd2]
  rw [hnorm] at h
  convert h using 1
  congr 1
  apply sum_congr rfl
  intro r hr
  apply sum_congr rfl
  intro s hs
  dsimp [L]
  simp only [map_div₀, Complex.conj_ofReal, Complex.ofReal_mul]
  field_simp [hdC r, hdC s]

/-- The individual spacing cosecant form follows from the three explicit kernel moments.
MV1974 pages 76 to 81, Lemmas 2, 4 and 5 and the proof of display 1.3.
The analytic moment estimates remain hypotheses. -/
theorem mv1974_cosecant_of_moments {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x δ : ι → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s → δ r ≤ LeanLab.PNTPort.LargeSieve.dist0 (x r-x s))
    (hsecond : ∀ s, ∑ r, δ r/(Real.sin (Real.pi*(x r-x s)))^2 ≤ (4/Real.pi^2)/δ s)
    (hfourth : ∀ s, ∑ r, δ r/(Real.sin (Real.pi*(x r-x s)))^4 ≤
      (7/2)*(1/Real.pi^2)^2/δ s^3)
    (hmixed : ∀ s t, s ≠ t →
      ∑ r, δ r/((Real.sin (Real.pi*(x r-x s)))^2*(Real.sin (Real.pi*(x r-x t)))^2) ≤
        4*(1/Real.pi^2)*(1/δ s+1/δ t)/(Real.sin (Real.pi*(x s-x t)))^2)
    (b : ι → ℂ) :
    ‖∑ r, ∑ s ∈ univ.erase r,
      b r*conj (b s)/(Real.sin (Real.pi*(x r-x s)) : ℂ)‖ ≤
      3/2*∑ r, ‖b r‖^2/δ r := by
  let K (r s : ι) : ℝ := 1/Real.sin (Real.pi*(x r-x s))
  let C (r s : ι) : ℝ := Real.cos (Real.pi*(x r-x s))/Real.sin (Real.pi*(x r-x s))
  have hK (r s : ι) : K s r = -K r s := by
    dsimp [K]
    rw [show Real.pi*(x s-x r) = -(Real.pi*(x r-x s)) by ring, Real.sin_neg]
    simp
  have hsin (r s : ι) (hne : r ≠ s) : Real.sin (Real.pi*(x r-x s)) ≠ 0 :=
    LeanLab.Linnik.HilbertCosecant.sin_ne_zero_of_dist0_pos ((hδ r).trans_le (hsep r s hne))
  have hprod (r s t : ι) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
      K r s*K r t = K s t*(C r s-C r t) := by
    have h := LeanLab.Linnik.HilbertCosecant.cosecant_product
      (a := Real.pi*x r) (b := Real.pi*x s) (c := Real.pi*x t)
      (by rw [← mul_sub]; exact hsin r s hrs)
      (by rw [← mul_sub]; exact hsin r t hrt)
      (by rw [← mul_sub]; exact hsin s t hst)
    simpa only [← mul_sub] using h
  have hCK (r s : ι) : |C r s*K r s| ≤ K r s^2 := by
    have he : C r s*K r s = Real.cos (Real.pi*(x r-x s))*K r s^2 := by
      dsimp [C, K]
      ring
    rw [he, abs_mul, abs_sq]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (sq_nonneg _)).trans_eq (one_mul _)
  have hh := mv1974_weighted_form_of_moments K C hK hprod hCK δ hδ
    (by simpa only [K, div_eq_mul_inv, mul_inv, mul_assoc, one_mul, inv_pow] using hsecond)
    (by simpa only [K, div_eq_mul_inv, mul_inv, mul_assoc, one_mul, inv_pow] using hfourth)
    (by
      intro s t hst
      simpa only [K, div_eq_mul_inv, mul_inv, mul_assoc, one_mul, inv_pow] using hmixed s t hst) b
  convert hh using 1
  congr 1
  apply sum_congr rfl
  intro r hr
  apply sum_congr rfl
  intro s hs
  simp [K, div_eq_mul_inv]

/-- Derivative of the cotangent kernel used in MV1974 pages 76 and 77. -/
theorem mv1974_hasDerivAt_cot (t : ℝ) (hs : Real.sin (Real.pi*t) ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.cos (Real.pi*x)/Real.sin (Real.pi*x))
      (-Real.pi/(Real.sin (Real.pi*t))^2) t := by
  have hlin := (hasDerivAt_id t).const_mul Real.pi
  have h := ((Real.hasDerivAt_cos (Real.pi*t)).comp t hlin).div
    ((Real.hasDerivAt_sin (Real.pi*t)).comp t hlin) hs
  simp only [Function.comp_apply, mul_one] at h
  change HasDerivAt (fun x : ℝ => Real.cos (Real.pi*x)/Real.sin (Real.pi*x))
    ((-Real.sin (Real.pi*t)*Real.pi*Real.sin (Real.pi*t)-
      Real.cos (Real.pi*t)*(Real.cos (Real.pi*t)*Real.pi))/(Real.sin (Real.pi*t))^2) t at h
  have hn : -Real.sin (Real.pi*t)*Real.pi*Real.sin (Real.pi*t)-
      Real.cos (Real.pi*t)*(Real.cos (Real.pi*t)*Real.pi) = -Real.pi := by
    calc
      _ = -Real.pi*((Real.sin (Real.pi*t))^2+(Real.cos (Real.pi*t))^2) := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]
  rwa [hn] at h
/-- The cosecant square primitive in MV1974 page 76 Lemma 2. -/
theorem mv1974_integral_cosecant_sq (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ t in a..b, 1/(Real.sin (Real.pi*t))^2) =
      (Real.cos (Real.pi*a)/Real.sin (Real.pi*a)-
        Real.cos (Real.pi*b)/Real.sin (Real.pi*b))/Real.pi := by
  have hs (t : ℝ) (ht : t ∈ Set.uIcc a b) : Real.sin (Real.pi*t) ≠ 0 := by
    rw [Set.uIcc_of_le hab] at ht
    exact (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (ha.trans_le ht.1))
      (by nlinarith [mul_pos Real.pi_pos (sub_pos.mpr (ht.2.trans_lt hb))])).ne'
  have hi : IntervalIntegrable (fun t : ℝ => 1/(Real.sin (Real.pi*t))^2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.pow 2)
      (fun t ht => pow_ne_zero 2 (hs t ht))
  have hd (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      HasDerivAt (fun x : ℝ => -(Real.cos (Real.pi*x)/Real.sin (Real.pi*x))/Real.pi)
        (1/(Real.sin (Real.pi*t))^2) t := by
    convert (mv1974_hasDerivAt_cot t (hs t ht)).neg.div_const Real.pi using 1
    field_simp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [h]
  ring

/-- The cosecant fourth power primitive in MV1974 page 77 Lemma 4. -/
theorem mv1974_integral_cosecant_fourth (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ t in a..b, 1/(Real.sin (Real.pi*t))^4) =
      ((Real.cos (Real.pi*a)/Real.sin (Real.pi*a) +
          (Real.cos (Real.pi*a)/Real.sin (Real.pi*a))^3/3) -
        (Real.cos (Real.pi*b)/Real.sin (Real.pi*b) +
          (Real.cos (Real.pi*b)/Real.sin (Real.pi*b))^3/3))/Real.pi := by
  have hs (t : ℝ) (ht : t ∈ Set.uIcc a b) : Real.sin (Real.pi*t) ≠ 0 := by
    rw [Set.uIcc_of_le hab] at ht
    exact (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (ha.trans_le ht.1))
      (by nlinarith [mul_pos Real.pi_pos (sub_pos.mpr (ht.2.trans_lt hb))])).ne'
  have hi : IntervalIntegrable (fun t : ℝ => 1/(Real.sin (Real.pi*t))^4) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.pow 4)
      (fun t ht => pow_ne_zero 4 (hs t ht))
  have hd (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      HasDerivAt (fun x : ℝ => -((Real.cos (Real.pi*x)/Real.sin (Real.pi*x)) +
        (Real.cos (Real.pi*x)/Real.sin (Real.pi*x))^3/3)/Real.pi)
        (1/(Real.sin (Real.pi*t))^4) t := by
    have hc := mv1974_hasDerivAt_cot t (hs t ht)
    convert (hc.add ((hc.pow 3).div_const 3)).neg.div_const Real.pi using 1
    norm_num
    field_simp [hs t ht]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi*t)]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [h]
  ring

/-- The complementary interval integral bound in MV1974 page 76 Lemma 2. -/
theorem mv1974_integral_cosecant_sq_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ t in (δ/2)..(1-δ/2), 1/(Real.sin (Real.pi*t))^2) <
      4/(Real.pi^2*δ) := by
  rcases lt_or_eq_of_le hδ1 with hlt | rfl
  · let t := Real.pi*δ/2
    have ht0 : 0 < t := by dsimp [t]; positivity
    have htpi : t < Real.pi/2 := by
      dsimp [t]
      nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hlt)]
    have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
    have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htpi⟩
    have htan := Real.lt_tan ht0 htpi
    rw [Real.tan_eq_sin_div_cos] at htan
    have htc : t*Real.cos t < Real.sin t := (lt_div_iff₀ hc).mp htan
    have hcot : Real.cos t/Real.sin t < 1/t := by
      apply (div_lt_div_iff₀ hs ht0).mpr
      simpa only [one_mul, mul_comm] using htc
    rw [mv1974_integral_cosecant_sq (δ/2) (1-δ/2) (by positivity) (by linarith) (by linarith)]
    have ha : Real.pi*(δ/2) = t := by dsimp [t]; ring
    have hb : Real.pi*(1-δ/2) = Real.pi-t := by dsimp [t]; ring
    rw [ha, hb, Real.sin_pi_sub, Real.cos_pi_sub]
    calc
      _ = (2/Real.pi)*(Real.cos t/Real.sin t) := by ring
      _ < (2/Real.pi)*(1/t) := mul_lt_mul_of_pos_left hcot (by positivity)
      _ = _ := by dsimp [t]; field_simp; ring
  · norm_num
    positivity

/-- Convexity of the square cosecant kernel in MV1974 page 76 Lemma 2. -/
theorem mv1974_convexOn_cosecant_sq :
    ConvexOn ℝ (Set.Ioo 0 1) (fun x : ℝ => 1/(Real.sin (Real.pi*x))^2) := by
  refine ⟨convex_Ioo 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hpx : Real.pi*x ∈ Set.Icc 0 Real.pi := by constructor <;> nlinarith [Real.pi_pos, hx.1, hx.2]
  have hpy : Real.pi*y ∈ Set.Icc 0 Real.pi := by constructor <;> nlinarith [Real.pi_pos, hy.1, hy.2]
  have hsx : 0 < Real.sin (Real.pi*x) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos hx.1) (by nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hx.2)])
  have hsy : 0 < Real.sin (Real.pi*y) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos hy.1) (by nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hy.2)])
  have hj := strictConcaveOn_sin_Icc.concaveOn.2 hpx hpy ha hb hab
  simp only [smul_eq_mul] at hj ⊢
  rw [show a*(Real.pi*x)+b*(Real.pi*y) = Real.pi*(a*x+b*y) by ring] at hj
  have hp : 0 < a*Real.sin (Real.pi*x)+b*Real.sin (Real.pi*y) := by
    simpa only [smul_eq_mul, Set.mem_Ioi] using (convex_Ioi (0:ℝ)) hsx hsy ha hb hab
  have hc := (convexOn_zpow (𝕜 := ℝ) (-2)).2 hsx hsy ha hb hab
  have hfirst : 1/(Real.sin (Real.pi*(a*x+b*y)))^2 ≤
      1/(a*Real.sin (Real.pi*x)+b*Real.sin (Real.pi*y))^2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos hp)
    exact pow_le_pow_left₀ hp.le hj 2
  refine hfirst.trans ?_
  simpa only [smul_eq_mul, zpow_neg, zpow_ofNat, one_div] using hc

/-- The local convex integral comparison in MV1974 page 76 Lemma 2. -/
theorem mv1974_local_cosecant_sq (c d : ℝ) (hd : 0 < d)
    (hl : 0 < c-d/2) (hr : c+d/2 < 1) :
    d/(Real.sin (Real.pi*c))^2 ≤
      ∫ t in (c-d/2)..(c+d/2), 1/(Real.sin (Real.pi*t))^2 := by
  let f (t : ℝ) := 1/(Real.sin (Real.pi*t))^2
  have hab : c-d/2 ≤ c+d/2 := by linarith
  have hs (t : ℝ) (ht : t ∈ Set.uIcc (c-d/2) (c+d/2)) : Real.sin (Real.pi*t) ≠ 0 := by
    rw [Set.uIcc_of_le hab] at ht
    exact (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (hl.trans_le ht.1))
      (by nlinarith [mul_pos Real.pi_pos (sub_pos.mpr (ht.2.trans_lt hr))])).ne'
  have hi : IntervalIntegrable f volume (c-d/2) (c+d/2) := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.pow 2)
      (fun t ht => pow_ne_zero 2 (hs t ht))
  have hA : 2*c-(c+d/2) = c-d/2 := by ring
  have hB : 2*c-(c-d/2) = c+d/2 := by ring
  have hi2 : IntervalIntegrable (fun t => f (2*c-t)) volume (c-d/2) (c+d/2) := by
    simpa only [hA, hB] using (hi.comp_sub_left (2*c)).symm
  have hp (t : ℝ) (ht : t ∈ Set.Icc (c-d/2) (c+d/2)) :
      2*f c ≤ f t+f (2*c-t) := by
    have hj := mv1974_convexOn_cosecant_sq.2
    have h := hj (x := t) (y := 2*c-t) (by constructor <;> linarith [ht.1, ht.2])
      (by constructor <;> linarith [ht.1, ht.2]) (a := 1/2) (b := 1/2)
      (by norm_num) (by norm_num) (by norm_num)
    simp only [smul_eq_mul] at h
    rw [show (1/2:ℝ)*t+(1/2)*(2*c-t) = c by ring] at h
    change 2*f c ≤ f t+f (2*c-t)
    change f c ≤ (1/2)*f t+(1/2)*f (2*c-t) at h
    linarith
  have hInt := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 2*f c) volume (c-d/2) (c+d/2)) (hi.add hi2) hp
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add hi hi2,
    intervalIntegral.integral_comp_sub_left, hA, hB] at hInt
  simp only [smul_eq_mul] at hInt
  have hdiff : (c+d/2)-(c-d/2) = d := by ring
  rw [hdiff] at hInt
  have hfinal : d*f c ≤ ∫ t in (c-d/2)..(c+d/2), f t := by nlinarith
  simpa only [f, div_eq_mul_inv, one_mul] using hfinal

end LeanLab.SchnirelmannBounds.Decomp1525b
