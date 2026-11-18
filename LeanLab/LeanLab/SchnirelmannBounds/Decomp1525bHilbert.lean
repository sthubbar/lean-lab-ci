/-
Montgomery and Vaughan, Hilbert's inequality, 1974 page 73 display 1.3.
https://doi.org/10.1112/jlms/s2-8.1.73
The individual spacing input for Decomp1525b is PROVED at the end of this file, burst 20261117.
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

/-! ### MV1974 display 1.3: Lemmas 2 to 5 and the halving argument

Burst 20261117. AI wrote the Lean code. Goldbach is open. -/

open LeanLab.PNTPort.LargeSieve

/-- Integrals over non overlapping subintervals of [a,b] sum to at most the integral over [a,b]. -/
theorem mv1974_interval_packing {κ : Type*} (T : Finset κ) (l u : κ → ℝ) (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hlu : ∀ r ∈ T, l r ≤ u r) (hin : ∀ r ∈ T, a ≤ l r ∧ u r ≤ b)
    (hdisj : ∀ r ∈ T, ∀ r' ∈ T, r ≠ r' → u r ≤ l r' ∨ u r' ≤ l r)
    (hf0 : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hint : IntervalIntegrable f volume a b) :
    ∑ r ∈ T, ∫ t in l r..u r, f t ≤ ∫ t in a..b, f t := by
  have hI : IntegrableOn f (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint
  have hsub : ∀ r ∈ T, Set.Ioc (l r) (u r) ⊆ Set.Ioc a b := fun r hr =>
    Set.Ioc_subset_Ioc (hin r hr).1 (hin r hr).2
  have hU : (⋃ r ∈ T, Set.Ioc (l r) (u r)) ⊆ Set.Ioc a b := Set.iUnion₂_subset hsub
  have hpw : Set.Pairwise (↑T) (Function.onFun Disjoint fun r => Set.Ioc (l r) (u r)) := by
    intro r hr r' hr' hne
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases hdisj r hr r' hr' hne with h | h
    · linarith [hx.2, hx'.1]
    · linarith [hx.1, hx'.2]
  have hsum : ∑ r ∈ T, ∫ t in l r..u r, f t =
      ∫ t in ⋃ r ∈ T, Set.Ioc (l r) (u r), f t := by
    rw [integral_biUnion_finset T (fun r _ => measurableSet_Ioc) hpw
      (fun r hr => hI.mono_set (hsub r hr))]
    exact Finset.sum_congr rfl fun r hr => intervalIntegral.integral_of_le (hlu r hr)
  rw [hsum, intervalIntegral.integral_of_le hab]
  apply setIntegral_mono_set hI
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun t ht => hf0 t (Set.Ioc_subset_Icc_self ht)
  · exact Filter.Eventually.of_forall hU

/-- Midpoint convexity gives the local integral comparison. -/
theorem mv1974_local_midpoint (f : ℝ → ℝ) (c d : ℝ) (hd : 0 ≤ d)
    (hi : IntervalIntegrable f volume (c-d/2) (c+d/2))
    (hmid : ∀ t ∈ Set.Icc (c-d/2) (c+d/2), 2*f c ≤ f t + f (2*c-t)) :
    d*f c ≤ ∫ t in (c-d/2)..(c+d/2), f t := by
  have hab : c-d/2 ≤ c+d/2 := by linarith
  have hA : 2*c-(c+d/2) = c-d/2 := by ring
  have hB : 2*c-(c-d/2) = c+d/2 := by ring
  have hi2 : IntervalIntegrable (fun t => f (2*c-t)) volume (c-d/2) (c+d/2) := by
    simpa only [hA, hB] using (hi.comp_sub_left (2*c)).symm
  have hInt := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 2*f c) volume (c-d/2) (c+d/2))
    (hi.add hi2) hmid
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add hi hi2,
    intervalIntegral.integral_comp_sub_left, hA, hB] at hInt
  simp only [smul_eq_mul] at hInt
  have hdiff : (c+d/2)-(c-d/2) = d := by ring
  rw [hdiff] at hInt
  nlinarith

/-- MV1974 Lemma 2 for points in the open unit interval. -/
theorem mv1974_line_second {κ : Type*} (T : Finset κ) (c δ : κ → ℝ) (D : ℝ) (hD : 0 < D)
    (hδ : ∀ r ∈ T, 0 < δ r)
    (hlo : ∀ r ∈ T, δ r ≤ c r ∧ D ≤ c r)
    (hhi : ∀ r ∈ T, c r ≤ 1 - δ r ∧ c r ≤ 1 - D)
    (hsp : ∀ r ∈ T, ∀ r' ∈ T, r ≠ r' → δ r ≤ |c r - c r'|) :
    ∑ r ∈ T, δ r/(Real.sin (Real.pi*c r))^2 ≤ (4/Real.pi^2)/D := by
  rcases T.eq_empty_or_nonempty with rfl | ⟨r₀, hr₀⟩
  · simp only [Finset.sum_empty]
    positivity
  have hD1 : D ≤ 1 := by linarith [(hlo r₀ hr₀).2, (hhi r₀ hr₀).2]
  have hDhalf : D/2 ≤ 1-D/2 := by linarith
  have hs (t : ℝ) (ht : t ∈ Set.Icc (D/2) (1-D/2)) : 0 < Real.sin (Real.pi*t) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (by linarith [ht.1]))
      (by nlinarith [mul_pos Real.pi_pos (show 0 < 1 - t by linarith [ht.2])])
  have hint : IntervalIntegrable (fun t : ℝ => 1/(Real.sin (Real.pi*t))^2) volume
      (D/2) (1-D/2) := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_const.div
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.pow 2) ?_
    intro t ht
    rw [Set.uIcc_of_le hDhalf] at ht
    exact pow_ne_zero 2 (hs t ht).ne'
  have hpack := mv1974_interval_packing T (fun r => c r - δ r/2) (fun r => c r + δ r/2)
    (fun t : ℝ => 1/(Real.sin (Real.pi*t))^2) (D/2) (1-D/2) hDhalf
    (fun r hr => by linarith [hδ r hr])
    (fun r hr => ⟨by linarith [(hlo r hr).1, (hlo r hr).2],
      by linarith [(hhi r hr).1, (hhi r hr).2]⟩)
    (fun r hr r' hr' hne => by
      have h1 := hsp r hr r' hr' hne
      have h2 := hsp r' hr' r hr (Ne.symm hne)
      rw [abs_sub_comm] at h2
      rcases le_total (c r) (c r') with h | h
      · left
        rw [abs_of_nonpos (by linarith)] at h1 h2
        linarith
      · right
        rw [abs_of_nonneg (by linarith)] at h1 h2
        linarith)
    (fun t ht => by have := hs t ht; positivity) hint
  have hterm : ∀ r ∈ T, δ r/(Real.sin (Real.pi*c r))^2 ≤
      ∫ t in (c r - δ r/2)..(c r + δ r/2), 1/(Real.sin (Real.pi*t))^2 := fun r hr =>
    mv1974_local_cosecant_sq (c r) (δ r) (hδ r hr)
      (by linarith [(hlo r hr).1, hδ r hr]) (by linarith [(hhi r hr).1, hδ r hr])
  have hb := mv1974_integral_cosecant_sq_bound D hD hD1
  calc ∑ r ∈ T, δ r/(Real.sin (Real.pi*c r))^2
      ≤ ∑ r ∈ T, ∫ t in (c r - δ r/2)..(c r + δ r/2), 1/(Real.sin (Real.pi*t))^2 :=
        Finset.sum_le_sum hterm
    _ ≤ ∫ t in (D/2)..(1-D/2), 1/(Real.sin (Real.pi*t))^2 := hpack
    _ ≤ 4/(Real.pi^2*D) := hb.le
    _ = (4/Real.pi^2)/D := by rw [div_div]

/-- Algebraic partial fraction identity behind `1/(sin^2 a sin^2 b)` with `a - b = θ`. -/
theorem mv1974_mixed_alg (sa ca sb cb P : ℝ) (hsa : sa ≠ 0) (hsb : sb ≠ 0)
    (hS : sa*cb - ca*sb ≠ 0) (hP : P ≠ 0) (h1 : sa^2+ca^2 = 1) (h2 : sb^2+cb^2 = 1) :
    (1/(P*(sa*cb - ca*sb)^2)) *
      (-(((-sa*P)*sa - ca*(ca*P))/sa^2) - (((-sb*P)*sb - cb*(cb*P))/sb^2) +
        (2*((ca*cb+sa*sb)/(sa*cb - ca*sb))) * (ca*P/sa - cb*P/sb)) = 1/(sa^2*sb^2) := by
  have e1 : -(((-sa*P)*sa - ca*(ca*P))/sa^2) = P/sa^2 := by
    have : -((-sa*P)*sa - ca*(ca*P)) = P*(sa^2+ca^2) := by ring
    rw [← neg_div, this, h1, mul_one]
  have e2 : (((-sb*P)*sb - cb*(cb*P))/sb^2) = -(P/sb^2) := by
    have : ((-sb*P)*sb - cb*(cb*P)) = -(P*(sb^2+cb^2)) := by ring
    rw [this, h2, mul_one, neg_div]
  rw [e1, e2]
  obtain ⟨S, hSd⟩ : ∃ S, S = sa*cb - ca*sb := ⟨_, rfl⟩
  rw [← hSd] at hS ⊢
  have e4 : ca*P/sa - cb*P/sb = -(P*S/(sa*sb)) := by
    rw [hSd]; field_simp; ring
  rw [e4]
  have e5 : (2*((ca*cb+sa*sb)/S)) * -(P*S/(sa*sb))
      = -(2*P*(ca*cb+sa*sb)/(sa*sb)) := by
    field_simp
  rw [e5]
  have e6 : P/sa^2 - -(P/sb^2) + -(2*P*(ca*cb+sa*sb)/(sa*sb))
      = P*S^2/(sa^2*sb^2) := by
    rw [hSd]; field_simp
    linear_combination (-sb^2)*h1 + (-sa^2)*h2
  rw [e6]
  field_simp

/-- The explicit primitive of `1/(sin^2 (π x) sin^2 (π (x-c)))` evaluated by the FTC. -/
theorem mv1974_mixed_piece (c u v : ℝ) (hc : Real.sin (Real.pi*c) ≠ 0) (huv : u ≤ v)
    (h : ∀ x ∈ Set.Icc u v, Real.sin (Real.pi*x) ≠ 0 ∧ Real.sin (Real.pi*(x-c)) ≠ 0) :
    (∫ x in u..v, 1/((Real.sin (Real.pi*x))^2*(Real.sin (Real.pi*(x-c)))^2)) =
      (1/(Real.pi*(Real.sin (Real.pi*c))^2)) *
        (-(Real.cos (Real.pi*v)/Real.sin (Real.pi*v))
          - Real.cos (Real.pi*(v-c))/Real.sin (Real.pi*(v-c))
          + (2*(Real.cos (Real.pi*c)/Real.sin (Real.pi*c))) *
            (Real.log (Real.sin (Real.pi*v)) - Real.log (Real.sin (Real.pi*(v-c))))) -
      (1/(Real.pi*(Real.sin (Real.pi*c))^2)) *
        (-(Real.cos (Real.pi*u)/Real.sin (Real.pi*u))
          - Real.cos (Real.pi*(u-c))/Real.sin (Real.pi*(u-c))
          + (2*(Real.cos (Real.pi*c)/Real.sin (Real.pi*c))) *
            (Real.log (Real.sin (Real.pi*u)) - Real.log (Real.sin (Real.pi*(u-c))))) := by
  have hI : Set.uIcc u v = Set.Icc u v := Set.uIcc_of_le huv
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => (1/(Real.pi*(Real.sin (Real.pi*c))^2)) *
        (-(Real.cos (Real.pi*x)/Real.sin (Real.pi*x))
          - Real.cos (Real.pi*(x-c))/Real.sin (Real.pi*(x-c))
          + (2*(Real.cos (Real.pi*c)/Real.sin (Real.pi*c))) *
            (Real.log (Real.sin (Real.pi*x)) - Real.log (Real.sin (Real.pi*(x-c))))))
  · intro x hx
    rw [hI] at hx
    obtain ⟨hsa, hsb⟩ := h x hx
    have ha : HasDerivAt (fun x : ℝ => Real.pi*x) Real.pi x := by
      simpa using (hasDerivAt_id x).const_mul Real.pi
    have hb : HasDerivAt (fun x : ℝ => Real.pi*(x-c)) Real.pi x := by
      simpa using ((hasDerivAt_id x).sub_const c).const_mul Real.pi
    have hsaD := ha.sin
    have hcaD := ha.cos
    have hsbD := hb.sin
    have hcbD := hb.cos
    have hcta := hcaD.div hsaD hsa
    have hctb := hcbD.div hsbD hsb
    have hla := hsaD.log hsa
    have hlb := hsbD.log hsb
    have hG := ((hcta.neg.sub hctb).add
      ((hla.sub hlb).const_mul (2*(Real.cos (Real.pi*c)/Real.sin (Real.pi*c))))).const_mul
        (1/(Real.pi*(Real.sin (Real.pi*c))^2))
    have hθ : Real.pi*c = Real.pi*x - Real.pi*(x-c) := by ring
    have hS : Real.sin (Real.pi*c) = Real.sin (Real.pi*x)*Real.cos (Real.pi*(x-c))
        - Real.cos (Real.pi*x)*Real.sin (Real.pi*(x-c)) := by
      rw [hθ, Real.sin_sub]
    have hC : Real.cos (Real.pi*c) = Real.cos (Real.pi*x)*Real.cos (Real.pi*(x-c))
        + Real.sin (Real.pi*x)*Real.sin (Real.pi*(x-c)) := by
      rw [hθ, Real.cos_sub]
    have key := mv1974_mixed_alg (Real.sin (Real.pi*x)) (Real.cos (Real.pi*x))
      (Real.sin (Real.pi*(x-c))) (Real.cos (Real.pi*(x-c))) Real.pi hsa hsb (hS ▸ hc)
      Real.pi_ne_zero (Real.sin_sq_add_cos_sq _) (Real.sin_sq_add_cos_sq _)
    rw [← hS, ← hC] at key
    exact hG.congr_deriv key
  · apply ContinuousOn.intervalIntegrable
    rw [hI]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    obtain ⟨hsa, hsb⟩ := h x hx
    positivity

/-- Cotangent decreases and the log sine term has the right sign. -/
theorem mv1974_mixed_bracket (θ α : ℝ) (hα : 0 < α) (h1 : α < θ) (h2 : θ + α < Real.pi) :
    (Real.cos (θ+α)/Real.sin (θ+α) - Real.cos (θ-α)/Real.sin (θ-α)) +
      (2*(Real.cos θ/Real.sin θ)) *
        (Real.log (Real.sin (θ-α)) - Real.log (Real.sin (θ+α))) ≤ 0 := by
  have hsp : 0 < Real.sin (θ+α) := Real.sin_pos_of_pos_of_lt_pi (by linarith) h2
  have hsm : 0 < Real.sin (θ-α) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have h2α : 0 < Real.sin (2*α) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have A : Real.cos (θ+α)/Real.sin (θ+α) - Real.cos (θ-α)/Real.sin (θ-α) ≤ 0 := by
    rw [div_sub_div _ _ hsp.ne' hsm.ne']
    apply div_nonpos_of_nonpos_of_nonneg _ (mul_pos hsp hsm).le
    have e : Real.sin (2*α) = Real.sin (θ+α)*Real.cos (θ-α) - Real.cos (θ+α)*Real.sin (θ-α) := by
      rw [← Real.sin_sub]; congr 1; ring
    nlinarith
  have hd : Real.sin (θ+α) - Real.sin (θ-α) = 2*Real.cos θ*Real.sin α := by
    rw [Real.sin_add, Real.sin_sub]; ring
  have B : (Real.cos θ/Real.sin θ) *
        (Real.log (Real.sin (θ-α)) - Real.log (Real.sin (θ+α))) ≤ 0 := by
    rcases le_total 0 (Real.cos θ) with hc | hc
    · apply mul_nonpos_of_nonneg_of_nonpos (div_nonneg hc hsθ.le)
      have : Real.sin (θ-α) ≤ Real.sin (θ+α) := by nlinarith [mul_nonneg hc hsα.le]
      linarith [Real.log_le_log hsm this]
    · apply mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hc hsθ.le)
      have : Real.sin (θ+α) ≤ Real.sin (θ-α) := by nlinarith [mul_nonneg (neg_nonneg.2 hc) hsα.le]
      linarith [Real.log_le_log hsp this]
  linarith

/-- `cot α ≤ 1/α` on `(0, π/2)`. -/
theorem mv1974_cot_le_inv (α : ℝ) (hα : 0 < α) (h2 : α < Real.pi/2) :
    Real.cos α/Real.sin α ≤ 1/α := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, h2⟩
  have ht := Real.lt_tan hα h2
  rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hc] at ht
  rw [div_le_div_iff₀ hs hα]
  linarith

theorem mv1974_mixed_integral (c p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : p+q ≤ c)
    (hc : c+p+q ≤ 1) :
    (∫ x in p..(c-q), 1/((Real.sin (Real.pi*x))^2*(Real.sin (Real.pi*(x-c)))^2)) +
      (∫ x in (c+q)..(1-p), 1/((Real.sin (Real.pi*x))^2*(Real.sin (Real.pi*(x-c)))^2)) ≤
      4*(1/Real.pi^2)*(1/(2*p)+1/(2*q))/(Real.sin (Real.pi*c))^2 := by
  have hπ := Real.pi_pos
  have sinpos : ∀ y : ℝ, 0 < y → y < 1 → 0 < Real.sin (Real.pi*y) := fun y h0 h1 =>
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have hsθ : 0 < Real.sin (Real.pi*c) := sinpos c (by linarith) (by linarith)
  have I1 := mv1974_mixed_piece c p (c-q) hsθ.ne' (by linarith) (by
    intro x hx
    refine ⟨(sinpos x (by linarith [hx.1]) (by linarith [hx.2])).ne', ?_⟩
    have : 0 < Real.sin (Real.pi*(c-x)) := sinpos _ (by linarith [hx.2]) (by linarith [hx.1])
    have e : Real.pi*(x-c) = -(Real.pi*(c-x)) := by ring
    rw [e, Real.sin_neg]; linarith)
  have I2 := mv1974_mixed_piece c (c+q) (1-p) hsθ.ne' (by linarith) (by
    intro x hx
    exact ⟨(sinpos x (by linarith [hx.1]) (by linarith [hx.2])).ne',
      (sinpos _ (by linarith [hx.1]) (by linarith [hx.2])).ne'⟩)
  rw [I1, I2]
  have a1 : Real.pi*(c-q) = Real.pi*c - Real.pi*q := by ring
  have a2 : Real.pi*(c-q-c) = -(Real.pi*q) := by ring
  have a3 : Real.pi*(p-c) = -(Real.pi*c - Real.pi*p) := by ring
  have a4 : Real.pi*(1-p) = Real.pi - Real.pi*p := by ring
  have a5 : Real.pi*(1-p-c) = Real.pi - (Real.pi*c + Real.pi*p) := by ring
  have a6 : Real.pi*(c+q) = Real.pi*c + Real.pi*q := by ring
  have a7 : Real.pi*(c+q-c) = Real.pi*q := by ring
  have s1 : Real.sin (Real.pi*(c-q)) = Real.sin (Real.pi*c - Real.pi*q) := by rw [a1]
  have c1 : Real.cos (Real.pi*(c-q)) = Real.cos (Real.pi*c - Real.pi*q) := by rw [a1]
  have s2 : Real.sin (Real.pi*(c-q-c)) = -Real.sin (Real.pi*q) := by rw [a2, Real.sin_neg]
  have c2 : Real.cos (Real.pi*(c-q-c)) = Real.cos (Real.pi*q) := by rw [a2, Real.cos_neg]
  have s3 : Real.sin (Real.pi*(p-c)) = -Real.sin (Real.pi*c - Real.pi*p) := by
    rw [a3, Real.sin_neg]
  have c3 : Real.cos (Real.pi*(p-c)) = Real.cos (Real.pi*c - Real.pi*p) := by
    rw [a3, Real.cos_neg]
  have s4 : Real.sin (Real.pi*(1-p)) = Real.sin (Real.pi*p) := by rw [a4, Real.sin_pi_sub]
  have c4 : Real.cos (Real.pi*(1-p)) = -Real.cos (Real.pi*p) := by rw [a4, Real.cos_pi_sub]
  have s5 : Real.sin (Real.pi*(1-p-c)) = Real.sin (Real.pi*c + Real.pi*p) := by
    rw [a5, Real.sin_pi_sub]
  have c5 : Real.cos (Real.pi*(1-p-c)) = -Real.cos (Real.pi*c + Real.pi*p) := by
    rw [a5, Real.cos_pi_sub]
  have s6 : Real.sin (Real.pi*(c+q)) = Real.sin (Real.pi*c + Real.pi*q) := by rw [a6]
  have c6 : Real.cos (Real.pi*(c+q)) = Real.cos (Real.pi*c + Real.pi*q) := by rw [a6]
  rw [s1, c1, s2, c2, s3, c3, s4, c4, s5, c5, s6, c6, a7]
  simp only [Real.log_neg_eq_log, div_neg, neg_div, neg_neg]
  have L : ∀ y z : ℝ, y < z → Real.pi*y < Real.pi*z := fun y z h =>
    mul_lt_mul_of_pos_left h hπ
  have l1 := L p c (by linarith)
  have l2 := L q c (by linarith)
  have l3 := L (c+p) 1 (by linarith)
  have l4 := L (c+q) 1 (by linarith)
  have l5 := L p (1/2) (by linarith)
  have l6 := L q (1/2) (by linarith)
  have Bα := mv1974_mixed_bracket (Real.pi*c) (Real.pi*p) (by positivity) l1 (by linarith)
  have Bβ := mv1974_mixed_bracket (Real.pi*c) (Real.pi*q) (by positivity) l2 (by linarith)
  have Cα := mv1974_cot_le_inv (Real.pi*p) (by positivity) (by linarith)
  have Cβ := mv1974_cot_le_inv (Real.pi*q) (by positivity) (by linarith)
  have hK : 0 ≤ 1/(Real.pi*(Real.sin (Real.pi*c))^2) := by positivity
  have hfin : 4*(1/Real.pi^2)*(1/(2*p)+1/(2*q))/(Real.sin (Real.pi*c))^2
      = (1/(Real.pi*(Real.sin (Real.pi*c))^2)) * (2*(1/(Real.pi*p)) + 2*(1/(Real.pi*q))) := by
    field_simp
    norm_num
  rw [hfin]
  have hb : (-(Real.cos (Real.pi*c - Real.pi*q)/Real.sin (Real.pi*c - Real.pi*q)) +
              Real.cos (Real.pi*q)/Real.sin (Real.pi*q) +
            2*(Real.cos (Real.pi*c)/Real.sin (Real.pi*c)) *
              (Real.log (Real.sin (Real.pi*c - Real.pi*q)) - Real.log (Real.sin (Real.pi*q))) -
          (-(Real.cos (Real.pi*p)/Real.sin (Real.pi*p)) +
              Real.cos (Real.pi*c - Real.pi*p)/Real.sin (Real.pi*c - Real.pi*p) +
            2*(Real.cos (Real.pi*c)/Real.sin (Real.pi*c)) *
              (Real.log (Real.sin (Real.pi*p)) - Real.log (Real.sin (Real.pi*c - Real.pi*p))))) +
      ((Real.cos (Real.pi*p)/Real.sin (Real.pi*p) +
              Real.cos (Real.pi*c + Real.pi*p)/Real.sin (Real.pi*c + Real.pi*p) +
            2*(Real.cos (Real.pi*c)/Real.sin (Real.pi*c)) *
              (Real.log (Real.sin (Real.pi*p)) - Real.log (Real.sin (Real.pi*c + Real.pi*p)))) -
          (-(Real.cos (Real.pi*c + Real.pi*q)/Real.sin (Real.pi*c + Real.pi*q)) -
              Real.cos (Real.pi*q)/Real.sin (Real.pi*q) +
            2*(Real.cos (Real.pi*c)/Real.sin (Real.pi*c)) *
              (Real.log (Real.sin (Real.pi*c + Real.pi*q)) - Real.log (Real.sin (Real.pi*q)))))
      ≤ 2*(1/(Real.pi*p)) + 2*(1/(Real.pi*q)) := by
    linarith
  have hm := mul_le_mul_of_nonneg_left hb hK
  linarith

/-- Quartic Taylor upper bound for the cosine on the nonnegative reals. -/
theorem mv1974_cos_le_quartic {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f (t : ℝ) := 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hd (t : ℝ) : deriv f t = Real.sin t - t + t ^ 3 / 6 := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hd]
    have h := Real.sin_ge_sub_cube (show 0 ≤ t by simp only [interior_Ici, Set.mem_Ioi] at ht; exact ht.le)
    linarith
  have h := hm (by simp) hx hx
  dsimp [f] at h
  simp only [Real.cos_zero] at h
  linarith

/-- MV1974 Lemma 3, display 2.1. -/
theorem mv1974_lemma3 (D : ℝ) (hD : 0 < D) (hD6 : D ≤ 1/6) :
    D/(Real.sin (Real.pi*D))^4 +
      (Real.cos (Real.pi*D)/Real.sin (Real.pi*D) +
        (Real.cos (Real.pi*D)/Real.sin (Real.pi*D))^3/3)/Real.pi ≤
      (7/4)*(1/Real.pi^2)^2/D^3 := by
  have hpi := Real.pi_pos
  set x := Real.pi*D with hx
  have hx0 : 0 < x := by positivity
  have hxu : x ≤ 0.5236 := by
    have := Real.pi_lt_d4
    have : x ≤ Real.pi*(1/6) := mul_le_mul_of_nonneg_left hD6 hpi.le
    linarith
  have hxpi : x < Real.pi/2 := by
    have : x ≤ Real.pi*(1/6) := mul_le_mul_of_nonneg_left hD6 hpi.le
    linarith
  set s := Real.sin x with hs
  set c := Real.cos x with hc
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith)
  have hc0 : 0 ≤ c := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hxpi.le⟩
  have hsl : x - x^3/6 ≤ s := Real.sin_ge_sub_cube hx0.le
  have hcu : c ≤ 1 - x^2/2 + x^4/24 := mv1974_cos_le_quartic hx0.le
  set y := x^2 with hy
  have hy0 : 0 < y := by positivity
  have hyu : y ≤ 0.2742 := by rw [hy]; nlinarith
  set p := x/s with hp
  set w := x*c/s with hw
  have hp0 : 0 ≤ p := by positivity
  have hw0 : 0 ≤ w := by positivity
  have hsl' : x*(1 - y/6) ≤ s := by rw [hy]; linarith
  -- p ≤ 1.048
  have hpu : p ≤ 1.048 := by
    rw [hp, div_le_iff₀ hs0]
    nlinarith
  have hp2 : p^2 ≤ 1.1 := by nlinarith
  have hp4 : p^4 ≤ 1.21 := by
    have : p^4 = (p^2)^2 := by ring
    rw [this]; nlinarith [sq_nonneg p]
  -- w ≤ 1 - y/3
  have hwu : w ≤ 1 - y/3 := by
    rw [hw, div_le_iff₀ hs0]
    have h1 : x*c ≤ x*(1 - y/2 + y^2/24) := by
      apply mul_le_mul_of_nonneg_left _ hx0.le
      rw [hy]; linarith [hcu, show (x^2)^2 = x^4 by ring]
    have h2 : (1 - y/3)*(x*(1-y/6)) ≤ (1 - y/3)*s :=
      mul_le_mul_of_nonneg_left hsl' (by linarith)
    nlinarith [mul_pos hx0 (mul_pos hy0 hy0)]
  have hw3 : w^3 ≤ (1 - y/3)^3 := pow_le_pow_left₀ hw0 hwu 3
  have hyw : y*w ≤ y*(1 - y/3) := mul_le_mul_of_nonneg_left hwu hy0.le
  have hpoly : y*(1 - y/3) + (1 - y/3)^3/3 ≤ 0.52 := by
    nlinarith [mul_pos hy0 hy0, mul_pos hy0 (mul_pos hy0 hy0)]
  have hmain : p^4 + y*w + w^3/3 ≤ 7/4 := by linarith
  have hDne := hD.ne'
  have hsne := hs0.ne'
  have hpine := hpi.ne'
  have heq : D/s^4 + (c/s + (c/s)^3/3)/Real.pi =
      (p^4 + y*w + w^3/3)*((1/Real.pi^2)^2/D^3) := by
    rw [hp, hw, hy, hx]
    field_simp
    ring
  rw [heq]
  have : (7/4)*(1/Real.pi^2)^2/D^3 = (7/4)*((1/Real.pi^2)^2/D^3) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right hmain (by positivity)

/-- One side of MV1974 Lemma 4. -/
theorem mv1974_line_fourth_half {κ : Type*} (T : Finset κ) (c δ : κ → ℝ) (D : ℝ) (hD : 0 < D)
    (hD6 : D ≤ 1/6) (hδ : ∀ r ∈ T, 0 < δ r) (hδ6 : ∀ r ∈ T, δ r ≤ 1/6)
    (hlo : ∀ r ∈ T, δ r ≤ c r ∧ D ≤ c r)
    (hhalf : ∀ r ∈ T, c r ≤ 1/2)
    (hsp : ∀ r ∈ T, ∀ r' ∈ T, r ≠ r' → δ r ≤ |c r - c r'|) :
    ∑ r ∈ T, δ r/(Real.sin (Real.pi*c r))^4 ≤ (7/4)*(1/Real.pi^2)^2/D^3 := by
  have hpi := Real.pi_pos
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]; positivity
  obtain ⟨m, hm, hmin⟩ := T.exists_min_image c hne
  set E := max D (δ m) with hE
  have hDE : D ≤ E := le_max_left _ _
  have hδE : δ m ≤ E := le_max_right _ _
  have hE0 : 0 < E := hD.trans_le hDE
  have hE6 : E ≤ 1/6 := max_le hD6 (hδ6 m hm)
  have hEc : E ≤ c m := max_le (hlo m hm).2 (hlo m hm).1
  have hsin0 : ∀ t : ℝ, 0 < t → t ≤ 1/2 → 0 < Real.sin (Real.pi*t) := fun t h0 h1 =>
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have hsinm : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 1/2 →
      Real.sin (Real.pi*a) ≤ Real.sin (Real.pi*b) := fun a b h0 hab hb =>
    Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) (by nlinarith)
      (mul_le_mul_of_nonneg_left hab hpi.le)
  have hganti : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 1/2 →
      1/(Real.sin (Real.pi*b))^4 ≤ 1/(Real.sin (Real.pi*a))^4 := fun a b h0 hab hb =>
    one_div_le_one_div_of_le (pow_pos (hsin0 a h0 (hab.trans hb)) 4)
      (pow_le_pow_left₀ (hsin0 a h0 (hab.trans hb)).le (hsinm a b h0 hab hb) 4)
  have hint : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 1/2 →
      IntervalIntegrable (fun t : ℝ => 1/(Real.sin (Real.pi*t))^4) volume a b := by
    intro a b h0 hab hb
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_const.div
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.pow 4)
      (fun t ht => pow_ne_zero 4 ?_)
    rw [Set.uIcc_of_le hab] at ht
    exact (hsin0 t (h0.trans_le ht.1) (ht.2.trans hb)).ne'
  -- the minimal term
  have hterm : δ m/(Real.sin (Real.pi*c m))^4 ≤ E/(Real.sin (Real.pi*E))^4 :=
    div_le_div₀ hE0.le hδE (pow_pos (hsin0 E hE0 (by linarith)) 4)
      (pow_le_pow_left₀ (hsin0 E hE0 (by linarith)).le (hsinm E (c m) hE0 hEc (hhalf m hm)) 4)
  -- the other terms
  have hlow : ∀ r ∈ T.erase m, E ≤ c r - δ r := by
    intro r hr
    have hrT := Finset.mem_of_mem_erase hr
    have h := hsp r hrT m hm (Finset.ne_of_mem_erase hr)
    rw [abs_of_nonneg (by linarith [hmin r hrT])] at h
    linarith
  have hrest : ∑ r ∈ T.erase m, δ r/(Real.sin (Real.pi*c r))^4 ≤
      ∫ t in E..(1/2), 1/(Real.sin (Real.pi*t))^4 := by
    calc ∑ r ∈ T.erase m, δ r/(Real.sin (Real.pi*c r))^4
        ≤ ∑ r ∈ T.erase m, ∫ t in (c r - δ r)..(c r), 1/(Real.sin (Real.pi*t))^4 := by
          apply Finset.sum_le_sum
          intro r hr
          have hrT := Finset.mem_of_mem_erase hr
          have hl := hlow r hr
          have hδr := hδ r hrT
          have hc : (∫ _t in (c r - δ r)..(c r), 1/(Real.sin (Real.pi*c r))^4) =
              δ r/(Real.sin (Real.pi*c r))^4 := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring
          rw [← hc]
          apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
            (hint _ _ (by linarith) (by linarith) (hhalf r hrT))
          intro t ht
          exact hganti t (c r) (by linarith [ht.1]) ht.2 (hhalf r hrT)
      _ ≤ _ := by
          apply mv1974_interval_packing (T.erase m) (fun r => c r - δ r) c
            (fun t : ℝ => 1/(Real.sin (Real.pi*t))^4) E (1/2) (by linarith)
          · intro r hr
            linarith [hδ r (Finset.mem_of_mem_erase hr)]
          · intro r hr
            exact ⟨hlow r hr, hhalf r (Finset.mem_of_mem_erase hr)⟩
          · intro r hr r' hr' hne'
            have hrT := Finset.mem_of_mem_erase hr
            have hrT' := Finset.mem_of_mem_erase hr'
            have h1 := hsp r hrT r' hrT' hne'
            have h2 := hsp r' hrT' r hrT (Ne.symm hne')
            rcases le_total (c r) (c r') with h | h
            · left
              rw [abs_of_nonneg (by linarith)] at h2
              linarith
            · right
              rw [abs_of_nonneg (by linarith)] at h1
              linarith
          · intro t ht
            positivity
          · exact hint E (1/2) hE0 (by linarith) le_rfl
  have hival : (∫ t in E..(1/2), 1/(Real.sin (Real.pi*t))^4) =
      (Real.cos (Real.pi*E)/Real.sin (Real.pi*E) +
        (Real.cos (Real.pi*E)/Real.sin (Real.pi*E))^3/3)/Real.pi := by
    rw [mv1974_integral_cosecant_fourth E (1/2) hE0 (by linarith) (by norm_num)]
    have : Real.pi*(1/2) = Real.pi/2 := by ring
    rw [this, Real.cos_pi_div_two]
    simp
  have h3 := mv1974_lemma3 E hE0 hE6
  have hfin : (7/4)*(1/Real.pi^2)^2/E^3 ≤ (7/4)*(1/Real.pi^2)^2/D^3 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hD.le hDE 3)
  rw [← Finset.add_sum_erase T _ hm]
  linarith

/-- MV1974 Lemma 4 for points in the open unit interval. -/
theorem mv1974_line_fourth {κ : Type*} (T : Finset κ) (c δ : κ → ℝ) (D : ℝ) (hD : 0 < D)
    (hD6 : D ≤ 1/6) (hδ : ∀ r ∈ T, 0 < δ r) (hδ6 : ∀ r ∈ T, δ r ≤ 1/6)
    (hlo : ∀ r ∈ T, δ r ≤ c r ∧ D ≤ c r)
    (hhi : ∀ r ∈ T, c r ≤ 1 - δ r ∧ c r ≤ 1 - D)
    (hsp : ∀ r ∈ T, ∀ r' ∈ T, r ≠ r' → δ r ≤ |c r - c r'|) :
    ∑ r ∈ T, δ r/(Real.sin (Real.pi*c r))^4 ≤ (7/2)*(1/Real.pi^2)^2/D^3 := by
  have h1 := mv1974_line_fourth_half (T.filter (fun r => c r ≤ 1/2)) c δ D hD hD6
    (fun r hr => hδ r (Finset.mem_filter.mp hr).1)
    (fun r hr => hδ6 r (Finset.mem_filter.mp hr).1)
    (fun r hr => hlo r (Finset.mem_filter.mp hr).1)
    (fun r hr => (Finset.mem_filter.mp hr).2)
    (fun r hr r' hr' hne => hsp r (Finset.mem_filter.mp hr).1 r' (Finset.mem_filter.mp hr').1 hne)
  have h2 := mv1974_line_fourth_half (T.filter (fun r => ¬ c r ≤ 1/2)) (fun r => 1 - c r) δ D
    hD hD6
    (fun r hr => hδ r (Finset.mem_filter.mp hr).1)
    (fun r hr => hδ6 r (Finset.mem_filter.mp hr).1)
    (fun r hr => by
      have := hhi r (Finset.mem_filter.mp hr).1
      constructor <;> linarith)
    (fun r hr => by
      have := (Finset.mem_filter.mp hr).2
      linarith [not_le.mp this])
    (fun r hr r' hr' hne => by
      have := hsp r (Finset.mem_filter.mp hr).1 r' (Finset.mem_filter.mp hr').1 hne
      have e : (1 - c r) - (1 - c r') = -(c r - c r') := by ring
      rw [e, abs_neg]
      exact this)
  have e : ∀ r, Real.sin (Real.pi*(1 - c r)) = Real.sin (Real.pi*c r) := fun r => by
    rw [mul_sub, mul_one, Real.sin_pi_sub]
  simp only [e] at h2
  rw [← Finset.sum_filter_add_sum_filter_not T (fun r => c r ≤ 1/2)]
  have : (7/2)*(1/Real.pi^2)^2/D^3 = 2*((7/4)*(1/Real.pi^2)^2/D^3) := by ring
  linarith

/-- The product formula sin (A - B) * sin (A + B) = sin A ^ 2 - sin B ^ 2. -/
theorem mv1974_sin_sub_mul_sin_add (A B : ℝ) :
    Real.sin (A - B) * Real.sin (A + B) = Real.sin A ^ 2 - Real.sin B ^ 2 := by
  rw [Real.sin_sub, Real.sin_add]
  have h1 := Real.cos_sq' A
  have h2 := Real.cos_sq' B
  linear_combination (Real.sin A) ^ 2 * h2 - (Real.sin B) ^ 2 * h1

/-- AM GM for inverse squares: if 0 < x * y ≤ z ^ 2 then 2 / z ^ 2 ≤ 1 / x ^ 2 + 1 / y ^ 2. -/
theorem mv1974_inv_sq_midpoint (x y z : ℝ) (hxy : 0 < x * y) (hz : x * y ≤ z ^ 2) :
    2 * (1 / z ^ 2) ≤ 1 / x ^ 2 + 1 / y ^ 2 := by
  have hx : x ≠ 0 := fun h => by simp [h] at hxy
  have hy : y ≠ 0 := fun h => by simp [h] at hxy
  have h1 : 1 / z ^ 2 ≤ 1 / (x * y) := one_div_le_one_div_of_le hxy hz
  have h2 : 1 / x ^ 2 + 1 / y ^ 2 - 2 * (1 / (x * y)) = (1 / x - 1 / y) ^ 2 := by
    field_simp
    ring
  nlinarith [sq_nonneg (1 / x - 1 / y)]

/-- One side of MV1974 Lemma 5: a Riemann sum at spaced midpoints is at most the integral,
for the integrand 1 / (sin (π x) ^ 2 * sin (π (x - C)) ^ 2) on an interval free of its poles. -/
theorem mv1974_mixed_side {κ : Type*} (S : Finset κ) (c δ : κ → ℝ) (C a b : ℝ) (hab : a ≤ b)
    (hpos : ∀ x ∈ Set.Icc a b, 0 < Real.sin (Real.pi * x))
    (hC : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      0 < Real.sin (Real.pi * (x - C)) * Real.sin (Real.pi * (y - C)))
    (hδ : ∀ r ∈ S, 0 < δ r)
    (hin : ∀ r ∈ S, a ≤ c r - δ r / 2 ∧ c r + δ r / 2 ≤ b)
    (hsp : ∀ r ∈ S, ∀ r' ∈ S, r ≠ r' → δ r ≤ |c r - c r'|) :
    ∑ r ∈ S, δ r / ((Real.sin (Real.pi * c r)) ^ 2 * (Real.sin (Real.pi * (c r - C))) ^ 2) ≤
      ∫ x in a..b, 1 / ((Real.sin (Real.pi * x)) ^ 2 * (Real.sin (Real.pi * (x - C))) ^ 2) := by
  set F : ℝ → ℝ :=
    fun x => 1 / ((Real.sin (Real.pi * x)) ^ 2 * (Real.sin (Real.pi * (x - C))) ^ 2) with hF
  have hne2 : ∀ x ∈ Set.Icc a b, Real.sin (Real.pi * (x - C)) ≠ 0 := fun x hx h => by
    have := hC x hx x hx
    rw [h] at this
    simp at this
  have hcont : ContinuousOn F (Set.Icc a b) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    exact mul_ne_zero (pow_ne_zero _ (hpos x hx).ne') (pow_ne_zero _ (hne2 x hx))
  have hint : IntervalIntegrable F volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have hF0 : ∀ x, 0 ≤ F x := fun x => by simp only [hF]; positivity
  have hsub : ∀ r ∈ S, Set.Icc (c r - δ r / 2) (c r + δ r / 2) ⊆ Set.Icc a b := fun r hr =>
    Set.Icc_subset_Icc (hin r hr).1 (hin r hr).2
  calc ∑ r ∈ S, δ r / ((Real.sin (Real.pi * c r)) ^ 2 * (Real.sin (Real.pi * (c r - C))) ^ 2)
      = ∑ r ∈ S, δ r * F (c r) := by
        apply Finset.sum_congr rfl
        intro r _
        simp only [hF]
        rw [div_eq_mul_one_div]
    _ ≤ ∑ r ∈ S, ∫ x in (c r - δ r / 2)..(c r + δ r / 2), F x := by
        apply Finset.sum_le_sum
        intro r hr
        have hd := hδ r hr
        apply mv1974_local_midpoint F (c r) (δ r) hd.le
        · apply hint.mono_set
          rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by linarith)]
          exact hsub r hr
        · intro u hu
          have hu' : 2 * c r - u ∈ Set.Icc (c r - δ r / 2) (c r + δ r / 2) :=
            ⟨by linarith [hu.2], by linarith [hu.1]⟩
          have hm : c r ∈ Set.Icc (c r - δ r / 2) (c r + δ r / 2) :=
            ⟨by linarith, by linarith⟩
          have hU := hsub r hr hu
          have hU' := hsub r hr hu'
          have e1 : Real.sin (Real.pi * u) * Real.sin (Real.pi * (2 * c r - u)) =
              Real.sin (Real.pi * c r) ^ 2 - Real.sin (Real.pi * (c r - u)) ^ 2 := by
            rw [← mv1974_sin_sub_mul_sin_add]
            congr 2 <;> ring
          have e2 : Real.sin (Real.pi * (u - C)) * Real.sin (Real.pi * (2 * c r - u - C)) =
              Real.sin (Real.pi * (c r - C)) ^ 2 - Real.sin (Real.pi * (c r - u)) ^ 2 := by
            rw [← mv1974_sin_sub_mul_sin_add]
            congr 2 <;> ring
          have p1 : 0 < Real.sin (Real.pi * u) * Real.sin (Real.pi * (2 * c r - u)) :=
            mul_pos (hpos u hU) (hpos _ hU')
          have p2 := hC u hU _ hU'
          have q1 : Real.sin (Real.pi * u) * Real.sin (Real.pi * (2 * c r - u)) ≤
              Real.sin (Real.pi * c r) ^ 2 := by
            rw [e1]; linarith [sq_nonneg (Real.sin (Real.pi * (c r - u)))]
          have q2 : Real.sin (Real.pi * (u - C)) * Real.sin (Real.pi * (2 * c r - u - C)) ≤
              Real.sin (Real.pi * (c r - C)) ^ 2 := by
            rw [e2]; linarith [sq_nonneg (Real.sin (Real.pi * (c r - u)))]
          have key := mv1974_inv_sq_midpoint
            (Real.sin (Real.pi * u) * Real.sin (Real.pi * (u - C)))
            (Real.sin (Real.pi * (2 * c r - u)) * Real.sin (Real.pi * (2 * c r - u - C)))
            (Real.sin (Real.pi * c r) * Real.sin (Real.pi * (c r - C)))
            (by nlinarith [mul_pos p1 p2])
            (by
              have := mul_le_mul q1 q2 p2.le (sq_nonneg _)
              nlinarith [this])
          simp only [hF]
          rw [mul_pow, mul_pow, mul_pow] at key
          exact key
    _ ≤ ∫ x in a..b, F x := by
        apply mv1974_interval_packing S _ _ F a b hab
        · intro r hr; linarith [hδ r hr]
        · exact hin
        · intro r hr r' hr' hne
          have h1 := hsp r hr r' hr' hne
          have h2 := hsp r' hr' r hr (Ne.symm hne)
          rcases le_total (c r) (c r') with h | h
          · left
            rw [abs_of_nonpos (by linarith)] at h1
            rw [abs_of_nonneg (by linarith)] at h2
            linarith
          · right
            rw [abs_of_nonneg (by linarith)] at h1
            rw [abs_of_nonpos (by linarith)] at h2
            linarith
        · intro x _; exact hF0 x
        · exact hint

/-- MV1974 Lemma 5 for points in the open unit interval. -/
theorem mv1974_line_mixed {κ : Type*} [DecidableEq κ] (T : Finset κ) (c δ : κ → ℝ) (D : ℝ)
    (hD : 0 < D) (hδ : ∀ r ∈ T, 0 < δ r)
    (hlo : ∀ r ∈ T, δ r ≤ c r ∧ D ≤ c r)
    (hhi : ∀ r ∈ T, c r ≤ 1 - δ r ∧ c r ≤ 1 - D)
    (hsp : ∀ r ∈ T, ∀ r' ∈ T, r ≠ r' → δ r ≤ |c r - c r'|)
    (t : κ) (ht : t ∈ T) :
    ∑ r ∈ T.erase t, δ r/((Real.sin (Real.pi*c r))^2*(Real.sin (Real.pi*(c r - c t)))^2) ≤
      4*(1/Real.pi^2)*(1/D+1/δ t)/(Real.sin (Real.pi*c t))^2 := by
  have hd := hδ t ht
  have hlt := hlo t ht
  have hht := hhi t ht
  have hpi := Real.pi_pos
  rw [← Finset.sum_filter_add_sum_filter_not (T.erase t) (fun r => c r < c t)]
  have hmemL : ∀ r ∈ (T.erase t).filter (fun r => c r < c t),
      r ∈ T ∧ δ r ≤ c t - c r ∧ δ t ≤ c t - c r := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_erase] at hr
    obtain ⟨⟨hne, hrT⟩, hlt'⟩ := hr
    have h1 := hsp r hrT t ht hne
    have h2 := hsp t ht r hrT (Ne.symm hne)
    rw [abs_of_nonpos (by linarith)] at h1
    rw [abs_of_nonneg (by linarith)] at h2
    exact ⟨hrT, by linarith, by linarith⟩
  have hmemR : ∀ r ∈ (T.erase t).filter (fun r => ¬ c r < c t),
      r ∈ T ∧ δ r ≤ c r - c t ∧ δ t ≤ c r - c t := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_erase] at hr
    obtain ⟨⟨hne, hrT⟩, hlt'⟩ := hr
    have hge : c t ≤ c r := not_lt.mp hlt'
    have h1 := hsp r hrT t ht hne
    have h2 := hsp t ht r hrT (Ne.symm hne)
    rw [abs_of_nonneg (by linarith)] at h1
    rw [abs_of_nonpos (by linarith)] at h2
    exact ⟨hrT, by linarith, by linarith⟩
  have hL := mv1974_mixed_side ((T.erase t).filter (fun r => c r < c t)) c δ (c t)
    (D / 2) (c t - δ t / 2) (by linarith)
    (fun x hx => Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi (by linarith [hx.1]))
      (by nlinarith [hx.2]))
    (fun x hx y hy => mul_pos_of_neg_of_neg
      (Real.sin_neg_of_neg_of_neg_pi_lt (by nlinarith [hx.2]) (by nlinarith [hx.1]))
      (Real.sin_neg_of_neg_of_neg_pi_lt (by nlinarith [hy.2]) (by nlinarith [hy.1])))
    (fun r hr => hδ r (hmemL r hr).1)
    (fun r hr => by
      obtain ⟨hrT, h1, h2⟩ := hmemL r hr
      have := hlo r hrT
      exact ⟨by linarith, by linarith⟩)
    (fun r hr r' hr' hne => hsp r (hmemL r hr).1 r' (hmemL r' hr').1 hne)
  have hR := mv1974_mixed_side ((T.erase t).filter (fun r => ¬ c r < c t)) c δ (c t)
    (c t + δ t / 2) (1 - D / 2) (by linarith)
    (fun x hx => Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi (by linarith [hx.1]))
      (by nlinarith [hx.2]))
    (fun x hx y hy => mul_pos
      (Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi (by linarith [hx.1])) (by nlinarith [hx.2]))
      (Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi (by linarith [hy.1])) (by nlinarith [hy.2])))
    (fun r hr => hδ r (hmemR r hr).1)
    (fun r hr => by
      obtain ⟨hrT, h1, h2⟩ := hmemR r hr
      have := hhi r hrT
      exact ⟨by linarith, by linarith⟩)
    (fun r hr r' hr' hne => hsp r (hmemR r hr).1 r' (hmemR r' hr').1 hne)
  have hP := mv1974_mixed_integral (c t) (D / 2) (δ t / 2) (by linarith) (by linarith)
    (by linarith) (by linarith)
  have e1 : 2 * (D / 2) = D := by ring
  have e2 : 2 * (δ t / 2) = δ t := by ring
  rw [e1, e2] at hP
  linarith

/-- The square of sin (π a) is unchanged when a is shifted by an integer. -/
theorem mv1974_sin_sq_sub_int (a b : ℝ) (n : ℤ) (h : a = b + n) :
    (Real.sin (Real.pi*a))^2 = (Real.sin (Real.pi*b))^2 := by
  rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub, h]
  have : 2*(Real.pi*(b + n)) = 2*(Real.pi*b) + n*(2*Real.pi) := by ring
  rw [this, Real.cos_add_int_mul_two_pi]

/-- The distance to the nearest integer is at most the fractional part and its complement. Standard. -/
theorem mv1974_dist0_le_fract (y : ℝ) : dist0 y ≤ Int.fract y ∧ dist0 y ≤ 1 - Int.fract y := by
  have h0 := Int.fract_nonneg y
  have h1 := Int.fract_lt_one y
  have hy : y = Int.fract y + ⌊y⌋ := (Int.fract_add_floor y).symm
  constructor
  · have h := dist0_le_abs_sub_int y ⌊y⌋
    have e : y - (⌊y⌋ : ℝ) = Int.fract y := by linarith
    rw [e, abs_of_nonneg h0] at h
    exact h
  · have h := dist0_le_abs_sub_int y (⌊y⌋ + 1)
    have e : y - ((⌊y⌋ + 1 : ℤ) : ℝ) = -(1 - Int.fract y) := by push_cast; linarith
    rw [e, abs_neg, abs_of_nonneg (by linarith)] at h
    exact h

/-- The distance of a difference to the nearest integer is at most the gap of fractional parts and its complement. Standard. -/
theorem mv1974_dist0_le_fract_sub (y z : ℝ) :
    dist0 (y - z) ≤ |Int.fract y - Int.fract z| ∧
      dist0 (y - z) ≤ 1 - |Int.fract y - Int.fract z| := by
  have hy0 := Int.fract_nonneg y
  have hy1 := Int.fract_lt_one y
  have hz0 := Int.fract_nonneg z
  have hz1 := Int.fract_lt_one z
  have hy : y = Int.fract y + ⌊y⌋ := (Int.fract_add_floor y).symm
  have hz : z = Int.fract z + ⌊z⌋ := (Int.fract_add_floor z).symm
  constructor
  · have h := dist0_le_abs_sub_int (y - z) (⌊y⌋ - ⌊z⌋)
    have e : y - z - ((⌊y⌋ - ⌊z⌋ : ℤ) : ℝ) = Int.fract y - Int.fract z := by
      push_cast; linarith
    rw [e] at h
    exact h
  · rcases le_total 0 (Int.fract y - Int.fract z) with hd | hd
    · have h := dist0_le_abs_sub_int (y - z) (⌊y⌋ - ⌊z⌋ + 1)
      have e : y - z - ((⌊y⌋ - ⌊z⌋ + 1 : ℤ) : ℝ) = -(1 - (Int.fract y - Int.fract z)) := by
        push_cast; linarith
      rw [e, abs_neg, abs_of_nonneg (by linarith)] at h
      rw [abs_of_nonneg hd]
      exact h
    · have h := dist0_le_abs_sub_int (y - z) (⌊y⌋ - ⌊z⌋ - 1)
      have e : y - z - ((⌊y⌋ - ⌊z⌋ - 1 : ℤ) : ℝ) = 1 + (Int.fract y - Int.fract z) := by
        push_cast; linarith
      rw [e, abs_of_nonneg (by linarith)] at h
      rw [abs_of_nonpos hd]
      linarith

/-- The squared sine at pi times y depends only on the fractional part of y. Standard. -/
theorem mv1974_sin_sq_fract (y : ℝ) :
    (Real.sin (Real.pi*y))^2 = (Real.sin (Real.pi*Int.fract y))^2 :=
  mv1974_sin_sq_sub_int y (Int.fract y) ⌊y⌋ (Int.fract_add_floor y).symm

/-- The squared sine at pi times a difference depends only on the fractional parts. Standard. -/
theorem mv1974_sin_sq_fract_sub (y z : ℝ) :
    (Real.sin (Real.pi*(y - z)))^2 = (Real.sin (Real.pi*(Int.fract y - Int.fract z)))^2 := by
  apply mv1974_sin_sq_sub_int _ _ (⌊y⌋ - ⌊z⌋)
  have hy : y = Int.fract y + ⌊y⌋ := (Int.fract_add_floor y).symm
  have hz : z = Int.fract z + ⌊z⌋ := (Int.fract_add_floor z).symm
  push_cast; linarith

/-- The fractional parts of the differences to a base point satisfy the line hypotheses. -/
theorem mv1974_fract_line_hyps {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x δ : ι → ℝ)
    (hsep : ∀ r s, r ≠ s → δ r ≤ dist0 (x r-x s)) (s : ι) :
    (∀ r ∈ univ.erase s, δ r ≤ Int.fract (x r - x s) ∧ δ s ≤ Int.fract (x r - x s)) ∧
    (∀ r ∈ univ.erase s, Int.fract (x r - x s) ≤ 1 - δ r ∧ Int.fract (x r - x s) ≤ 1 - δ s) ∧
    (∀ r ∈ univ.erase s, ∀ r' ∈ univ.erase s, r ≠ r' →
      δ r ≤ |Int.fract (x r - x s) - Int.fract (x r' - x s)|) := by
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr r' hr' hne => ?_⟩
  · have hrs : r ≠ s := (Finset.mem_erase.mp hr).1
    have h1 := hsep r s hrs
    have h2 := hsep s r hrs.symm
    rw [dist0_sub_comm] at h2
    have h3 := (mv1974_dist0_le_fract (x r - x s)).1
    exact ⟨by linarith, by linarith⟩
  · have hrs : r ≠ s := (Finset.mem_erase.mp hr).1
    have h1 := hsep r s hrs
    have h2 := hsep s r hrs.symm
    rw [dist0_sub_comm] at h2
    have h3 := (mv1974_dist0_le_fract (x r - x s)).2
    exact ⟨by linarith, by linarith⟩
  · have h1 := hsep r r' hne
    have h3 := (mv1974_dist0_le_fract_sub (x r - x s) (x r' - x s)).1
    have e : x r - x s - (x r' - x s) = x r - x r' := by ring
    rw [e] at h3
    linarith

/-- MV1974 page 76 Lemma 2. -/
theorem mv1974_second_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x δ : ι → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s → δ r ≤ dist0 (x r-x s)) (s : ι) :
    ∑ r, δ r/(Real.sin (Real.pi*(x r-x s)))^2 ≤ (4/Real.pi^2)/δ s := by
  obtain ⟨hlo, hhi, hsp⟩ := mv1974_fract_line_hyps x δ hsep s
  have key := mv1974_line_second (univ.erase s) (fun r => Int.fract (x r - x s)) δ (δ s) (hδ s)
    (fun r _ => hδ r) hlo hhi hsp
  have hsum : ∑ r, δ r/(Real.sin (Real.pi*(x r-x s)))^2 =
      ∑ r ∈ univ.erase s, δ r/(Real.sin (Real.pi*Int.fract (x r - x s)))^2 := by
    rw [← Finset.sum_subset (Finset.subset_univ (univ.erase s))]
    · exact Finset.sum_congr rfl fun r _ => by rw [mv1974_sin_sq_fract]
    · intro r _ hr
      have : r = s := by simpa using hr
      subst this
      simp
  rw [hsum]
  exact key

/-- MV1974 page 77 Lemma 4, for spacings at most one sixth. -/
theorem mv1974_fourth_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x δ : ι → ℝ) (hδ : ∀ r, 0 < δ r) (hδ6 : ∀ r, δ r ≤ 1/6)
    (hsep : ∀ r s, r ≠ s → δ r ≤ dist0 (x r-x s)) (s : ι) :
    ∑ r, δ r/(Real.sin (Real.pi*(x r-x s)))^4 ≤ (7/2)*(1/Real.pi^2)^2/δ s^3 := by
  obtain ⟨hlo, hhi, hsp⟩ := mv1974_fract_line_hyps x δ hsep s
  have key := mv1974_line_fourth (univ.erase s) (fun r => Int.fract (x r - x s)) δ (δ s) (hδ s)
    (hδ6 s) (fun r _ => hδ r) (fun r _ => hδ6 r) hlo hhi hsp
  have hsum : ∑ r, δ r/(Real.sin (Real.pi*(x r-x s)))^4 =
      ∑ r ∈ univ.erase s, δ r/(Real.sin (Real.pi*Int.fract (x r - x s)))^4 := by
    rw [← Finset.sum_subset (Finset.subset_univ (univ.erase s))]
    · refine Finset.sum_congr rfl fun r _ => ?_
      have h := mv1974_sin_sq_fract (x r - x s)
      have e : ∀ a : ℝ, a^4 = (a^2)^2 := fun a => by ring
      rw [e, e, h]
    · intro r _ hr
      have : r = s := by simpa using hr
      subst this
      simp
  rw [hsum]
  exact key

/-- MV1974 page 77 Lemma 5. -/
theorem mv1974_mixed_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x δ : ι → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s → δ r ≤ dist0 (x r-x s)) (s t : ι) (hst : s ≠ t) :
    ∑ r, δ r/((Real.sin (Real.pi*(x r-x s)))^2*(Real.sin (Real.pi*(x r-x t)))^2) ≤
      4*(1/Real.pi^2)*(1/δ s+1/δ t)/(Real.sin (Real.pi*(x s-x t)))^2 := by
  obtain ⟨hlo, hhi, hsp⟩ := mv1974_fract_line_hyps x δ hsep s
  have key := mv1974_line_mixed (univ.erase s) (fun r => Int.fract (x r - x s)) δ (δ s) (hδ s)
    (fun r _ => hδ r) hlo hhi hsp t (Finset.mem_erase.mpr ⟨hst.symm, Finset.mem_univ t⟩)
  have hsum : ∑ r, δ r/((Real.sin (Real.pi*(x r-x s)))^2*(Real.sin (Real.pi*(x r-x t)))^2) =
      ∑ r ∈ (univ.erase s).erase t, δ r/((Real.sin (Real.pi*Int.fract (x r - x s)))^2*
        (Real.sin (Real.pi*(Int.fract (x r - x s) - Int.fract (x t - x s))))^2) := by
    rw [← Finset.sum_subset (Finset.subset_univ ((univ.erase s).erase t))]
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [← mv1974_sin_sq_fract, ← mv1974_sin_sq_fract_sub]
      have e : x r - x s - (x t - x s) = x r - x t := by ring
      rw [e]
    · intro r _ hr
      have : r = t ∨ r = s := by
        by_contra hcon
        push Not at hcon
        exact hr (Finset.mem_erase.mpr ⟨hcon.1, Finset.mem_erase.mpr ⟨hcon.2, Finset.mem_univ r⟩⟩)
      rcases this with h | h <;> subst h <;> simp
  have hden : (Real.sin (Real.pi*(x s-x t)))^2 =
      (Real.sin (Real.pi*Int.fract (x t - x s)))^2 := by
    rw [← mv1974_sin_sq_fract]
    have e : Real.pi*(x s - x t) = -(Real.pi*(x t - x s)) := by ring
    rw [e, Real.sin_neg, neg_sq]
  rw [hsum, hden]
  exact key

/-- MV1974 display 1.3 when every spacing is at most one sixth. -/
theorem mv1974_cosecant_small {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x δ : ι → ℝ) (hδ : ∀ r, 0 < δ r) (hδ6 : ∀ r, δ r ≤ 1/6)
    (hsep : ∀ r s, r ≠ s → δ r ≤ dist0 (x r-x s)) (b : ι → ℂ) :
    ‖∑ r, ∑ s ∈ univ.erase r,
      b r*conj (b s)/(Real.sin (Real.pi*(x r-x s)) : ℂ)‖ ≤
      3/2*∑ r, ‖b r‖^2/δ r :=
  mv1974_cosecant_of_moments x δ hδ hsep (mv1974_second_moment x δ hδ hsep)
    (mv1974_fourth_moment x δ hδ hδ6 hsep) (mv1974_mixed_moment x δ hδ hsep) b

/-- A product of two twisted coefficients, written with cosine and sine of the phase difference. -/
theorem mv1974_twist_term (σ y1 y2 : ℝ) (e1 e2 c d : ℂ) (he2 : conj e2 = e2) :
    (e1 * c * Complex.exp ((σ : ℂ) * Real.pi * I * (y1 : ℂ))) *
        conj (e2 * d * Complex.exp ((σ : ℂ) * Real.pi * I * (y2 : ℂ))) =
      e1 * e2 * (c * conj d) *
        ((Real.cos (σ * (Real.pi * (y1 - y2))) : ℂ) +
          (Real.sin (σ * (Real.pi * (y1 - y2))) : ℂ) * I) := by
  have h1 : conj (Complex.exp ((σ : ℂ) * Real.pi * I * (y2 : ℂ))) =
      Complex.exp (-((σ : ℂ) * Real.pi * I * (y2 : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have h2 : Complex.exp ((σ : ℂ) * Real.pi * I * (y1 : ℂ)) *
      Complex.exp (-((σ : ℂ) * Real.pi * I * (y2 : ℂ))) =
        (Real.cos (σ * (Real.pi * (y1 - y2))) : ℂ) +
          (Real.sin (σ * (Real.pi * (y1 - y2))) : ℂ) * I := by
    rw [← Complex.exp_add, Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I]
    congr 1
    push_cast
    ring
  rw [map_mul, map_mul, h1, he2, ← h2]
  ring

/-- The trigonometric identity 4 cot φ + 4 tan φ = 8 / sin 2φ behind the halving step. -/
theorem mv1974_pair_identity (xr xs : ℝ) (c d : ℂ) :
    ∑ ε : Bool, ∑ ε' : Bool,
      (((if ε then (-1 : ℂ) else 1) * c *
          Complex.exp (((1 : ℝ) : ℂ) * Real.pi * I * (((xr + (if ε then 1 else 0)) / 2 : ℝ) : ℂ))) *
        conj ((if ε' then (-1 : ℂ) else 1) * d *
          Complex.exp (((1 : ℝ) : ℂ) * Real.pi * I *
            (((xs + (if ε' then 1 else 0)) / 2 : ℝ) : ℂ))) /
        (Real.sin (Real.pi * ((xr + (if ε then 1 else 0)) / 2 -
          (xs + (if ε' then 1 else 0)) / 2)) : ℂ) +
       ((if ε then (-1 : ℂ) else 1) * c *
          Complex.exp (((-1 : ℝ) : ℂ) * Real.pi * I * (((xr + (if ε then 1 else 0)) / 2 : ℝ) : ℂ))) *
        conj ((if ε' then (-1 : ℂ) else 1) * d *
          Complex.exp (((-1 : ℝ) : ℂ) * Real.pi * I *
            (((xs + (if ε' then 1 else 0)) / 2 : ℝ) : ℂ))) /
        (Real.sin (Real.pi * ((xr + (if ε then 1 else 0)) / 2 -
          (xs + (if ε' then 1 else 0)) / 2)) : ℂ)) =
      8 * (c * conj d / (Real.sin (Real.pi * (xr - xs)) : ℂ)) := by
  have c1 : conj (1 : ℂ) = 1 := map_one _
  have c2 : conj (-1 : ℂ) = -1 := by simp
  set φ : ℝ := Real.pi * (xr - xs) / 2 with hφ
  have a1 : Real.pi * ((xr + 1) / 2 - (xs + 1) / 2) = φ := by rw [hφ]; ring
  have a2 : Real.pi * ((xr + 1) / 2 - (xs + 0) / 2) = φ + Real.pi / 2 := by rw [hφ]; ring
  have a3 : Real.pi * ((xr + 0) / 2 - (xs + 1) / 2) = φ - Real.pi / 2 := by rw [hφ]; ring
  have a4 : Real.pi * ((xr + 0) / 2 - (xs + 0) / 2) = φ := by rw [hφ]; ring
  have a5 : Real.pi * (xr - xs) = 2 * φ := by rw [hφ]; ring
  simp only [Fintype.sum_bool, ite_true, ite_false, Bool.false_eq_true]
  rw [mv1974_twist_term _ _ _ _ _ _ _ c2, mv1974_twist_term _ _ _ _ _ _ _ c2,
    mv1974_twist_term _ _ _ _ _ _ _ c1, mv1974_twist_term _ _ _ _ _ _ _ c1,
    mv1974_twist_term _ _ _ _ _ _ _ c2, mv1974_twist_term _ _ _ _ _ _ _ c2,
    mv1974_twist_term _ _ _ _ _ _ _ c1, mv1974_twist_term _ _ _ _ _ _ _ c1]
  simp only [a1, a2, a3, a4, a5, one_mul, neg_one_mul, Real.cos_neg, Real.sin_neg,
    Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, Real.cos_sub_pi_div_two,
    Real.sin_sub_pi_div_two, Real.sin_two_mul, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  have hsc : (Real.sin φ : ℂ) ^ 2 + (Real.cos φ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq φ
  generalize (Real.sin φ : ℂ) = S at *
  generalize (Real.cos φ : ℂ) = C at *
  generalize conj d = d'
  by_cases hS : S = 0
  · have hC : C ≠ 0 := by rintro rfl; simp [hS] at hsc
    subst hS
    simp only [mul_zero, zero_mul, div_zero, neg_zero, zero_add, add_zero, mul_zero]
    field_simp
    ring
  by_cases hC : C = 0
  · subst hC
    simp only [mul_zero, zero_mul, div_zero, neg_zero, zero_add, add_zero, mul_zero]
    field_simp
    ring
  field_simp
  linear_combination (8 * c * d') * hsc

/-- Halving a point shifted by an integer at most halves the distance to the nearest integer. -/
theorem mv1974_dist0_half (θ : ℝ) (k : ℤ) : dist0 θ / 2 ≤ dist0 ((θ + k) / 2) := by
  have h := dist0_le_abs_sub_int θ (2 * round ((θ + k) / 2) - k)
  have h2 : θ - ((2 * round ((θ + k) / 2) - k : ℤ) : ℝ) =
      2 * ((θ + k) / 2 - round ((θ + k) / 2)) := by push_cast; ring
  rw [h2, abs_mul, abs_two] at h
  unfold dist0 at h ⊢
  linarith

/-- The distance from one half to the nearest integer is at least one half. -/
theorem mv1974_dist0_one_half : (1 : ℝ) / 2 ≤ dist0 (1 / 2) := by
  unfold dist0
  generalize round ((1 : ℝ) / 2) = n
  rcases le_or_gt n 0 with h | h
  · have : (n : ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]; linarith

/-- The halving step on MV1974 page 81, displays 3.18 and 3.19. -/
theorem mv1974_cosecant_doubling.{v} (B : ℝ) (hB : 2*B ≤ 1)
    (hyp : ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (x δ : ι → ℝ), (∀ r, 0 < δ r) →
      (∀ r, δ r ≤ B) → (∀ r s, r ≠ s → δ r ≤ dist0 (x r-x s)) → ∀ b : ι → ℂ,
      ‖∑ r, ∑ s ∈ univ.erase r,
        b r*conj (b s)/(Real.sin (Real.pi*(x r-x s)) : ℂ)‖ ≤ 3/2*∑ r, ‖b r‖^2/δ r)
    (ι : Type v) [Fintype ι] [DecidableEq ι] (x δ : ι → ℝ) (hδ : ∀ r, 0 < δ r)
    (hδB : ∀ r, δ r ≤ 2*B) (hsep : ∀ r s, r ≠ s → δ r ≤ dist0 (x r-x s)) (b : ι → ℂ) :
    ‖∑ r, ∑ s ∈ univ.erase r,
      b r*conj (b s)/(Real.sin (Real.pi*(x r-x s)) : ℂ)‖ ≤ 3/2*∑ r, ‖b r‖^2/δ r := by
  let y : ι × Bool → ℝ := fun p => (x p.1 + (if p.2 then 1 else 0)) / 2
  let δ' : ι × Bool → ℝ := fun p => δ p.1 / 2
  let w : ℝ → ι × Bool → ℂ := fun σ p =>
    (if p.2 then (-1 : ℂ) else 1) * b p.1 * Complex.exp ((σ : ℂ) * Real.pi * I * ((y p : ℝ) : ℂ))
  have hδ' : ∀ p, 0 < δ' p := fun p => by simp only [δ']; linarith [hδ p.1]
  have hδ'B : ∀ p, δ' p ≤ B := fun p => by simp only [δ']; linarith [hδB p.1]
  have hsep' : ∀ p q, p ≠ q → δ' p ≤ dist0 (y p - y q) := by
    rintro ⟨r, ε⟩ ⟨s, ε'⟩ hne
    by_cases hrs : r = s
    · subst hrs
      have hd : δ r / 2 ≤ dist0 (1 / 2) :=
        le_trans (by linarith [hδB r]) mv1974_dist0_one_half
      cases ε <;> cases ε'
      · exact absurd rfl hne
      · simp only [y, δ', ite_true, ite_false, Bool.false_eq_true]
        rw [show (x r + 0) / 2 - (x r + 1) / 2 = -(1 / 2) by ring, dist0_neg]
        exact hd
      · simp only [y, δ', ite_true, ite_false, Bool.false_eq_true]
        rw [show (x r + 1) / 2 - (x r + 0) / 2 = 1 / 2 by ring]
        exact hd
      · exact absurd rfl hne
    · have key : ∀ k : ℤ, δ r / 2 ≤ dist0 ((x r - x s + k) / 2) := fun k =>
        le_trans (by linarith [hsep r s hrs]) (mv1974_dist0_half _ k)
      cases ε <;> cases ε' <;> simp only [y, δ', ite_true, ite_false, Bool.false_eq_true]
      · convert key 0 using 2; push_cast; ring
      · convert key (-1) using 2; push_cast; ring
      · convert key 1 using 2; push_cast; ring
      · convert key 0 using 2; push_cast; ring
  have hnorm : ∀ σ p, ‖w σ p‖ = ‖b p.1‖ := by
    intro σ p
    have h1 : ‖Complex.exp ((σ : ℂ) * Real.pi * I * ((y p : ℝ) : ℂ))‖ = 1 := by
      rw [show (σ : ℂ) * Real.pi * I * ((y p : ℝ) : ℂ) = ((σ * Real.pi * y p : ℝ) : ℂ) * I by
        push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have h2 : ‖(if p.2 then (-1 : ℂ) else 1)‖ = 1 := by split_ifs <;> simp
    simp only [w, norm_mul, h1, h2, one_mul, mul_one]
  have hsum : ∀ σ, ∑ p, ‖w σ p‖ ^ 2 / δ' p = 4 * ∑ r, ‖b r‖ ^ 2 / δ r := by
    intro σ
    simp_rw [hnorm]
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun r _ => ?_
    have := (hδ r).ne'
    simp only [Fintype.sum_bool, δ']
    field_simp
    ring
  have hA : ∀ σ, ‖∑ p, ∑ q, w σ p * conj (w σ q) /
      (Real.sin (Real.pi * (y p - y q)) : ℂ)‖ ≤ 6 * ∑ r, ‖b r‖ ^ 2 / δ r := by
    intro σ
    have h := hyp (ι × Bool) y δ' hδ' hδ'B hsep' (w σ)
    rw [hsum σ] at h
    have her : ∀ p : ι × Bool, (∑ q ∈ univ.erase p, w σ p * conj (w σ q) /
        (Real.sin (Real.pi * (y p - y q)) : ℂ)) =
          ∑ q, w σ p * conj (w σ q) / (Real.sin (Real.pi * (y p - y q)) : ℂ) :=
      fun p => Finset.sum_erase _ (by simp)
    simp_rw [her] at h
    linarith
  have hid : (∑ p, ∑ q, w 1 p * conj (w 1 q) / (Real.sin (Real.pi * (y p - y q)) : ℂ)) +
      (∑ p, ∑ q, w (-1) p * conj (w (-1) q) / (Real.sin (Real.pi * (y p - y q)) : ℂ)) =
      8 * ∑ r, ∑ s, b r * conj (b s) / (Real.sin (Real.pi * (x r - x s)) : ℂ) := by
    rw [← sum_add_distrib]
    simp_rw [← sum_add_distrib]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [mul_sum]
    refine sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm, mul_sum]
    refine sum_congr rfl fun s _ => ?_
    exact mv1974_pair_identity (x r) (x s) (b r) (b s)
  have her0 : ∀ r : ι, (∑ s ∈ univ.erase r, b r * conj (b s) /
      (Real.sin (Real.pi * (x r - x s)) : ℂ)) =
        ∑ s, b r * conj (b s) / (Real.sin (Real.pi * (x r - x s)) : ℂ) :=
    fun r => Finset.sum_erase _ (by simp)
  simp_rw [her0]
  have h8 : ‖(8 : ℂ) * ∑ r, ∑ s, b r * conj (b s) /
      (Real.sin (Real.pi * (x r - x s)) : ℂ)‖ ≤ 12 * ∑ r, ‖b r‖ ^ 2 / δ r := by
    rw [← hid]
    exact le_trans (norm_add_le _ _) (by linarith [hA 1, hA (-1)])
  rw [norm_mul] at h8
  have : ‖(8 : ℂ)‖ = 8 := by simp
  rw [this] at h8
  linarith

/-- MV1974 display 1.3 on a finite type. -/
theorem mv1974_cosecant_fintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x δ : ι → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s → δ r ≤ dist0 (x r-x s)) (b : ι → ℂ) :
    ‖∑ r, ∑ s ∈ univ.erase r,
      b r*conj (b s)/(Real.sin (Real.pi*(x r-x s)) : ℂ)‖ ≤ 3/2*∑ r, ‖b r‖^2/δ r := by
  by_cases h : ∀ r, δ r ≤ 1 / 2
  · have s1 := mv1974_cosecant_doubling (1 / 6) (by norm_num)
      (fun ι _ _ x δ h1 h2 h3 b => mv1974_cosecant_small x δ h1 h2 h3 b)
    have s2 := mv1974_cosecant_doubling (2 * (1 / 6)) (by norm_num) s1
    exact s2 ι x δ hδ (fun r => by linarith [h r]) hsep b
  · simp only [not_forall, not_le] at h
    obtain ⟨r0, hr0⟩ := h
    have hall : ∀ s, s = r0 := by
      intro s
      by_contra hs
      have := hsep r0 s (fun h => hs h.symm)
      linarith [dist0_le_half (x r0 - x s)]
    have hz : (∑ r, ∑ s ∈ univ.erase r,
        b r * conj (b s) / (Real.sin (Real.pi * (x r - x s)) : ℂ)) = 0 := by
      refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s hs => ?_
      exact absurd ((hall s).trans (hall r).symm) (Finset.ne_of_mem_erase hs)
    rw [hz, norm_zero]
    exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (hδ r).le)

/-- Montgomery and Vaughan 1974 page 73 Theorem 1 display 1.3.
For real points distinct modulo one and positive individual spacings no greater
than each distance to another point, the cosecant form has norm at most three
halves times the sum of squared coefficient norms divided by individual spacing.
The positive spacing and pairwise bounds express the paper's minimum condition.
This is also MV1973 page 122 display 2.2. PROVED here from Lemmas 2 to 5
and the halving argument on MV1974 page 81; Lemma 5 uses a real primitive in place
of the paper's contour integral. -/
theorem mv1974_individual_cosecant {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (x δ : ι → ℝ)
    (hδ : ∀ r ∈ R, 0 < δ r)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s →
      δ r ≤ LeanLab.PNTPort.LargeSieve.dist0 (x r - x s))
    (u : ι → ℂ) :
    ‖∑ r ∈ R, ∑ s ∈ R.erase r,
      u r * (starRingEnd ℂ) (u s) / (Real.sin (Real.pi * (x r - x s)) : ℂ)‖ ≤
      3 / 2 * ∑ r ∈ R, ‖u r‖ ^ 2 / δ r := by
  have hh := mv1974_cosecant_fintype (fun r : R => x r) (fun r : R => δ r)
    (fun r => hδ r r.property)
    (fun r s hne => hsep r r.property s s.property (fun h => hne (Subtype.ext h)))
    (fun r : R => u r)
  have her (r : R) : (∑ t ∈ (univ : Finset R).erase r,
      u r * conj (u t) / (Real.sin (Real.pi * (x r - x t)) : ℂ)) =
        ∑ t : R, u r * conj (u t) / (Real.sin (Real.pi * (x r - x t)) : ℂ) :=
    Finset.sum_erase _ (by simp)
  simp_rw [her] at hh
  have hex (r : ι) : (∑ t ∈ R.erase r,
      u r * conj (u t) / (Real.sin (Real.pi * (x r - x t)) : ℂ)) =
        ∑ t ∈ R, u r * conj (u t) / (Real.sin (Real.pi * (x r - x t)) : ℂ) :=
    Finset.sum_erase R (by simp)
  simp_rw [hex]
  simpa only [← Finset.sum_coe_sort R] using hh

end LeanLab.SchnirelmannBounds.Decomp1525b
