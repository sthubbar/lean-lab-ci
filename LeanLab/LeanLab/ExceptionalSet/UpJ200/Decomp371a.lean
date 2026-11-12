import LeanLab.ExceptionalSet.UpJ200.DecompJ200
import LeanLab.ExceptionalSet.BrudernPerelliExplicit

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.Decomp371a`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


/-!
Task371 decomposes the remaining major arc leaf of P0082.
Source: https://doi.org/10.5802/aif.1621 pages 362 to 365, displays 8 and 23.
The open leaves isolate the coefficient bound, the boundary count and the Fourier identity.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp371a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE Sp eC majorArcs)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200

/-- P0082 page 372 display 47. On real arguments at least eight, the derivative
of F is at least gamma. Mathlib's mean value theorem gives this growth bound. -/
theorem F_growth (γ x y : ℝ) (hγ : 1 < γ) (hx : 8 ≤ x) (hxy : x ≤ y) :
    γ * (y - x) ≤ F γ y - F γ x := by
  have hlog8 : (1 : ℝ) ≤ Real.log 8 := by
    have ht := Real.log_two_gt_d9
    have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hd (z : ℝ) (hz : 8 ≤ z) :
      HasDerivAt (F γ) (F γ z * (γ * Real.log z ^ (γ - 1)) / z) z := by
    have hz0 : 0 < z := by linarith
    have hL : 0 < Real.log z := Real.log_pos (by linarith)
    convert ((Real.hasDerivAt_log hz0.ne').rpow_const (p := γ) (Or.inl hL.ne')).exp using 1
    · rfl
    · dsimp [F]; ring
  have hbound (z : ℝ) (hz : 8 ≤ z) :
      γ ≤ deriv (F γ) z := by
    have hz0 : 0 < z := by linarith
    have hL : 1 ≤ Real.log z :=
      hlog8.trans (Real.log_le_log (by norm_num) hz)
    have hF : z ≤ F γ z := by
      calc z = Real.exp (Real.log z) := (Real.exp_log hz0).symm
        _ ≤ Real.exp (Real.log z ^ γ) := by
          apply Real.exp_le_exp.mpr
          simpa only [Real.rpow_one] using
            (Real.rpow_le_rpow_of_exponent_le hL hγ.le)
    have hp : 1 ≤ Real.log z ^ (γ - 1) := Real.one_le_rpow hL (by linarith)
    rw [(hd z hz).deriv, le_div_iff₀ hz0]
    calc γ * z ≤ γ * F γ z := mul_le_mul_of_nonneg_left hF (by linarith)
      _ ≤ (γ * F γ z) * Real.log z ^ (γ - 1) := le_mul_of_one_le_right (mul_nonneg (by linarith) (Real.exp_pos _).le) hp
      _ = _ := by ring
  apply (convex_Ici (8 : ℝ)).mul_sub_le_image_sub_of_le_deriv
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => hbound z (interior_subset hz)) x hx y (hx.trans hxy) hxy


/-- P0082 page 365 floor window. Once N is at least eight, its upper floor
restriction excludes every index above N. A unit index step changes F by more than one. -/
theorem window_upper (γ : ℝ) (hγ : 1 < γ) (N : ℕ) (hN : 8 ≤ N)
    (n : ℕ) (hn : n ∈ window γ N) : n ≤ N := by
  by_contra hnN
  have hstep : (1 : ℝ) ≤ (n : ℝ) - N := by
    have hr : (N : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : N + 1 ≤ n)
    linarith
  have hg := F_growth γ N n hγ (by exact_mod_cast hN) (by exact_mod_cast (by omega : N ≤ n))
  have hγ0 : 0 ≤ γ := by linarith
  have hgap : 1 < F γ n - F γ N := by
    have hm := mul_le_mul_of_nonneg_left hstep hγ0
    nlinarith
  have hfloor : F γ n < (nu γ n : ℝ) + 1 := by
    simpa only [nu] using Int.lt_floor_add_one (F γ n)
  have hnu : (nu γ n : ℝ) ≤ F γ N := (Finset.mem_filter.mp hn).2.2
  linarith

/-- P0082 page 372 display 47. The derivative of F divided by x is nonnegative
on x at least eight. This supports the index range used on page 365. -/
theorem F_ratio_mono (γ x y : ℝ) (hγ : 1 < γ) (hx : 8 ≤ x) (hxy : x ≤ y) :
    F γ x / x ≤ F γ y / y := by
  have hlog8 : (1 : ℝ) ≤ Real.log 8 := by
    have ht := Real.log_two_gt_d9
    have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hd (z : ℝ) (hz : 8 ≤ z) : HasDerivAt (fun z => F γ z / z)
      (F γ z * (γ * Real.log z ^ (γ - 1) - 1) / z ^ 2) z := by
    have hz0 : 0 < z := by linarith
    have hL : 0 < Real.log z := Real.log_pos (by linarith)
    have hF : HasDerivAt (F γ) (F γ z * (γ * Real.log z ^ (γ - 1)) / z) z := by
      convert ((Real.hasDerivAt_log hz0.ne').rpow_const (p := γ) (Or.inl hL.ne')).exp using 1
      · rfl
      · dsimp [F]; ring
    convert hF.div (hasDerivAt_id z) hz0.ne' using 1
    · rfl
    · dsimp
      field_simp
  apply monotoneOn_of_deriv_nonneg (convex_Ici (8 : ℝ))
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => ?_) hx (hx.trans hxy) hxy
  have hz8 : 8 ≤ z := interior_subset hz
  have hL : 1 ≤ Real.log z := hlog8.trans (Real.log_le_log (by norm_num) hz8)
  have hp : 1 ≤ Real.log z ^ (γ - 1) := Real.one_le_rpow hL (by linarith)
  rw [(hd z hz8).deriv]
  apply div_nonneg
  · apply mul_nonneg (Real.exp_pos _).le
    have hg : 1 ≤ γ * Real.log z ^ (γ - 1) := one_le_mul_of_one_le_of_one_le hγ.le hp
    linarith
  · positivity


/-- P0082 page 365 floor window. For N at least sixteen the lower floor
restriction forces n strictly above N divided by two. -/
theorem window_lower (γ : ℝ) (hγ : 1 < γ) (N : ℕ) (hN : 16 ≤ N)
    (n : ℕ) (hn : n ∈ window γ N) : N / 2 < n := by
  by_contra hnlow
  have hnN : n ≤ N / 2 := by omega
  let m := max n 8
  have hm8 : 8 ≤ m := Nat.le_max_right _ _
  have hnm : n ≤ m := Nat.le_max_left _ _
  have hmN : 2 * m ≤ N := by dsimp [m]; omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hFm : 0 < F γ m := Real.exp_pos _
  have hmono : F γ n ≤ F γ m := by
    by_cases hn0 : n = 0
    · subst n
      have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
      have hpow : 0 ≤ Real.log (m : ℝ) ^ γ := Real.rpow_nonneg hlog _
      simpa only [F, Nat.cast_zero, Real.log_zero, Real.zero_rpow (by linarith : γ ≠ 0), Real.exp_zero]
        using Real.one_le_exp_iff.mpr hpow
    · exact LeanLab.ExceptionalSet.BrudernPerelli1998.F_mono (by linarith) (by omega) hnm
  have hr := F_ratio_mono γ m N hγ (by exact_mod_cast hm8) (by exact_mod_cast (by omega : m ≤ N))
  have hcross : F γ m * N ≤ F γ N * m := (div_le_div_iff₀ hmpos hNpos).mp hr
  have hhalf : F γ m ≤ F γ N / 2 := by
    calc
      _ ≤ F γ N * m / N := (le_div_iff₀ hNpos).mpr hcross
      _ ≤ F γ N / 2 := by
        rw [div_le_div_iff₀ hNpos (by norm_num : (0 : ℝ) < 2)]
        have hmNr : 2 * (m : ℝ) ≤ N := by exact_mod_cast hmN
        have hFN : 0 < F γ N := Real.exp_pos _
        nlinarith [mul_le_mul_of_nonneg_left hmNr hFN.le]
  have hfloor : (nu γ n : ℝ) ≤ F γ n := Int.floor_le _
  have hnu : F γ N / 2 < (nu γ n : ℝ) := (Finset.mem_filter.mp hn).2.1
  linarith

/-- P0082 page 365 Lemma 8. The literal floor window lies in the index range
used for the paper's equidistribution and second moment estimates. -/
theorem window_subset_Ioc (γ : ℝ) (hγ : 1 < γ) (N : ℕ) (hN : 16 ≤ N) :
    window γ N ⊆ Finset.Ioc (N / 2) N := by
  intro n hn
  exact Finset.mem_Ioc.mpr ⟨window_lower γ hγ N hN n hn,
    window_upper γ hγ N (by omega) n hn⟩

/-- P0082 page 357, the prime sum preceding display 6. Its integer frequencies
make it periodic with period one, as required by the Fourier coefficient argument. -/
theorem Sp_periodic (P X : ℝ) : Function.Periodic (Sp P X) 1 := by
  intro α
  unfold Sp
  apply Finset.sum_congr rfl
  intro p hp
  have he : eC ((α + 1) * (p : ℝ)) = eC (α * (p : ℝ)) := by
    unfold eC
    push_cast
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (((α : ℂ) + 1) * (p : ℂ))) =
      2 * (Real.pi : ℂ) * Complex.I * ((α : ℂ) * (p : ℂ)) + (p : ℂ) * (2 * Real.pi * Complex.I) by ring]
    rw [Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [he]

end LeanLab.ExceptionalSet.UpJ200.Decomp371a
