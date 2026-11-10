/-
Split of `theorem82`, the Theorem 8.2 step of this folder's Section 8, into four leaves and one
assembly.

The assembly is the counting argument of the proof.  The sparse two-sided Hardy-Littlewood
input is a statement about the multiples of the conductor `r` in the dyadic interval at
`X = r^A`; the analytic formula of Section 8 fails on at most `X^(3/5+ε)` even integers of
that interval, and the sparse input fails on at most `X^(3/5)` of them.  Since the interval
holds about `X/r` multiples of `r`, and `A > 5/2` makes `X^(3/5)` smaller than `X/r`, one
multiple of `r` lies outside both exceptional sets.  There the two-sided range and the
analytic formula contradict each other, because at a real zero `β = 1 - e` with `e` small the
formula's main term is `𝔖(N)·N·(1 + χ(-1))` up to `O(δ)`.

Leaves: a lower bound for the singular series on even arguments, the two-sided estimate for
the beta factor at a zero close to one, the domination of the three error terms by the main
term, and the absence of zeros at or beyond one.  Everything else is proved here.

AI wrote the Lean code.  Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements
import LeanLab.BhowmikGrimmelt2026.Decomp150a
import LeanLab.BhowmikGrimmelt2026.Counting107
import LeanLab.BhowmikGrimmelt2026.Section8Steps107

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction
open LeanLab.ExceptionalSet (E PowerBound PowerSaving LogPowerSaving EventuallyBelow DensityZero)

attribute [local instance] Classical.propDecidable

/-! ## Leaves -/

/-- LEAF. Step 1: on even arguments the singular series is at least `1/2`, so the main term
`𝔖(N)·N` of the analytic formula of Section 8 dominates its three error terms. -/
theorem leaf_singular_lower (N : ℕ) (hEven : Even N) (h2 : 2 ≤ N) : (1 / 2 : ℝ) ≤ singular N := by
  exact (by norm_num : (1 / 2 : ℝ) ≤ 1).trans
    (singular_ge_one461 N hEven (by omega))

private theorem norm_ofReal_eq_abs' (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  simpa using RCLike.norm_ofReal (K := ℂ) x

private theorem cpow_kernel_eq (β : ℝ) {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ 1) :
    ((x : ℂ) ^ ((β : ℂ) - 1)) * ((1 : ℂ) - (x : ℂ)) ^ ((β : ℂ) - 1)
      = (((x * (1 - x)) ^ (β - 1) : ℝ) : ℂ) := by
  have hcast : ((β : ℂ) - 1) = ((β - 1 : ℝ) : ℂ) := by push_cast; ring
  have hsub : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
  have h1x : (0 : ℝ) ≤ 1 - x := by linarith
  rw [hcast, hsub, ← Complex.ofReal_cpow hx1 (β - 1),
    ← Complex.ofReal_cpow h1x (β - 1), ← Complex.ofReal_mul, Real.mul_rpow hx1 h1x]

private theorem norm_kernel_eq (β : ℝ) {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ 1) :
    ‖(x : ℂ) ^ ((β : ℂ) - 1) * ((1 : ℂ) - (x : ℂ)) ^ ((β : ℂ) - 1)‖
      = (x * (1 - x)) ^ (β - 1) := by
  rw [cpow_kernel_eq β hx1 hx2, norm_ofReal_eq_abs']
  exact abs_of_nonneg (Real.rpow_nonneg (by nlinarith) _)

private theorem intervalIntegrable_kernel {β : ℝ} (hβ0 : 0 < β) :
    IntervalIntegrable (fun x : ℝ => (x * (1 - x)) ^ (β - 1)) volume 0 1 := by
  have hu : 0 < ((β : ℂ)).re := by simpa using hβ0
  have hc : IntervalIntegrable
      (fun x : ℝ => (x : ℂ) ^ ((β : ℂ) - 1) * ((1 : ℂ) - (x : ℂ)) ^ ((β : ℂ) - 1))
      volume 0 1 := Complex.betaIntegral_convergent hu hu
  refine hc.norm.congr_uIoo ?_
  intro x hx
  simp only [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Ioo] at hx
  exact norm_kernel_eq β hx.1.le hx.2.le

private theorem betaC_eq_integral {β : ℝ} (hβ0 : 0 < β) :
    betaC (β : ℂ) (β : ℂ) = (((∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ)) : ℝ) : ℂ) := by
  have hu : 0 < ((β : ℂ)).re := by simpa using hβ0
  have h1 : betaC (β : ℂ) (β : ℂ) = Complex.betaIntegral (β : ℂ) (β : ℂ) := by
    rw [betaC, ← Complex.betaIntegral_eq_Gamma_mul_div (β : ℂ) (β : ℂ) hu hu]
  have hcongr : ∫ x in (0 : ℝ)..1, ((x : ℂ) ^ ((β : ℂ) - 1) * ((1 : ℂ) - (x : ℂ)) ^ ((β : ℂ) - 1))
      = ∫ x in (0 : ℝ)..1, (((x * (1 - x)) ^ (β - 1) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact cpow_kernel_eq β hx.1 hx.2
  rw [h1, Complex.betaIntegral, hcongr, intervalIntegral.integral_ofReal]

/-! ## Bounds for the real beta integral -/

private theorem one_le_beta_integral {β : ℝ} (hβ4 : 3 / 4 ≤ β) (hβ1 : β ≤ 1) :
    1 ≤ ∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ) := by
  have hβ0 : 0 < β := by linarith
  have hint := intervalIntegrable_kernel (β := β) hβ0
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
    (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => (x * (1 - x)) ^ (β - 1))
    (a := 0) (b := 1) (by norm_num) hconst hint ?_
  · simpa using hmono
  · intro x hx
    have hx0 : 0 < x * (1 - x) := by nlinarith [hx.1, hx.2]
    have hxle : x * (1 - x) ≤ 1 := by nlinarith [hx.1, hx.2]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx0 hxle (by linarith)

private theorem half_integral_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∫ x in (0 : ℝ)..(1 / 2), ((x * (1 - x)) ^ (β - 1) : ℝ) ≤ (2 : ℝ) ^ (1 - 2 * β) / β := by
  have hint := intervalIntegrable_kernel (β := β) hβ0
  have hsub : IntervalIntegrable (fun x : ℝ => (x * (1 - x)) ^ (β - 1)) volume 0 (1 / 2) :=
    hint.mono_set (by
      intro y hy
      simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
        Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Icc] at hy ⊢
      constructor <;> linarith [hy.1, hy.2])
  have hg : IntervalIntegrable (fun x : ℝ => (2 : ℝ) ^ (1 - β) * x ^ (β - 1)) volume 0 (1 / 2) := by
    refine IntervalIntegrable.const_mul ?_ _
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < β - 1)
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
    (f := fun x : ℝ => (x * (1 - x)) ^ (β - 1))
    (g := fun x : ℝ => (2 : ℝ) ^ (1 - β) * x ^ (β - 1))
    (a := 0) (b := 1 / 2) (by norm_num) hsub hg ?_
  · have hval : ∫ x in (0 : ℝ)..(1 / 2), (x : ℝ) ^ (β - 1)
        = ((1 / 2 : ℝ) ^ β - 0 ^ β) / β := by
      simpa only [show β - 1 + 1 = β by ring] using
        integral_rpow (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) (r := β - 1)
          (Or.inl (by linarith : (-1 : ℝ) < β - 1))
    have hmaj : ∫ x in (0 : ℝ)..(1 / 2), (2 : ℝ) ^ (1 - β) * x ^ (β - 1)
        = (2 : ℝ) ^ (1 - β) * (((1 / 2 : ℝ) ^ β - 0 ^ β) / β) := by
      rw [intervalIntegral.integral_const_mul, hval]
    have hzero : (0 : ℝ) ^ β = 0 := Real.zero_rpow (by linarith : β ≠ 0)
    have hhalf : (1 / 2 : ℝ) ^ β = (2 : ℝ) ^ (-β) := by
      rw [Real.div_rpow (by norm_num) (by norm_num : (0 : ℝ) ≤ 2), Real.one_rpow, div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), one_mul]
    have hcomb : (2 : ℝ) ^ (1 - β) * ((2 : ℝ) ^ (-β) / β) = (2 : ℝ) ^ (1 - 2 * β) / β := by
      rw [← mul_div_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        show 1 - β + -β = 1 - 2 * β by ring]
    have hmaj2 : ∫ x in (0 : ℝ)..(1 / 2), (2 : ℝ) ^ (1 - β) * x ^ (β - 1)
        = (2 : ℝ) ^ (1 - 2 * β) / β := by
      rw [hmaj, hzero, sub_zero, hhalf, hcomb]
    rw [hmaj2] at hmono
    exact hmono
  · intro x hx
    have hx1 : (0 : ℝ) < x := hx.1
    have hx2 : x ≤ 1 / 2 := le_of_lt hx.2
    have hle : x / 2 ≤ x * (1 - x) := by nlinarith
    have hstep : (x * (1 - x)) ^ (β - 1) ≤ (x / 2) ^ (β - 1) :=
      Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < x / 2) hle (by linarith)
    have hdiv : (x / 2) ^ (β - 1) = (2 : ℝ) ^ (1 - β) * x ^ (β - 1) := by
      rw [Real.div_rpow hx1.le (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), show -(β - 1) = 1 - β by ring]
      ring
    linarith [hstep, hdiv]

private theorem beta_integral_le {β : ℝ} (hβ4 : 3 / 4 ≤ β) (hβ1 : β ≤ 1) :
    ∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ) ≤ (2 : ℝ) ^ (2 - 2 * β) / β := by
  have hβ0 : 0 < β := by linarith
  have hint := intervalIntegrable_kernel (β := β) hβ0
  have hhalf1 : IntervalIntegrable (fun x : ℝ => (x * (1 - x)) ^ (β - 1)) volume 0 (1 / 2) :=
    hint.mono_set (by
      intro y hy
      simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
        Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Icc] at hy ⊢
      constructor <;> linarith [hy.1, hy.2])
  have hhalf2 : IntervalIntegrable (fun x : ℝ => (x * (1 - x)) ^ (β - 1)) volume (1 / 2) 1 :=
    hint.mono_set (by
      intro y hy
      simp only [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
        Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Icc] at hy ⊢
      constructor <;> linarith [hy.1, hy.2])
  have hadd : (∫ x in (0 : ℝ)..(1 / 2), ((x * (1 - x)) ^ (β - 1) : ℝ))
      + (∫ x in (1 / 2 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ))
      = ∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ) :=
    intervalIntegral.integral_add_adjacent_intervals hhalf1 hhalf2
  have hsym : (∫ x in (1 / 2 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ))
      = ∫ x in (0 : ℝ)..(1 / 2), ((x * (1 - x)) ^ (β - 1) : ℝ) := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (a := (1 / 2 : ℝ)) (b := 1) (f := fun x : ℝ => ((x * (1 - x)) ^ (β - 1) : ℝ)) 1
    have hcongr : (∫ x in (1 / 2 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ))
        = ∫ x in (1 / 2 : ℝ)..1, (((1 - x) * (1 - (1 - x))) ^ (β - 1) : ℝ) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hx
      have : (1 - x) * (1 - (1 - x)) = x * (1 - x) := by ring
      rw [this]
    rw [hcongr, hcomp]
    norm_num
  have hhalf := half_integral_le hβ0 hβ1
  have h2 : (2 : ℝ) ^ (2 - 2 * β) / β = 2 * ((2 : ℝ) ^ (1 - 2 * β) / β) := by
    rw [show 2 - 2 * β = 1 - 2 * β + 1 by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring
  rw [← hadd, hsym, h2]
  linarith [hhalf]

/-! ## The elementary exponential bound and the leaf -/

private theorem four_rpow_le {u : ℝ} (hu0 : 0 ≤ u) (hu4 : u ≤ 1 / 4) :
    (2 : ℝ) ^ (2 * u) ≤ 1 + 3 * u := by
  have h2 : (2 : ℝ) ^ (2 * u) = Real.exp (2 * u * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  have hy0 : 0 ≤ 2 * u * Real.log 2 := by
    have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  have hy1 : |2 * u * Real.log 2| ≤ 1 := by
    have hL : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
    rw [abs_of_nonneg hy0]
    nlinarith
  have hstep : Real.exp (2 * u * Real.log 2) - 1 ≤ 2 * (2 * u * Real.log 2) := by
    have h1 : Real.exp (2 * u * Real.log 2) - 1 ≤ |Real.exp (2 * u * Real.log 2) - 1| :=
      le_abs_self _
    have hb := Real.abs_exp_sub_one_le (x := 2 * u * Real.log 2) hy1
    rw [abs_of_nonneg hy0] at hb
    linarith [h1, hb]
  have hLt : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
  rw [h2]
  nlinarith [hstep, hu0, hLt]

/-- LEAF. Step 2: at a real zero `β` with `3/4 ≤ β ≤ 1` the beta factor is real and the
combination `βC(β,β)·N^(2β-2)` differs from one by at most `8·(1-β)·log N` on either side.
This is the factor that turns the formula's main term into `𝔖(N)·N·(1 + χ(-1))`. -/
theorem leaf_kappa_between (N : ℕ) (hN : 2 ≤ N) {β : ℝ} (hβ : 3 / 4 ≤ β) (hβ' : β ≤ 1) :
    (betaC (β : ℂ) (β : ℂ)).im = 0 ∧
      1 - 8 * (1 - β) * Real.log N ≤ (betaC (β : ℂ) (β : ℂ)).re * (N : ℝ) ^ (2 * β - 2) ∧
      (betaC (β : ℂ) (β : ℂ)).re * (N : ℝ) ^ (2 * β - 2) ≤ 1 + 8 * (1 - β) * Real.log N := by
  have hβ0 : 0 < β := by linarith
  have heq := betaC_eq_integral (β := β) hβ0
  have hre : (betaC (β : ℂ) (β : ℂ)).re
      = ∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ) := by
    rw [heq]
    exact Complex.ofReal_re _
  have him : (betaC (β : ℂ) (β : ℂ)).im = 0 := by
    rw [heq]
    exact Complex.ofReal_im _
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set u : ℝ := 1 - β with hu
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  have hu4 : u ≤ 1 / 4 := by rw [hu]; linarith
  have hβu : β = 1 - u := by rw [hu]; ring
  rw [hre]
  refine ⟨him, ?_, ?_⟩
  · -- lower bound
    have h1 : (1 : ℝ) ≤ ∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ) :=
      one_le_beta_integral hβ hβ'
    have hpow_nonneg : (0 : ℝ) ≤ (N : ℝ) ^ (2 * β - 2) := Real.rpow_nonneg hNpos.le _
    have hpow_ge : 1 - 2 * u * Real.log N ≤ (N : ℝ) ^ (2 * β - 2) := by
      rw [Real.rpow_def_of_pos hNpos]
      have hexp : Real.log ((N : ℝ)) * (2 * β - 2) = -(2 * u * Real.log N) := by rw [hu]; ring
      rw [hexp]
      have h := Real.add_one_le_exp (-(2 * u * Real.log N))
      linarith [h]
    have hmul : (1 : ℝ) * (N : ℝ) ^ (2 * β - 2)
        ≤ (∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ)) * (N : ℝ) ^ (2 * β - 2) :=
      mul_le_mul_of_nonneg_right h1 hpow_nonneg
    have hmul' : (N : ℝ) ^ (2 * β - 2)
        ≤ (∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ)) * (N : ℝ) ^ (2 * β - 2) := by
      simpa using hmul
    have huLog : 0 ≤ u * Real.log N := mul_nonneg hu0 (Real.log_nonneg hN1)
    have : 1 - 8 * u * Real.log N ≤ 1 - 2 * u * Real.log N := by linarith
    calc 1 - 8 * (1 - β) * Real.log N = 1 - 8 * u * Real.log N := by rw [hu]
      _ ≤ (N : ℝ) ^ (2 * β - 2) := le_trans this hpow_ge
      _ ≤ (∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ)) * (N : ℝ) ^ (2 * β - 2) := hmul'
  · -- upper bound
    have hup : ∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ) ≤ (2 : ℝ) ^ (2 * u) / β := by
      have h := beta_integral_le hβ hβ'
      have he : (2 : ℝ) ^ (2 * u) = (2 : ℝ) ^ (2 - 2 * β) := by rw [hu]; ring_nf
      rw [he]
      exact h
    have hB1 : (1 : ℝ) ≤ ∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ) :=
      one_le_beta_integral hβ hβ'
    have hpow_le : (N : ℝ) ^ (2 * β - 2) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos hN1 ?_
      linarith
    have hmaj : (2 : ℝ) ^ (2 * u) / β ≤ 1 + 8 * u * Real.log N := by
      have hexp := four_rpow_le hu0 hu4
      have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
      have hLb : (0.6931471803 : ℝ) ≤ Real.log 2 := Real.log_two_gt_d9.le
      have hLt : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
      have hprod : 0 ≤ (Real.log N - 0.6931471803) * (1 / 4 - u) :=
        mul_nonneg (by linarith) (by linarith)
      have key : 1 + 3 * u ≤ β * (1 + 8 * u * Real.log N) := by
        rw [hβu]
        nlinarith [hprod, hu0, hu4, hLb, hlogN]
      calc (2 : ℝ) ^ (2 * u) / β
          ≤ (1 + 3 * u) / β := div_le_div_of_nonneg_right hexp hβ0.le
        _ ≤ (β * (1 + 8 * u * Real.log N)) / β := div_le_div_of_nonneg_right key hβ0.le
        _ = 1 + 8 * u * Real.log N := by field_simp
    have hle : (∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ)) * (N : ℝ) ^ (2 * β - 2)
        ≤ (∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left hpow_le (by linarith)
    have hle' : (∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ)) * (N : ℝ) ^ (2 * β - 2)
        ≤ ∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ) := by
      simpa using hle
    calc (∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ)) * (N : ℝ) ^ (2 * β - 2)
        ≤ ∫ x in (0 : ℝ)..1, ((x * (1 - x)) ^ (β - 1) : ℝ) := hle'
      _ ≤ (2 : ℝ) ^ (2 * u) / β := hup
      _ ≤ 1 + 8 * u * Real.log N := hmaj
      _ = 1 + 8 * (1 - β) * Real.log N := by rw [hu]


private lemma prod_one_sub_inv_ge (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (1 : ℝ) / ((S.card : ℝ) + 1) ≤ ∏ p ∈ S, (1 - ((p : ℝ))⁻¹) := by
  classical
  revert hS
  refine Finset.induction_on_max_value (id : ℕ → ℕ) S ?_ ?_
  · intro _
    simp
  · intro a s ha_notin hle ih hS
    have ha_prime : a.Prime := hS a (Finset.mem_insert_self a s)
    have hs_prime : ∀ p ∈ s, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hih : (1 : ℝ) / ((s.card : ℝ) + 1) ≤ ∏ p ∈ s, (1 - ((p : ℝ))⁻¹) := ih hs_prime
    rw [Finset.prod_insert ha_notin, Finset.card_insert_of_notMem ha_notin, Nat.cast_add,
      Nat.cast_one]
    have hgoal : (1 : ℝ) / ((s.card : ℝ) + 1 + 1) = 1 / ((s.card : ℝ) + 2) := by
      congr 1
      ring
    rw [hgoal]
    have ha2 : 2 ≤ a := ha_prime.two_le
    have hsub : s ⊆ Finset.Icc 2 (a - 1) := by
      intro x hx
      have hx1 : 2 ≤ x := (hs_prime x hx).two_le
      have hx2 : x ≤ a := hle x hx
      have hx3 : x ≠ a := fun h => ha_notin (h ▸ hx)
      simp only [Finset.mem_Icc]
      omega
    have hcard : s.card ≤ a - 2 := by
      have h1 := Finset.card_le_card hsub
      rwa [Nat.card_Icc] at h1
    have hja : (s.card : ℝ) + 2 ≤ (a : ℝ) := by
      have h1 : s.card + 2 ≤ a := by omega
      exact_mod_cast h1
    have hapos : (0 : ℝ) < (a : ℝ) := by
      have : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
      linarith
    have hjpos : (0 : ℝ) < (s.card : ℝ) + 2 := by positivity
    have hnonneg : (0 : ℝ) ≤ 1 - ((a : ℝ))⁻¹ := by
      have : ((a : ℝ))⁻¹ ≤ 1 := by
        rw [inv_le_one₀ hapos]
        linarith
      linarith
    have h1a : ((s.card : ℝ) + 1) / ((s.card : ℝ) + 2) ≤ 1 - ((a : ℝ))⁻¹ := by
      have h : (0 : ℝ) ≤ (1 - ((a : ℝ))⁻¹) - ((s.card : ℝ) + 1) / ((s.card : ℝ) + 2) := by
        rw [show (1 : ℝ) - ((a : ℝ))⁻¹ - ((s.card : ℝ) + 1) / ((s.card : ℝ) + 2)
            = ((a : ℝ) - ((s.card : ℝ) + 2)) / ((a : ℝ) * ((s.card : ℝ) + 2)) by
          field_simp
          ring]
        exact div_nonneg (by linarith) (by positivity)
      linarith
    have hstep : 1 / ((s.card : ℝ) + 2)
        ≤ (1 - ((a : ℝ))⁻¹) * (1 / ((s.card : ℝ) + 1)) := by
      have heq : ((s.card : ℝ) + 1) / ((s.card : ℝ) + 2) * (1 / ((s.card : ℝ) + 1))
          = 1 / ((s.card : ℝ) + 2) := by
        field_simp
      rw [← heq]
      exact mul_le_mul_of_nonneg_right h1a (by positivity)
    calc (1 : ℝ) / ((s.card : ℝ) + 2)
        ≤ (1 - ((a : ℝ))⁻¹) * (1 / ((s.card : ℝ) + 1)) := hstep
      _ ≤ (1 - ((a : ℝ))⁻¹) * ∏ p ∈ s, (1 - ((p : ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_left hih hnonneg

private lemma totient_cast_prod (n : ℕ) (_hn : n ≠ 0) :
    ((Nat.totient n : ℝ)) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - ((p : ℝ))⁻¹) := by
  have hq := Nat.totient_eq_mul_prod_factors n
  have h := congrArg (fun q : ℚ => (q : ℝ)) hq
  push_cast at h
  simpa using h

private lemma card_primeFactors_le_log (n : ℕ) (hn : n ≠ 0) :
    (n.primeFactors.card : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have hprod : ∏ p ∈ n.primeFactors, p ∣ n := Nat.prod_primeFactors_dvd n
  have hle : ∏ p ∈ n.primeFactors, p ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hprod
  have h2k : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
    have hstep : ∏ p ∈ n.primeFactors, 2 ≤ ∏ p ∈ n.primeFactors, p := by
      exact Finset.prod_le_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    simpa using hstep
  have hcast : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) := by
    have h1 : ((2 ^ n.primeFactors.card : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2k.trans hle
    simpa using h1
  have hlog : (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    have h1 : Real.log ((2 : ℝ) ^ n.primeFactors.card) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) hcast
    rwa [Real.log_pow] at h1
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).mpr hlog

private lemma log_two_gt_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

private lemma one_add_logb_sq_le (x : ℝ) (hx : 1 ≤ x) :
    (1 + Real.log x / Real.log 2) ^ 2 ≤ 81 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq0 : (0 : ℝ) ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx0.le _
  have hlogx : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have h1 := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    have h2 : x ^ (1 / 4 : ℝ) / (1 / 4) = 4 * x ^ (1 / 4 : ℝ) := by
      field_simp
    rwa [h2] at h1
  have hlogb : Real.log x / Real.log 2 ≤ 8 * x ^ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ hlog2]
    nlinarith [hlogx, log_two_gt_half, hq0]
  have hq1 : (1 : ℝ) ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hle9 : 1 + Real.log x / Real.log 2 ≤ 9 * x ^ (1 / 4 : ℝ) := by linarith
  have hnonneg : (0 : ℝ) ≤ 1 + Real.log x / Real.log 2 := by
    have h1 : 0 ≤ Real.log x := Real.log_nonneg hx
    positivity
  have h1 := pow_le_pow_left₀ hnonneg hle9 2
  have hsq : (9 * x ^ (1 / 4 : ℝ)) ^ 2 = 81 * Real.sqrt x := by
    have h1 : (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hx0.le]
      norm_num
    have h2 : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
    rw [mul_pow, h1, h2]
    norm_num
  rwa [hsq] at h1

private lemma totient_sq_growth (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t)
    (hnt : (81 * t) ^ 2 ≤ (n : ℝ)) : t * (n : ℝ) ≤ ((Nat.totient n : ℝ)) ^ 2 := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hprod := prod_one_sub_inv_ge n.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have htot := totient_cast_prod n hn0
  have hge : (n : ℝ) / ((n.primeFactors.card : ℝ) + 1) ≤ (Nat.totient n : ℝ) := by
    rw [htot, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hprod hnpos.le
  have hk : (n.primeFactors.card : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 :=
    card_primeFactors_le_log n hn0
  have hlogb := one_add_logb_sq_le (n : ℝ) (by exact_mod_cast hn)
  have hk0 : (0 : ℝ) ≤ (n.primeFactors.card : ℝ) := by positivity
  have hsq : ((n.primeFactors.card : ℝ) + 1) ^ 2 ≤ 81 * Real.sqrt (n : ℝ) := by nlinarith
  have hden : (0 : ℝ) < ((n.primeFactors.card : ℝ) + 1) ^ 2 := by positivity
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hstep1 : (n : ℝ) ^ 2 / (81 * Real.sqrt (n : ℝ))
      ≤ (n : ℝ) ^ 2 / ((n.primeFactors.card : ℝ) + 1) ^ 2 := by
    exact div_le_div_of_nonneg_left (by positivity) hden hsq
  have hstep2 : ((n : ℝ) / ((n.primeFactors.card : ℝ) + 1)) ^ 2
      ≤ ((Nat.totient n : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hge 2
  have hdiv : ((n : ℝ) / ((n.primeFactors.card : ℝ) + 1)) ^ 2
      = (n : ℝ) ^ 2 / ((n.primeFactors.card : ℝ) + 1) ^ 2 := div_pow ..
  rw [hdiv] at hstep2
  have hroot : (n : ℝ) * Real.sqrt (n : ℝ) / 81
      = (n : ℝ) ^ 2 / (81 * Real.sqrt (n : ℝ)) := by
    field_simp
    rw [Real.sq_sqrt hnpos.le]
  have hsqt : 81 * t ≤ Real.sqrt (n : ℝ) := by
    have h1 : Real.sqrt ((81 * t) ^ 2) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hnt
    rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 81 * t)] at h1
  have hlast : t * (n : ℝ) ≤ (n : ℝ) * Real.sqrt (n : ℝ) / 81 := by
    have h1 : (n : ℝ) * (81 * t) ≤ (n : ℝ) * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_left hsqt hnpos.le
    have h2 : t * (n : ℝ) = (n : ℝ) * (81 * t) / 81 := by field_simp
    rw [h2]
    exact div_le_div_of_nonneg_right h1 (by norm_num)
  rw [← hroot] at hstep1
  linarith [hstep1, hstep2, hlast]

private lemma exists_nat_rpow_ge (K : ℝ) (hK : 0 ≤ K) {s : ℝ} (hs : 0 < s) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → K ≤ (r : ℝ) ^ s := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / s)
  have hm0 : 0 < m := by
    have h1 : 0 < 1 / s := by positivity
    have h2 : (0 : ℝ) < (m : ℝ) := lt_trans h1 hm
    exact_mod_cast h2
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hle : 1 / (m : ℝ) ≤ s := by
    rw [div_le_iff₀ hmpos]
    have h1 : 1 / s < (m : ℝ) := hm
    rw [div_lt_iff₀ hs] at h1
    linarith
  refine ⟨max 1 ⌈K ^ m⌉₊, ?_⟩
  intro r hr
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
    have h1 : 1 ≤ r := le_trans (le_max_left _ _) hr
    exact_mod_cast h1
  have hKceil : K ^ m ≤ (r : ℝ) := by
    have h1 : ⌈K ^ m⌉₊ ≤ r := le_trans (le_max_right _ _) hr
    exact (Nat.le_ceil (K ^ m)).trans (by exact_mod_cast h1)
  have hKpow : K = (K ^ m : ℝ) ^ (1 / (m : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK, mul_one_div,
      div_self (ne_of_gt hmpos), Real.rpow_one]
  rw [hKpow]
  calc (K ^ m : ℝ) ^ (1 / (m : ℝ)) ≤ (r : ℝ) ^ (1 / (m : ℝ)) :=
        Real.rpow_le_rpow (by positivity) hKceil (by positivity)
    _ ≤ (r : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le hr1 hle

/-- The scalar rearrangement behind term 1 of the counting leaf. -/
private lemma err_scalar1 {C δ S N : ℝ} (hC : C ≠ 0) :
    C * (S * (2 * N) * (δ / (24 * C))) = (δ / 12) * (S * N) := by
  field_simp
  ring

/-- The scalar rearrangement behind term 2 of the counting leaf. -/
private lemma err_scalar2 {C δ S N : ℝ} (hC : C ≠ 0) :
    C * (S * N * (δ / (12 * C))) = (δ / 12) * (S * N) := by
  field_simp

/-- The scalar rearrangement behind term 3 of the counting leaf. -/
private lemma err_scalar3 {C δ X : ℝ} (hC : C ≠ 0) (hδ : δ ≠ 0) :
    C * (X / (48 * C / δ)) = δ * X / 48 := by
  field_simp

/-- `δ·X/48 = (δ/12)·(X/4)`. -/
private lemma err_scalar4 (δ X : ℝ) : δ * X / 48 = (δ / 12) * (X / 4) := by
  ring

/-- The facts about `r`, `N` that the counting leaf uses, from `r ≥ 1`, `A > 0` and the
dyadic membership `N ∈ Icc ⌈X/2⌉₊ ⌊X⌋₊` with `X = r^A`. -/
private theorem leaf_setup {A e : ℝ} {r N : ℕ} (hr1 : 1 ≤ r) (hA0 : 0 < A) (_he : 0 ≤ e)
    (hN : N ∈ Finset.Icc ⌈(r : ℝ) ^ A / 2⌉₊ ⌊(r : ℝ) ^ A⌋₊) (hEven : Even N) :
    (1 : ℝ) ≤ (r : ℝ) ∧ (0 : ℝ) < (r : ℝ) ^ A ∧ (N : ℝ) ≤ (r : ℝ) ^ A ∧
      (r : ℝ) ^ A ≤ 2 * (N : ℝ) ∧ 2 ≤ N ∧ (1 / 2 : ℝ) ≤ singular N ∧
      (0 : ℝ) ≤ Real.log ((r : ℝ) ^ A) := by
  have hr1' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hrA1 : (1 : ℝ) ≤ (r : ℝ) ^ A := Real.one_le_rpow hr1' hA0.le
  have hrA0 : (0 : ℝ) < (r : ℝ) ^ A := lt_of_lt_of_le zero_lt_one hrA1
  have hmem := Finset.mem_Icc.mp hN
  have hN1 : 1 ≤ N := by
    have h1 : 1 ≤ ⌈(r : ℝ) ^ A / 2⌉₊ := by
      rw [Nat.one_le_ceil_iff]
      linarith
    omega
  have hN2 : 2 ≤ N := by
    obtain ⟨j, hj⟩ := hEven
    omega
  have hNrA : (N : ℝ) ≤ (r : ℝ) ^ A := by
    have h1 : (N : ℝ) ≤ (⌊(r : ℝ) ^ A⌋₊ : ℝ) := by exact_mod_cast hmem.2
    exact h1.trans (Nat.floor_le hrA0.le)
  have hrAN : (r : ℝ) ^ A ≤ 2 * (N : ℝ) := by
    have h1 : (r : ℝ) ^ A / 2 ≤ (⌈(r : ℝ) ^ A / 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(r : ℝ) ^ A / 2⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmem.1
    linarith
  exact ⟨hr1', hrA0, hNrA, hrAN, hN2, leaf_singular_lower N hEven hN2, Real.log_nonneg hrA1⟩

/-- LEAF. Step 3: the three error terms of the analytic formula — the `X`-term carrying
`(e·log X)^c'`, the conductor term `𝔖(N)·N·r/φ(r)^2` and the minor term `X^(1-ε₀)` — are in
total at most `(δ/4)·𝔖(N)·N` on the dyadic interval, once the conductor is large enough.
This is where the constant `c = c(δ)` and the threshold `r₀ = r₀(A,δ)` come from. -/
theorem leaf_error_domination (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (C c' ε₀ h : ℝ)
    (hc' : 0 < c') (hε₀ : 0 < ε₀) (hh : 0 < h) :
    ∃ c : ℝ, 0 < c ∧ c < h ∧ c ≤ δ / 32 ∧ ∀ A : ℝ, 5 / 2 < A → ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      ∀ (N : ℕ) (e : ℝ), 0 ≤ e → e * Real.log ((r : ℝ) ^ A) ≤ c →
        N ∈ Finset.Icc ⌈(r : ℝ) ^ A / 2⌉₊ ⌊(r : ℝ) ^ A⌋₊ → Even N →
          C * (singular N * (r : ℝ) ^ A * ((e * Real.log ((r : ℝ) ^ A)) ^ c') +
                singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2 +
                ((r : ℝ) ^ A) ^ (1 - ε₀)) ≤ (δ / 4) * (singular N * N) := by
  rcases le_or_gt C 0 with hC | hC
  · -- `C ≤ 0`: the left side is nonpositive
    refine ⟨min (h / 2) (δ / 32), lt_min (by linarith) (by linarith), ?_, min_le_right _ _, ?_⟩
    · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · intro A hA
      refine ⟨1, ?_⟩
      intro r hr N e he hec hN hEven
      obtain ⟨hR1, hrA0, hNrA, hrAN, hN2, hS, hlog0⟩ :=
        leaf_setup (A := A) (e := e) (r := r) (N := N) (by omega) (by linarith) he hN hEven
      have hS0 : (0 : ℝ) ≤ singular N := by linarith
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      have hq0 : (0 : ℝ) ≤ (e * Real.log ((r : ℝ) ^ A)) ^ c' :=
        Real.rpow_nonneg (mul_nonneg he hlog0) _
      have hX0 : (0 : ℝ) ≤ singular N * (r : ℝ) ^ A * ((e * Real.log ((r : ℝ) ^ A)) ^ c') +
          singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2 +
            ((r : ℝ) ^ A) ^ (1 - ε₀) := by
        have h1 : (0 : ℝ) ≤ singular N * (r : ℝ) ^ A * ((e * Real.log ((r : ℝ) ^ A)) ^ c') :=
          mul_nonneg (mul_nonneg hS0 hrA0.le) hq0
        have h2 : (0 : ℝ) ≤ singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2 :=
          div_nonneg (mul_nonneg (mul_nonneg hS0 hN0) (by linarith : (0:ℝ) ≤ (r:ℝ)))
            (by positivity)
        have h3 : (0 : ℝ) ≤ ((r : ℝ) ^ A) ^ (1 - ε₀) := Real.rpow_nonneg hrA0.le _
        linarith
      have hSN : (0 : ℝ) ≤ singular N * N := mul_nonneg hS0 hN0
      have h1 : C * (singular N * (r : ℝ) ^ A * ((e * Real.log ((r : ℝ) ^ A)) ^ c') +
          singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2 +
            ((r : ℝ) ^ A) ^ (1 - ε₀)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC hX0
      have h2 : (0 : ℝ) ≤ (δ / 4) * (singular N * N) := mul_nonneg (by linarith) hSN
      linarith
  · -- `C > 0`
    have hqpos : 0 < δ / (24 * C) := by positivity
    set c₀ : ℝ := min (min (h / 2) (δ / 32)) (min 1 ((δ / (24 * C)) ^ (1 / c'))) with hc₀
    have hc₀0 : 0 < c₀ := by
      rw [hc₀]
      exact lt_min (lt_min (by linarith) (by linarith))
        (lt_min one_pos (Real.rpow_pos_of_pos hqpos _))
    have hc₀1 : c₀ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have hc₀x : c₀ ≤ (δ / (24 * C)) ^ (1 / c') := (min_le_right _ _).trans (min_le_right _ _)
    have hcc : c₀ ^ c' ≤ δ / (24 * C) := by
      have hx : ((δ / (24 * C)) ^ (1 / c')) ^ c' = δ / (24 * C) := by
        rw [← Real.rpow_mul (le_of_lt hqpos)]
        rw [one_div_mul_cancel (ne_of_gt hc'), Real.rpow_one]
      calc c₀ ^ c' ≤ ((δ / (24 * C)) ^ (1 / c')) ^ c' := Real.rpow_le_rpow hc₀0.le hc₀x hc'.le
        _ = δ / (24 * C) := hx
    refine ⟨c₀, hc₀0, ?_, (min_le_left _ _).trans (min_le_right _ _), ?_⟩
    · exact lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
    · intro A hA
      have hA0 : 0 < A := by linarith
      have hs : 0 < A * ε₀ := by positivity
      obtain ⟨rK, hrK⟩ := exists_nat_rpow_ge (48 * C / δ) (by positivity) hs
      refine ⟨max (max rK 1) ⌈(81 * (12 * C / δ)) ^ 2⌉₊, ?_⟩
      intro r hr N e he hec hN hEven
      have hrKle : rK ≤ r :=
        le_trans (le_trans (le_max_left rK 1) (le_max_left (max rK 1) _)) hr
      have h1le : 1 ≤ r :=
        le_trans (le_trans (le_max_right rK 1) (le_max_left (max rK 1) _)) hr
      have hceil : ⌈(81 * (12 * C / δ)) ^ 2⌉₊ ≤ r := le_trans (le_max_right _ _) hr
      obtain ⟨hR1, hrA0, hNrA, hrAN, hN2, hS, hlog0⟩ :=
        leaf_setup (A := A) (e := e) (r := r) (N := N) h1le hA0 he hN hEven
      have hRpos : (0 : ℝ) < (r : ℝ) := by linarith
      have hS0 : (0 : ℝ) ≤ singular N := by linarith
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      have hSN : (0 : ℝ) ≤ singular N * N := mul_nonneg hS0 hN0
      have hphi2 : (0 : ℝ) < (Nat.totient r : ℝ) ^ 2 := by
        have h1 : 0 < Nat.totient r := Nat.totient_pos.mpr (by omega)
        have h2 : (0 : ℝ) < (Nat.totient r : ℝ) := by exact_mod_cast h1
        positivity
      -- the analytic input `e·log X ≤ c₀` and the choice of `c₀`
      have hq0 : (0 : ℝ) ≤ e * Real.log ((r : ℝ) ^ A) := mul_nonneg he hlog0
      have hq0' : (0 : ℝ) ≤ (e * Real.log ((r : ℝ) ^ A)) ^ c' := Real.rpow_nonneg hq0 _
      have hqle : (e * Real.log ((r : ℝ) ^ A)) ^ c' ≤ δ / (24 * C) :=
        (Real.rpow_le_rpow hq0 hec hc'.le).trans hcc
      -- term 1: `C·𝔖(N)·X·(e·log X)^c'`
      have hT1 : C * (singular N * (r : ℝ) ^ A * ((e * Real.log ((r : ℝ) ^ A)) ^ c'))
          ≤ (δ / 12) * (singular N * N) := by
        have ha : (r : ℝ) ^ A * ((e * Real.log ((r : ℝ) ^ A)) ^ c')
            ≤ (2 * (N : ℝ)) * (δ / (24 * C)) :=
          mul_le_mul hrAN hqle hq0' (by positivity)
        have h1 : singular N * (r : ℝ) ^ A * ((e * Real.log ((r : ℝ) ^ A)) ^ c')
            ≤ singular N * (2 * (N : ℝ)) * (δ / (24 * C)) := by
          calc singular N * (r : ℝ) ^ A * ((e * Real.log ((r : ℝ) ^ A)) ^ c')
              = singular N * ((r : ℝ) ^ A * ((e * Real.log ((r : ℝ) ^ A)) ^ c')) := by ring
            _ ≤ singular N * ((2 * (N : ℝ)) * (δ / (24 * C))) := mul_le_mul_of_nonneg_left ha hS0
            _ = singular N * (2 * (N : ℝ)) * (δ / (24 * C)) := by ring
        calc C * (singular N * (r : ℝ) ^ A * ((e * Real.log ((r : ℝ) ^ A)) ^ c'))
            ≤ C * (singular N * (2 * (N : ℝ)) * (δ / (24 * C))) :=
              mul_le_mul_of_nonneg_left h1 hC.le
          _ = (δ / 12) * (singular N * N) :=
              err_scalar1 (ne_of_gt hC)
      -- term 2: `C·𝔖(N)·N·r/φ(r)^2`
      have htot := totient_sq_growth r (by omega) (12 * C / δ) (by positivity)
        ((Nat.le_ceil _).trans (by exact_mod_cast hceil))
      have hrho : (r : ℝ) / (Nat.totient r : ℝ) ^ 2 ≤ δ / (12 * C) := by
        rw [div_le_iff₀ hphi2]
        have ht1 : (δ / (12 * C)) * (12 * C / δ) = 1 := by field_simp
        have h1 : (δ / (12 * C)) * ((12 * C / δ) * (r : ℝ))
            ≤ (δ / (12 * C)) * (Nat.totient r : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left htot (by positivity)
        have h2 : (δ / (12 * C)) * ((12 * C / δ) * (r : ℝ)) = (r : ℝ) := by
          rw [← mul_assoc, ht1, one_mul]
        linarith [h1, h2]
      have hT2 : C * (singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2)
          ≤ (δ / 12) * (singular N * N) := by
        have h1 : singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2
            ≤ singular N * N * (δ / (12 * C)) := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hrho hSN
        calc C * (singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2)
            ≤ C * (singular N * N * (δ / (12 * C))) := mul_le_mul_of_nonneg_left h1 hC.le
          _ = (δ / 12) * (singular N * N) :=
              err_scalar2 (ne_of_gt hC)
      -- term 3: `C·X^(1-ε₀)`
      have hrs : 48 * C / δ ≤ ((r : ℝ) ^ A) ^ ε₀ := by
        rw [← Real.rpow_mul hRpos.le]
        exact hrK r hrKle
      have hpow : ((r : ℝ) ^ A) ^ (1 - ε₀) = (r : ℝ) ^ A / ((r : ℝ) ^ A) ^ ε₀ := by
        rw [Real.rpow_sub hrA0, Real.rpow_one]
      have h3a : ((r : ℝ) ^ A) ^ (1 - ε₀) ≤ (r : ℝ) ^ A / (48 * C / δ) := by
        rw [hpow]
        exact div_le_div_of_nonneg_left hrA0.le (by positivity) hrs
      have h3b : C * ((r : ℝ) ^ A / (48 * C / δ)) = δ * (r : ℝ) ^ A / 48 :=
        err_scalar3 (ne_of_gt hC) (ne_of_gt hδ)
      have hSN' : (r : ℝ) ^ A / 4 ≤ singular N * (N : ℝ) := by
        have h1 := mul_le_mul hS hrAN (le_of_lt hrA0) (by linarith : (0 : ℝ) ≤ singular N)
        nlinarith [h1]
      have hT3 : C * ((r : ℝ) ^ A) ^ (1 - ε₀) ≤ (δ / 12) * (singular N * N) := by
        calc C * ((r : ℝ) ^ A) ^ (1 - ε₀) ≤ C * ((r : ℝ) ^ A / (48 * C / δ)) :=
              mul_le_mul_of_nonneg_left h3a hC.le
          _ = δ * (r : ℝ) ^ A / 48 := h3b
          _ = (δ / 12) * ((r : ℝ) ^ A / 4) := err_scalar4 δ _
          _ ≤ (δ / 12) * (singular N * N) :=
              mul_le_mul_of_nonneg_left hSN' (by linarith)
      have hsplit : C * (singular N * (r : ℝ) ^ A * ((e * Real.log ((r : ℝ) ^ A)) ^ c') +
            singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2 + ((r : ℝ) ^ A) ^ (1 - ε₀))
          = C * (singular N * (r : ℝ) ^ A * ((e * Real.log ((r : ℝ) ^ A)) ^ c'))
            + C * (singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2)
            + C * (((r : ℝ) ^ A) ^ (1 - ε₀)) := by ring
      rw [hsplit]
      have hthree : 3 * ((δ / 12) * (singular N * N)) = (δ / 4) * (singular N * N) := by ring
      linarith [hT1, hT2, hT3, hthree]

/-- LEAF. Step 4: a primitive character of conductor at least two has no zero of its
L-function at or beyond one, so only the range `1 - c/log X < β < 1` needs the counting step. -/
theorem leaf_LFunction_ne_zero_ge_one {r : ℕ} [NeZero r] (hr : 2 ≤ r) (χ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) {β : ℝ} (hβ : 1 ≤ β) : DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  have hχne : χ ≠ 1 := by
    intro h1
    have hc : χ.conductor = 1 := (DirichletCharacter.eq_one_iff_conductor_eq_one).mp h1
    rw [DirichletCharacter.isPrimitive_def] at hχ
    omega
  refine DirichletCharacter.LFunction_ne_zero_of_one_le_re (s := (β : ℂ)) χ (Or.inl hχne) ?_
  simpa using hβ


/-! ## Private steps of the assembly -/

/-- A real number, read inside the complex numbers, has its absolute value as norm. -/
private theorem norm_ofReal_eq_abs (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  first
    | rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_sq_eq_abs]
    | simpa using RCLike.norm_ofReal (K := ℂ) x
    | simp

/-- A two-sided `δ/4` estimate for the beta factor plus a `δ/4` analytic remainder contradict
the two-sided range of the sparse input, for either sign of the character at `-1`. -/
private theorem split_norm_step {a s k δ : ℝ} {z : ℂ} (hz : z = 1 ∨ z = -1) (hs : 0 < s)
    (hδ : 0 < δ) (hmain : ‖(a : ℂ) - (s : ℂ) - z * (s : ℂ) * (k : ℂ)‖ ≤ (δ / 4) * s)
    (hk : |k - 1| ≤ δ / 4) : ‖(a : ℂ) - (1 + z) * (s : ℂ)‖ < δ * s := by
  have hz1 : ‖z‖ = 1 := by rcases hz with h | h <;> simp [h]
  have hcast : (k : ℂ) - 1 = ((k - 1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one]
  have hshift : ‖z * (s : ℂ) * ((k : ℂ) - 1)‖ = s * |k - 1| := by
    have h1 : ‖z * (s : ℂ) * ((k : ℂ) - 1)‖ = ‖z‖ * ‖(s : ℂ)‖ * ‖((k : ℂ) - 1)‖ := by
      rw [norm_mul, norm_mul]
    rw [h1, hz1, hcast, one_mul, norm_ofReal_eq_abs s, norm_ofReal_eq_abs (k - 1),
      abs_of_pos hs]
  have hsplit : (a : ℂ) - (1 + z) * (s : ℂ)
      = ((a : ℂ) - (s : ℂ) - z * (s : ℂ) * (k : ℂ)) + z * (s : ℂ) * ((k : ℂ) - 1) := by
    ring
  have h1 : s * |k - 1| ≤ s * (δ / 4) := mul_le_mul_of_nonneg_left hk hs.le
  rw [hsplit]
  calc ‖((a : ℂ) - (s : ℂ) - z * (s : ℂ) * (k : ℂ)) + z * (s : ℂ) * ((k : ℂ) - 1)‖
      ≤ ‖(a : ℂ) - (s : ℂ) - z * (s : ℂ) * (k : ℂ)‖ + ‖z * (s : ℂ) * ((k : ℂ) - 1)‖ :=
        norm_add_le _ _
    _ ≤ (δ / 4) * s + s * |k - 1| := by rw [hshift]; linarith
    _ ≤ (δ / 4) * s + s * (δ / 4) := by linarith
    _ < δ * s := by nlinarith

/-- The beta factor at a real argument is the real number given by its real part. -/
private theorem betaC_of_real {β : ℝ} (him : (betaC (β : ℂ) (β : ℂ)).im = 0) :
    betaC (β : ℂ) (β : ℂ) = (((betaC (β : ℂ) (β : ℂ)).re : ℝ) : ℂ) := by
  refine Complex.ext ?_ ?_
  · simp
  · simpa using him

/-! ## Assembly -/

/-- Theorem 8.2, proved from the four leaves: the sparse two-sided Hardy-Littlewood input on
the multiples of the conductor rules out real zeros of a primitive real character beyond
`1 - c/log X`. -/
theorem theorem82_split : Theorem82 := by
  intro δ hδ0 hδ1
  obtain ⟨h, c', ε₀, C, hh, hc', hε₀, hrest⟩ := prop81 (2 / 5) (by norm_num) (by norm_num)
  obtain ⟨c, hc0, hch, hcδ, hdom⟩ := leaf_error_domination δ hδ0 hδ1 C c' ε₀ h hc' hε₀ hh
  refine ⟨c, hc0, ?_⟩
  intro A hA
  obtain ⟨hA1, hεpos, hεlt⟩ := thm82_arith hA
  obtain ⟨Cε, hCε⟩ := hrest ((1 - 1 / A - 3 / 5) / 2) hεpos
  obtain ⟨r₀, hr₀⟩ := hdom A hA
  obtain ⟨r₁, hr₁⟩ := even_multiples_growth107 A hA (max Cε 0) (le_max_right _ _)
  refine ⟨max (max r₀ r₁) 2, ?_⟩
  intro r _ hr
  intro hcount
  intro χ hχprim hχreal β hβzero
  by_contra hcon
  simp only [not_le] at hcon
  -- scalar facts about the conductor and the scale
  have hr2 : 2 ≤ r := (le_max_right (max r₀ r₁) 2).trans hr
  have hr0r : r₀ ≤ r := (le_max_left r₀ r₁).trans ((le_max_left (max r₀ r₁) 2).trans hr)
  have hr1r : r₁ ≤ r := (le_max_right r₀ r₁).trans ((le_max_left (max r₀ r₁) 2).trans hr)
  have hr1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (show 1 < r by omega)
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hX2 : 2 ≤ (r : ℝ) ^ A := by
    have h2r : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    have h2A : (2 : ℝ) ≤ (2 : ℝ) ^ A := by
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2 : ℝ) ^ A := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    exact h2A.trans (Real.rpow_le_rpow (by norm_num) h2r hA0.le)
  have hlogX : 0 < Real.log ((r : ℝ) ^ A) := Real.log_pos (by linarith)
  have hlogX1 : 1 ≤ Real.log ((r : ℝ) ^ A) := by
    have hX4 : (4 : ℝ) ≤ (r : ℝ) ^ A := by
      have h2r : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
      have h24 : (4 : ℝ) ≤ (2 : ℝ) ^ A := by
        calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num [Real.rpow_two]
          _ ≤ (2 : ℝ) ^ A := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      exact h24.trans (Real.rpow_le_rpow (by norm_num) h2r hA0.le)
    have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
      have hsplit : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring
      rw [hsplit]
      nlinarith [Real.log_two_gt_d9]
    exact hlog4.trans (Real.log_le_log (by norm_num) hX4)
  have hcond : (r : ℝ) ≤ ((r : ℝ) ^ A) ^ (2 / 5 : ℝ) := (thm82_cond_lt_R hA hr1).le
  rcases lt_or_ge β 1 with hβlt | hβge
  · -- the zero sits in the interval (1 - c/log X, 1)
    have he0 : 0 < 1 - β := by linarith
    have helog : (1 - β) * Real.log ((r : ℝ) ^ A) ≤ c := by
      have h1 : 1 - β < c / Real.log ((r : ℝ) ^ A) := by linarith
      exact ((lt_div_iff₀ hlogX).mp h1).le
    have hβ34 : 3 / 4 ≤ β := by
      have h1 : 1 - β ≤ c / Real.log ((r : ℝ) ^ A) := (le_div_iff₀ hlogX).mpr helog
      have h2 : c / Real.log ((r : ℝ) ^ A) ≤ c := by
        rw [div_le_iff₀ hlogX]
        nlinarith [hc0]
      have h3 : c ≤ 1 / 32 := by linarith
      linarith
    -- the two exceptional sets
    set S : Finset ℕ := evenMultiples107 r ((r : ℝ) ^ A) with hS
    set B : Finset ℕ :=
      S.filter (fun N => ¬ (δ * singular N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * singular N * N)) with hB
    set Ef : Finset ℕ := (Finset.Icc ⌈(r : ℝ) ^ A / 2⌉₊ ⌊(r : ℝ) ^ A⌋₊).filter
      (fun N => Even N ∧
        ¬ ‖(r2 N : ℂ) - singular N * N - genSing χ χ N * betaC (β : ℂ) (β : ℂ) *
            (N : ℂ) ^ (2 * (β : ℂ) - 1)‖ ≤
          C * (singular N * (r : ℝ) ^ A * (((1 - β) * Real.log ((r : ℝ) ^ A)) ^ c') +
            singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2 +
            ((r : ℝ) ^ A) ^ (1 - ε₀))) with hEf
    -- the sparse input counts `B`
    have hBeq : B = (Finset.Icc ⌈(r : ℝ) ^ A / 2⌉₊ ⌊(r : ℝ) ^ A⌋₊).filter
        (fun N => Even N ∧ r ∣ N ∧
          ¬ (δ * singular N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * singular N * N)) := by
      ext N
      simp only [hB, hS, evenMultiples107, Finset.mem_filter, and_assoc]
    have hBcard : (B.card : ℝ) ≤ ((r : ℝ) ^ A) ^ (3 / 5 : ℝ) := by
      rw [hBeq]
      exact hcount
    -- the analytic formula counts `Ef`
    have hstep := hCε ((r : ℝ) ^ A) hX2 r χ (1 - β) hχprim hχreal hcond he0
      ((lt_div_iff₀ hlogX).mpr (by linarith))
      (by simpa only [show (1 : ℝ) - (1 - β) = β from by ring] using hβzero)
    have hEcard : (Ef.card : ℝ) ≤ Cε * ((r : ℝ) ^ A) ^ (3 / 5 + (1 - 1 / A - 3 / 5) / 2) := by
      rw [hEf]
      simpa only [show (1 : ℝ) - (1 - β) = β from by ring] using hstep
    -- more multiples than both exceptional sets together
    have hSg : (max Cε 0) * ((r : ℝ) ^ A) ^ (3 / 5 + (1 - 1 / A - 3 / 5) / 2) +
        ((r : ℝ) ^ A) ^ (3 / 5 : ℝ) < (S.card : ℝ) := by
      rw [hS]
      exact hr₁ r hr1r
    have hE2 : (Ef.card : ℝ) ≤
        (max Cε 0) * ((r : ℝ) ^ A) ^ (3 / 5 + (1 - 1 / A - 3 / 5) / 2) :=
      hEcard.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hcard : (B.card : ℝ) + (Ef.card : ℝ) < (S.card : ℝ) := by linarith
    obtain ⟨N, hNS, hNB, hNE⟩ := exists_outside_two107 S B Ef hcard
    have hNS' : N ∈ evenMultiples107 r ((r : ℝ) ^ A) := hS ▸ hNS
    have hNB' : N ∉ S.filter
        (fun N => ¬ (δ * singular N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * singular N * N)) := hB ▸ hNB
    have hNE' : N ∉ (Finset.Icc ⌈(r : ℝ) ^ A / 2⌉₊ ⌊(r : ℝ) ^ A⌋₊).filter
        (fun N => Even N ∧
          ¬ ‖(r2 N : ℂ) - singular N * N - genSing χ χ N * betaC (β : ℂ) (β : ℂ) *
              (N : ℂ) ^ (2 * (β : ℂ) - 1)‖ ≤
            C * (singular N * (r : ℝ) ^ A * (((1 - β) * Real.log ((r : ℝ) ^ A)) ^ c') +
              singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2 +
              ((r : ℝ) ^ A) ^ (1 - ε₀))) := hEf ▸ hNE
    obtain ⟨hNIcc, hNEv, hNdiv⟩ : N ∈ Finset.Icc ⌈(r : ℝ) ^ A / 2⌉₊ ⌊(r : ℝ) ^ A⌋₊ ∧
        Even N ∧ r ∣ N := by
      simpa only [evenMultiples107, Finset.mem_filter] using hNS'
    -- the range of the sparse input at this multiple
    have hgood : δ * singular N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * singular N * N := by
      by_contra hbad
      exact hNB' (Finset.mem_filter.mpr ⟨hNS, hbad⟩)
    have hrange : δ * (singular N * N) ≤ r2 N ∧ r2 N ≤ (2 - δ) * (singular N * N) :=
      ⟨by simpa only [mul_assoc] using hgood.1, by simpa only [mul_assoc] using hgood.2⟩
    -- the analytic formula at this multiple
    have hnorm : ‖(r2 N : ℂ) - singular N * N - genSing χ χ N * betaC (β : ℂ) (β : ℂ) *
        (N : ℂ) ^ (2 * (β : ℂ) - 1)‖ ≤
        C * (singular N * (r : ℝ) ^ A * (((1 - β) * Real.log ((r : ℝ) ^ A)) ^ c') +
          singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2 +
          ((r : ℝ) ^ A) ^ (1 - ε₀)) := by
      by_contra hbad
      exact hNE' (Finset.mem_filter.mpr ⟨hNIcc, hNEv, hbad⟩)
    -- sizes
    have hNge : 1 ≤ N := by
      have h1 : 0 < ⌈(r : ℝ) ^ A / 2⌉₊ := Nat.ceil_pos.mpr (by linarith)
      have h2 := (Finset.mem_Icc.mp hNIcc).1
      omega
    have hN2 : 2 ≤ N := by
      obtain ⟨k, hk⟩ := hNEv
      omega
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hNX : (N : ℝ) ≤ (r : ℝ) ^ A :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hNIcc).2).trans (Nat.floor_le (by positivity))
    have hlogN : Real.log (N : ℝ) ≤ Real.log ((r : ℝ) ^ A) :=
      Real.log_le_log hNpos hNX
    have h8 : 8 * (1 - β) * Real.log (N : ℝ) ≤ δ / 4 := by
      have hstep1 : 8 * ((1 - β) * Real.log (N : ℝ)) ≤
          8 * ((1 - β) * Real.log ((r : ℝ) ^ A)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogN he0.le) (by norm_num)
      have hstep2 : 8 * ((1 - β) * Real.log ((r : ℝ) ^ A)) ≤ 8 * c :=
        mul_le_mul_of_nonneg_left helog (by norm_num)
      have hstep3 : 8 * c ≤ δ / 4 := by linarith
      calc 8 * (1 - β) * Real.log (N : ℝ) = 8 * ((1 - β) * Real.log (N : ℝ)) := by ring
        _ ≤ δ / 4 := by linarith
    -- the beta factor is one up to `δ/4`
    obtain ⟨hkim, hklo, hkhi⟩ := leaf_kappa_between N hN2 hβ34 hβlt.le
    set k : ℝ := (betaC (β : ℂ) (β : ℂ)).re * (N : ℝ) ^ (2 * β - 2) with hkdef
    have hk1 : |k - 1| ≤ δ / 4 := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    -- the formula's third term is `χ(-1)·(𝔖(N)·N)·k`
    have hthird : genSing χ χ N * betaC (β : ℂ) (β : ℂ) * (N : ℂ) ^ (2 * (β : ℂ) - 1)
        = χ (-1) * ((singular N * N : ℝ) : ℂ) * (k : ℂ) := by
      have hgen : genSing χ χ N = χ (-1) * ((singular N : ℂ)) :=
        facts81.2 r χ hχprim hχreal N hNEv hN2 hNdiv
      have hpow : (N : ℂ) ^ (2 * (β : ℂ) - 1) = (((N : ℝ) ^ (2 * β - 1) : ℝ) : ℂ) := by
        rw [show (2 : ℂ) * (β : ℂ) - 1 = ((2 * β - 1 : ℝ) : ℂ) from by push_cast; ring]
        exact (Complex.ofReal_cpow hNpos.le (2 * β - 1)).symm
      have hbc := betaC_of_real hkim
      have hNpow : (N : ℝ) ^ (2 * β - 1) = (N : ℝ) * (N : ℝ) ^ (2 * β - 2) := by
        rw [show 2 * β - 1 = (2 * β - 2) + 1 by ring, Real.rpow_add hNpos, Real.rpow_one]
        ring
      rw [hgen, hbc, hpow, hNpow, hkdef]
      push_cast
      ring_nf
    have hnorm' : ‖(r2 N : ℂ) - ((singular N * N : ℝ) : ℂ) - χ (-1) *
        ((singular N * N : ℝ) : ℂ) * (k : ℂ)‖ ≤
        C * (singular N * (r : ℝ) ^ A * (((1 - β) * Real.log ((r : ℝ) ^ A)) ^ c') +
          singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2 +
          ((r : ℝ) ^ A) ^ (1 - ε₀)) := by
      rw [hthird] at hnorm
      simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using hnorm
    -- the error terms are dominated by the main term
    have herr := hr₀ r hr0r N (1 - β) he0.le helog hNIcc hNEv
    -- contradiction
    have hs : 0 < singular N * N := by
      have h1 := leaf_singular_lower N hNEv hN2
      have h2 : (0 : ℝ) < (N : ℝ) := hNpos
      nlinarith
    refine sign_contradiction107 hδ0 hrange (character_neg_one107 χ) ?_
    refine split_norm_step (character_neg_one107 χ) hs hδ0 ?_ hk1
    exact hnorm'.trans herr
  · exact absurd hβzero (leaf_LFunction_ne_zero_ge_one hr2 χ hχprim hβge)

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.theorem82_split
