/-
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261019T2314Z-cloud29, unit U-5793, paper P0097.

# Zinoviev's smoothed prime sum as a series, and its two integrals

`SZ N α = Σ'_{n ≥ 0} Λ(n) e^{-n/N} e(nα)`, Zinoviev's `S`, p. 335, with `α ↦ -α`, which changes
neither `∫₀¹ |S|²` nor, after `α ↦ -α` mod 1, the integral `∫₀¹ S³ e(Nα)`. Here:

* `SZ_sq_le`: `∫₀¹ ‖SZ(α)‖² dα ≤ 0.96 N ln N` for `N ≥ 10^20`, (3.17) with Lemma 1.5;
* `SZ_cube`: `∫₀¹ SZ(α)³ e(-Nα) dα` is the limit of the real triple sums
  `T3 N M = Σ_{x, y, z ≤ M, x + y + z = N} a(x) a(y) a(z)`, `a(n) = Λ(n) e^{-n/N}`, the identity
  behind (0.4), by `CircleOrth.ternary_orth` and dominated convergence.

Binary Goldbach is OPEN.
-/
import LeanLab.Zinoviev1997.MeanSquare

namespace LeanLab.Zinoviev1997
open Real Finset Filter Topology ArithmeticFunction LeanLab.CircleOrth MeasureTheory

/-- `a(n) = Λ(n) e^{-n/N}`. -/
noncomputable def aZ (N n : ℕ) : ℝ := Λ n * Real.exp (-n / N)

theorem aZ_nonneg (N n : ℕ) : 0 ≤ aZ N n :=
  mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le

theorem summable_aZ {N : ℕ} (hN : 0 < N) : Summable (aZ N) := by
  have hr : (0 : ℝ) < 1 / N := by positivity
  refine Summable.of_nonneg_of_le (aZ_nonneg N) (fun n => ?_)
    (Real.summable_pow_mul_exp_neg_nat_mul 1 hr)
  unfold aZ
  have h1 : Λ n ≤ (n : ℝ) ^ 1 := by
    rw [pow_one]
    exact vonMangoldt_le_log.trans (Real.log_le_self (Nat.cast_nonneg n))
  have h2 : Real.exp (-n / N) = Real.exp (-(1 / N) * n) := by congr 1; ring
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

/-- The series. -/
noncomputable def SZ (N : ℕ) (α : ℝ) : ℂ := ∑' n : ℕ, (aZ N n : ℂ) * ee (n * α)

/-- Its truncations. -/
noncomputable def SM (N M : ℕ) (α : ℝ) : ℂ := ∑ n ∈ range M, (aZ N n : ℂ) * ee (n * α)

theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  have : (2 * (Real.pi : ℂ) * Complex.I * x) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_term (N n : ℕ) (α : ℝ) : ‖(aZ N n : ℂ) * ee (n * α)‖ = aZ N n := by
  rw [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_of_nonneg (aZ_nonneg N n)]

theorem summable_term {N : ℕ} (hN : 0 < N) (α : ℝ) :
    Summable fun n : ℕ => (aZ N n : ℂ) * ee (n * α) :=
  Summable.of_norm (by simp_rw [norm_term]; exact summable_aZ hN)

theorem SM_tendsto {N : ℕ} (hN : 0 < N) (α : ℝ) :
    Tendsto (fun M => SM N M α) atTop (𝓝 (SZ N α)) :=
  (summable_term hN α).hasSum.tendsto_sum_nat

theorem continuous_term (N n : ℕ) : Continuous fun α : ℝ => (aZ N n : ℂ) * ee (n * α) :=
  continuous_const.mul (continuous_ee.comp (continuous_const.mul continuous_id))

theorem continuous_SM (N M : ℕ) : Continuous (SM N M) := by
  unfold SM; exact continuous_finsetSum _ fun n _ => continuous_term N n

theorem continuous_SZ {N : ℕ} (hN : 0 < N) : Continuous (SZ N) :=
  continuous_tsum (fun n => continuous_term N n) (summable_aZ hN)
    (fun n α => (norm_term N n α).le)

theorem norm_SM_le {N : ℕ} (hN : 0 < N) (M : ℕ) (α : ℝ) : ‖SM N M α‖ ≤ ∑' n, aZ N n := by
  unfold SM
  calc ‖∑ n ∈ range M, (aZ N n : ℂ) * ee (n * α)‖ ≤ ∑ n ∈ range M, ‖(aZ N n : ℂ) * ee (n * α)‖ :=
        norm_sum_le _ _
    _ = ∑ n ∈ range M, aZ N n := by simp_rw [norm_term]
    _ ≤ ∑' n, aZ N n := (summable_aZ hN).sum_le_tsum _ (fun n _ => aZ_nonneg N n)

theorem norm_SZ_le {N : ℕ} (hN : 0 < N) (α : ℝ) : ‖SZ N α‖ ≤ ∑' n, aZ N n :=
  le_of_tendsto ((continuous_norm.tendsto _).comp (SM_tendsto hN α))
    (Eventually.of_forall fun M => norm_SM_le hN M α)

/-- The truncation `SM N (M + 1)` is `CircleOrth.S (freqs M) (coef N)`. -/
theorem SM_eq_S (N M : ℕ) (α : ℝ) : SM N (M + 1) α = LeanLab.CircleOrth.S (freqs M) (coef N) α := by
  induction M with
  | zero =>
    simp [SM, LeanLab.CircleOrth.S, freqs, aZ]
  | succ M ih =>
    rw [SM, Finset.sum_range_succ, ← SM, ih]
    unfold LeanLab.CircleOrth.S freqs
    rw [Finset.sum_map, Finset.sum_map, Finset.sum_Icc_succ_top (by omega)]
    congr 1

/-- **(3.17) with Lemma 1.5** for the full series: `∫₀¹ ‖SZ(α)‖² dα ≤ 0.96 N ln N`. -/
theorem SZ_sq_le (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) :
    ∫ α in (0 : ℝ)..1, ‖SZ N α‖ ^ 2 ≤ 0.96 * N * Real.log N := by
  have hN0 : 0 < N := by
    have : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hN
    exact_mod_cast this
  set B := ∑' n, aZ N n
  have lim : Tendsto (fun M => ∫ α in (0 : ℝ)..1, ‖SM N (M + 1) α‖ ^ 2) atTop
      (𝓝 (∫ α in (0 : ℝ)..1, ‖SZ N α‖ ^ 2)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => B ^ 2)
      (Eventually.of_forall fun M => ((continuous_SM N (M + 1)).norm.pow 2).aestronglyMeasurable)
      (Eventually.of_forall fun M => ae_of_all _ fun α _ => ?_) intervalIntegrable_const
      (ae_of_all _ fun α _ => ?_)
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_SM_le hN0 _ α) 2
    · exact (((continuous_norm.tendsto _).comp (SM_tendsto hN0 α)).pow 2).comp
        (tendsto_add_atTop_nat 1)
  refine le_of_tendsto' lim fun M => ?_
  simp_rw [SM_eq_S]
  exact mean_square_le N hN M

/-- The triple sums `T3 N M = Σ_{x, y, z ∈ [1, M], x + y + z = N} a(x) a(y) a(z)`. -/
noncomputable def T3 (N M : ℕ) : ℝ :=
  ∑ x ∈ Icc 1 M, ∑ y ∈ Icc 1 M, ∑ z ∈ Icc 1 M,
    if x + y + z = N then aZ N x * aZ N y * aZ N z else 0

theorem coef_nat (N x : ℕ) : coef N (x : ℤ) = (aZ N x : ℂ) := by
  simp [coef, aZ, Int.toNat_natCast]

/-- The truncated cube integral is the triple sum, by `ternary_orth`. -/
theorem SM_cube (N M : ℕ) :
    ∫ α in (0 : ℝ)..1, SM N (M + 1) α ^ 3 * ee (-((N : ℤ) * α)) = (T3 N M : ℂ) := by
  simp_rw [SM_eq_S]
  rw [ternary_orth]
  unfold T3 freqs
  push_cast
  simp only [Finset.sum_map, Nat.castEmbedding_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  have hiff : ((x : ℤ) + (y : ℤ) + (z : ℤ) = (N : ℤ)) ↔ x + y + z = N := by
    constructor <;> intro h <;> [exact_mod_cast h; exact_mod_cast h]
  by_cases h : x + y + z = N
  · rw [if_pos (hiff.mpr h), if_pos h, coef_nat, coef_nat, coef_nat]; push_cast; ring
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]; simp

/-- **The identity behind (0.4)**: `∫₀¹ SZ³ e(-Nα)` is the limit of the triple sums. -/
theorem SZ_cube_tendsto {N : ℕ} (hN0 : 0 < N) :
    Tendsto (fun M => ((T3 N M : ℝ) : ℂ)) atTop
      (𝓝 (∫ α in (0 : ℝ)..1, SZ N α ^ 3 * ee (-((N : ℤ) * α)))) := by
  set B := ∑' n, aZ N n
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (a := 0) (b := 1) (l := atTop)
    (F := fun M α => SM N (M + 1) α ^ 3 * ee (-((N : ℤ) * α)))
    (f := fun α => SZ N α ^ 3 * ee (-((N : ℤ) * α))) (fun _ => B ^ 3)
    (Eventually.of_forall fun M => (((continuous_SM N (M + 1)).pow 3).mul
      (continuous_ee.comp (continuous_const.mul continuous_id).neg)).aestronglyMeasurable)
    (Eventually.of_forall fun M => ae_of_all _ fun α _ => by
      rw [norm_mul, norm_ee, mul_one, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_SM_le hN0 _ α) 3)
    intervalIntegrable_const
    (ae_of_all _ fun α _ => ((((SM_tendsto hN0 α).pow 3).mul tendsto_const_nhds).comp
      (tendsto_add_atTop_nat 1)))
  simp_rw [SM_cube] at h
  exact h

end LeanLab.Zinoviev1997
