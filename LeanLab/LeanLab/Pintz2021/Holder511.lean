/-
P0054 J. Pintz 2021, Section 5, display (5.11): the minor arc first moment by Hölder.
Unit U-6771, session 20261020T2317Z-cloud53.

* `holder_interval`: Hölder with exponents `4/3` and `4` on `[-1/2, 1/2]` for continuous `f, g ≥ 0`.
* `sum_R2_squares_le`: the first line of (5.11), `∑_{m ≤ N} ‖R₂(2m²)‖ ≤ B^{1/2} V^{3/4} W^{1/4}`.
* `fourth_moment`, `weighted_le_unweighted`: the fourth moment with weights `‖u‖ ≤ 1` is at most
  that of `f` of (5.9), so (5.10) covers the weighted sums that (5.11) needs.
* `minor511_of_lemma1`: (5.11), `≪ X N^{4/5} L^{c+4}`, CONDITIONAL ON Lemma 1 at `P ≥ X^{2/5}`
  and the fourth moment bound.
* `theorem5_of_paperInput`: Theorem 5 CONDITIONAL ON Lemma 1, (5.10) and the major arc output.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-21.
-/
import Mathlib
import LeanLab.Pintz2021.Reduction5

namespace LeanLab.Pintz2021.Holder511

open Real Finset MeasureTheory
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Gallagher LeanLab.Pintz2021.MinorArcs

theorem memLp_of_continuous (f : ℝ → ℝ) (hf : Continuous f) (p : ENNReal) :
    MemLp f p (volume.restrict (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-(1 / 2 : ℝ))) (b := 1 / 2)).exists_bound_of_continuousOn
    hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C
    (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hC x (Set.Ioc_subset_Icc_self hx))

/-- Hölder with exponents `4/3` and `4` on `[-1/2, 1/2]`. -/
theorem holder_interval (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f x * g x ≤
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), f x ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) *
        (∫ x in (-(1 / 2 : ℝ))..(1 / 2), g x ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := by
  have hle : (-(1 / 2 : ℝ)) ≤ 1 / 2 := by norm_num
  rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_of_le hle]
  have hpq : (4 / 3 : ℝ).HolderConjugate 4 := by
    rw [Real.holderConjugate_iff]; constructor <;> norm_num
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    hpq (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (memLp_of_continuous f hf _) (memLp_of_continuous g hg _)
  convert h using 3; norm_num

/-- The minor arc first moment over the squares, the first line of (5.11): with the norm of `S`
at most `B` on `mi`, and `W` bounding the fourth moment of every `∑_{m ≤ N} u(m) e(-2m²β)` with
`‖u(m)‖ ≤ 1`, `∑_{m ≤ N} ‖R₂(2m²)‖ ≤ B^{1/2} (∑ ‖a(n)‖²)^{3/4} W^{1/4}`. -/
theorem sum_R2_squares_le (a : ℕ → ℂ) (K : ℕ) (mi : Set ℝ) (hmi : MeasurableSet mi) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ β ∈ mi, ‖∑ n ∈ range K, a n * e (n * β)‖ ≤ B) (N : ℕ) {W : ℝ}
    (hW : ∀ u : ℕ → ℂ, (∀ m, ‖u m‖ ≤ 1) →
      ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖∑ m ∈ Icc 1 N, u m * e (-((2 * m ^ 2 : ℕ) * β))‖ ^ 4 ≤ W) :
    ∑ m ∈ Icc 1 N, ‖R2 (fun β => ∑ n ∈ range K, a n * e (n * β)) mi (2 * m ^ 2)‖ ≤
      B ^ (1 / 2 : ℝ) * (∑ n ∈ range K, ‖a n‖ ^ 2) ^ (3 / 4 : ℝ) * W ^ (1 / 4 : ℝ) := by
  set S : ℝ → ℂ := fun β => ∑ n ∈ range K, a n * e (n * β) with hS
  have hSc : Continuous S :=
    continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_e_mul _)
  set g : ℝ → ℂ := mi.indicator fun β => S β ^ 2
  have hS2 : IntervalIntegrable (fun β => S β ^ 2) volume (-(1 / 2)) (1 / 2) :=
    (hSc.pow 2).intervalIntegrable _ _
  have hg : IntervalIntegrable g volume (-(1 / 2)) (1 / 2) :=
    ⟨hS2.1.indicator hmi, hS2.2.indicator hmi⟩
  set z : ℕ → ℂ := fun m => R2 S mi (2 * m ^ 2)
  set u : ℕ → ℂ := fun m => (starRingEnd ℂ) (z m) / ((‖z m‖ : ℝ) : ℂ)
  have hu : ∀ m, ‖u m‖ ≤ 1 := by
    intro m
    simp only [u, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_norm]
    by_cases h0 : ‖z m‖ = 0
    · rw [h0]; simp
    · rw [div_self h0]
  have huz : ∀ m, u m * z m = ((‖z m‖ : ℝ) : ℂ) := by
    intro m
    by_cases h0 : z m = 0
    · simp [u, h0]
    · have hn : ((‖z m‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
      simp only [u]
      rw [div_mul_eq_mul_div, mul_comm ((starRingEnd ℂ) (z m)), Complex.mul_conj',
        div_eq_iff hn]
      ring
  set F : ℝ → ℂ := fun β => ∑ m ∈ Icc 1 N, u m * e (-((2 * m ^ 2 : ℕ) * β))
  have hcn : ∀ m : ℕ, Continuous fun β : ℝ => e (-((2 * m ^ 2 : ℕ) * β)) := fun m =>
    (continuous_e_mul (-((2 * m ^ 2 : ℕ) : ℝ))).congr fun β => by rw [neg_mul]
  have hFc : Continuous F := continuous_finsetSum _ fun m _ => continuous_const.mul (hcn m)
  -- the sum as one integral
  have hsum : ∑ m ∈ Icc 1 N, u m * z m = ∫ β in (-(1 / 2 : ℝ))..(1 / 2), g β * F β := by
    have hpt : ∀ β, g β * F β = ∑ m ∈ Icc 1 N, u m * (g β * e (-((2 * m ^ 2 : ℕ) * β))) := by
      intro β; simp only [F, mul_sum]; refine sum_congr rfl fun m _ => by ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum fun m _ =>
      (hg.mul_continuousOn (hcn m).continuousOn).const_mul _]
    refine sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_const_mul]
    rfl
  have hreal : ∑ m ∈ Icc 1 N, ‖z m‖ = (∑ m ∈ Icc 1 N, u m * z m).re := by
    simp_rw [huz]; rw [← Complex.ofReal_sum, Complex.ofReal_re]
  have hle : (-(1 / 2 : ℝ)) ≤ 1 / 2 := by norm_num
  -- pointwise bound
  set f1 : ℝ → ℝ := fun β => ‖S β‖ ^ (3 / 2 : ℝ)
  have hf1c : Continuous f1 := hSc.norm.rpow_const fun _ => Or.inr (by norm_num)
  have hpt : ∀ β, ‖g β * F β‖ ≤ B ^ (1 / 2 : ℝ) * (f1 β * ‖F β‖) := by
    intro β
    rw [norm_mul]
    have hF0 : 0 ≤ ‖F β‖ := norm_nonneg _
    have hgle : ‖g β‖ ≤ B ^ (1 / 2 : ℝ) * f1 β := by
      by_cases hβ : β ∈ mi
      · simp only [g, Set.indicator_of_mem hβ, norm_pow]
        have hS0 : 0 ≤ ‖S β‖ := norm_nonneg _
        have hsplit : ‖S β‖ ^ 2 = ‖S β‖ ^ (1 / 2 : ℝ) * ‖S β‖ ^ (3 / 2 : ℝ) := by
          rw [← rpow_add' hS0 (by norm_num)]; norm_num
        rw [hsplit]
        exact mul_le_mul_of_nonneg_right (rpow_le_rpow hS0 (hB β hβ) (by norm_num))
          (rpow_nonneg hS0 _)
      · simp only [g, Set.indicator_of_notMem hβ, norm_zero]
        exact mul_nonneg (rpow_nonneg hB0 _) (rpow_nonneg (norm_nonneg _) _)
    calc ‖g β‖ * ‖F β‖ ≤ B ^ (1 / 2 : ℝ) * f1 β * ‖F β‖ := mul_le_mul_of_nonneg_right hgle hF0
      _ = _ := by ring
  have hint1 : IntervalIntegrable (fun β => ‖g β * F β‖) volume (-(1 / 2)) (1 / 2) :=
    (hg.mul_continuousOn hFc.continuousOn).norm
  have hint2 : IntervalIntegrable (fun β => B ^ (1 / 2 : ℝ) * (f1 β * ‖F β‖)) volume
      (-(1 / 2)) (1 / 2) :=
    (continuous_const.mul (hf1c.mul hFc.norm)).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on hle hint1 hint2 fun β _ => hpt β
  rw [intervalIntegral.integral_const_mul] at hmono
  -- Hölder
  have hhol := holder_interval f1 (fun β => ‖F β‖) hf1c hFc.norm
    (fun _ => rpow_nonneg (norm_nonneg _) _) (fun _ => norm_nonneg _)
  have hf1p : ∀ β, f1 β ^ (4 / 3 : ℝ) = ‖S β‖ ^ 2 := by
    intro β
    simp only [f1]
    rw [← rpow_mul (norm_nonneg _)]; norm_num
  simp_rw [hf1p] at hhol
  rw [parseval a K] at hhol
  have hF4 : ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖F β‖ ^ (4 : ℝ) ≤ W := by
    have := hW u hu
    simp_rw [show ∀ β, ‖F β‖ ^ (4 : ℝ) = ‖F β‖ ^ (4 : ℕ) from fun β => by
      rw [← rpow_natCast]; norm_num]
    exact this
  have hF40 : 0 ≤ ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖F β‖ ^ (4 : ℝ) :=
    intervalIntegral.integral_nonneg hle fun β _ => rpow_nonneg (norm_nonneg _) _
  have hW14 : (∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖F β‖ ^ (4 : ℝ)) ^ (1 / 4 : ℝ) ≤ W ^ (1 / 4 : ℝ) :=
    rpow_le_rpow hF40 hF4 (by norm_num)
  have hV0 : 0 ≤ (∑ n ∈ range K, ‖a n‖ ^ 2) ^ (3 / 4 : ℝ) :=
    rpow_nonneg (sum_nonneg fun _ _ => sq_nonneg _) _
  have hB12 : 0 ≤ B ^ (1 / 2 : ℝ) := rpow_nonneg hB0 _
  calc ∑ m ∈ Icc 1 N, ‖R2 S mi (2 * m ^ 2)‖ = (∫ β in (-(1 / 2 : ℝ))..(1 / 2), g β * F β).re := by
        rw [← hsum]; exact hreal
    _ ≤ ‖∫ β in (-(1 / 2 : ℝ))..(1 / 2), g β * F β‖ := Complex.re_le_norm _
    _ ≤ ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖g β * F β‖ :=
        intervalIntegral.norm_integral_le_integral_norm hle
    _ ≤ B ^ (1 / 2 : ℝ) * ∫ β in (-(1 / 2 : ℝ))..(1 / 2), f1 β * ‖F β‖ := hmono
    _ ≤ B ^ (1 / 2 : ℝ) * ((∑ n ∈ range K, ‖a n‖ ^ 2) ^ (3 / 4 : ℝ) *
          (∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖F β‖ ^ (4 : ℝ)) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hhol hB12
    _ ≤ B ^ (1 / 2 : ℝ) * ((∑ n ∈ range K, ‖a n‖ ^ 2) ^ (3 / 4 : ℝ) * W ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW14 hV0) hB12
    _ = _ := by ring

/-- `log X ≥ 1` for `X ≥ 4`. -/
theorem one_le_log {X : ℝ} (hX : 4 ≤ X) : 1 ≤ Real.log X := by
  rw [← Real.log_exp 1]
  apply Real.log_le_log (Real.exp_pos 1)
  have := Real.exp_one_lt_d9
  linarith

/-- (5.10) for weights `‖u(m)‖ ≤ 1`, at `X = N²` and level `K₀ N² L^c`: the form in which the
fourth moment enters (5.11). It follows from (5.10) through the count of
`n₁² + n₂² = n₃² + n₄²`, which is not formalized here. -/
def Moment510 (K0 : ℝ) (c N : ℕ) : Prop :=
  ∀ u : ℕ → ℂ, (∀ m, ‖u m‖ ≤ 1) →
    ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖∑ m ∈ Icc 1 N, u m * e (-((2 * m ^ 2 : ℕ) * β))‖ ^ 4 ≤
      K0 * (N : ℝ) ^ 2 * Real.log ((N : ℝ) ^ 2) ^ c

/-- CONDITIONAL ON Lemma 1 at a level `P ≥ X^{2/5}` and on `Moment510`: display (5.11),
`∑_{m ≤ N} ‖R₂(2m²)‖ ≤ K' X N^{4/5} L^{c+4}` with `X = N²`, `L = log X`. -/
theorem minor511_of_lemma1 {A K0 X1 P : ℝ} {c N : ℕ} (hA : 0 ≤ A) (hK0 : 0 ≤ K0) (hN : 2 ≤ N)
    (hP : ((N : ℝ) ^ 2) ^ (2 / 5 : ℝ) ≤ P) (mi : Set ℝ) (hmi : MeasurableSet mi)
    (h1 : Lemma1On A X1 ((N : ℝ) ^ 2) P mi) (hW : Moment510 K0 c N) :
    ∑ m ∈ Icc 1 N, ‖R2 (S X1 ((N : ℝ) ^ 2)) mi (2 * m ^ 2)‖ ≤
      (2 * A) ^ (1 / 2 : ℝ) * 2 ^ (3 / 4 : ℝ) * K0 ^ (1 / 4 : ℝ) *
        (N : ℝ) ^ 2 * (N : ℝ) ^ (4 / 5 : ℝ) * Real.log ((N : ℝ) ^ 2) ^ (c + 4) := by
  set X : ℝ := (N : ℝ) ^ 2 with hXdef
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hX4 : 4 ≤ X := by simp only [X]; nlinarith
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  set L : ℝ := Real.log X
  have hL1 : 1 ≤ L := one_le_log hX4
  have hL0 : 0 ≤ L := by linarith
  -- the sup bound `B = 2 A X^{4/5} L⁴`
  have hP0 : 0 < P := lt_of_lt_of_le (rpow_pos_of_pos hX0 _) hP
  have hXP : X / Real.sqrt P ≤ X ^ (4 / 5 : ℝ) := by
    have hs : X ^ (1 / 5 : ℝ) ≤ Real.sqrt P := by
      rw [Real.le_sqrt (rpow_nonneg hX0.le _) hP0.le, ← rpow_natCast, ← rpow_mul hX0.le]
      norm_num; exact hP
    have hs0 : 0 < X ^ (1 / 5 : ℝ) := rpow_pos_of_pos hX0 _
    calc X / Real.sqrt P ≤ X / X ^ (1 / 5 : ℝ) := div_le_div_of_nonneg_left hX0.le hs0 hs
      _ = X ^ (4 / 5 : ℝ) := by
        rw [div_eq_iff hs0.ne', ← rpow_add hX0]; norm_num
  set B : ℝ := 2 * A * X ^ (4 / 5 : ℝ) * L ^ 4
  have hB0 : 0 ≤ B := by positivity
  have hB : ∀ β ∈ mi, ‖S X1 X β‖ ≤ B := by
    intro β hβ
    refine (h1 β hβ).trans ?_
    simp only [B]
    have : A * (X / Real.sqrt P + X ^ (4 / 5 : ℝ)) ≤ 2 * A * X ^ (4 / 5 : ℝ) := by nlinarith
    exact mul_le_mul_of_nonneg_right this (pow_nonneg hL0 4)
  have hmain := sum_R2_squares_le (aS X1 X) (⌊X⌋₊ + 1) mi hmi hB0 hB N hW
  have hV := sum_aS_sq_le X1 hX1
  have hV0 : 0 ≤ ∑ n ∈ range (⌊X⌋₊ + 1), ‖aS X1 X n‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hV34 : (∑ n ∈ range (⌊X⌋₊ + 1), ‖aS X1 X n‖ ^ 2) ^ (3 / 4 : ℝ) ≤
      (2 * X * L ^ 2) ^ (3 / 4 : ℝ) := rpow_le_rpow hV0 hV (by norm_num)
  -- the three factors
  have e1 : B ^ (1 / 2 : ℝ) = (2 * A) ^ (1 / 2 : ℝ) * X ^ (2 / 5 : ℝ) * L ^ (2 : ℝ) := by
    simp only [B]
    rw [mul_rpow (by positivity) (by positivity), mul_rpow (by positivity) (by positivity),
      ← rpow_mul hX0.le, ← rpow_natCast L 4, ← rpow_mul hL0]
    norm_num
  have e2 : (2 * X * L ^ 2) ^ (3 / 4 : ℝ) = 2 ^ (3 / 4 : ℝ) * X ^ (3 / 4 : ℝ) * L ^ (3 / 2 : ℝ) := by
    rw [mul_rpow (by positivity) (by positivity), mul_rpow (by positivity) (by positivity),
      ← rpow_natCast L 2, ← rpow_mul hL0]
    norm_num
  have e3 : (K0 * (N : ℝ) ^ 2 * L ^ c) ^ (1 / 4 : ℝ) =
      K0 ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) * L ^ ((c : ℝ) / 4) := by
    rw [mul_rpow (by positivity) (by positivity), mul_rpow (by positivity) (by positivity),
      ← rpow_natCast (N : ℝ) 2, ← rpow_mul hN0.le, ← rpow_natCast L c, ← rpow_mul hL0]
    rw [show ((2 : ℕ) : ℝ) * (1 / 4) = 1 / 2 by norm_num, show (c : ℝ) * (1 / 4) = c / 4 by ring]
  have hLexp : L ^ (2 : ℝ) * L ^ (3 / 2 : ℝ) * L ^ ((c : ℝ) / 4) ≤ L ^ (c + 4) := by
    rw [← rpow_add (by linarith), ← rpow_add (by linarith), ← rpow_natCast]
    apply rpow_le_rpow_of_exponent_le hL1
    push_cast
    have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    linarith
  have hXN : X ^ (2 / 5 : ℝ) * X ^ (3 / 4 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) =
      (N : ℝ) ^ 2 * (N : ℝ) ^ (4 / 5 : ℝ) := Applications.holder_511 hN0
  have hc1 : 0 ≤ (2 * A) ^ (1 / 2 : ℝ) := rpow_nonneg (by positivity) _
  have hc2 : 0 ≤ (2 : ℝ) ^ (3 / 4 : ℝ) := rpow_nonneg (by norm_num) _
  have hc3 : 0 ≤ K0 ^ (1 / 4 : ℝ) := rpow_nonneg hK0 _
  have hB12 : 0 ≤ B ^ (1 / 2 : ℝ) := rpow_nonneg hB0 _
  have hW14 : 0 ≤ (K0 * (N : ℝ) ^ 2 * L ^ c) ^ (1 / 4 : ℝ) := rpow_nonneg (by positivity) _
  calc ∑ m ∈ Icc 1 N, ‖R2 (S X1 X) mi (2 * m ^ 2)‖
      ≤ B ^ (1 / 2 : ℝ) * (∑ n ∈ range (⌊X⌋₊ + 1), ‖aS X1 X n‖ ^ 2) ^ (3 / 4 : ℝ) *
          (K0 * (N : ℝ) ^ 2 * L ^ c) ^ (1 / 4 : ℝ) := hmain
    _ ≤ B ^ (1 / 2 : ℝ) * (2 * X * L ^ 2) ^ (3 / 4 : ℝ) *
          (K0 * (N : ℝ) ^ 2 * L ^ c) ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV34 hB12) hW14
    _ = (2 * A) ^ (1 / 2 : ℝ) * 2 ^ (3 / 4 : ℝ) * K0 ^ (1 / 4 : ℝ) *
          (X ^ (2 / 5 : ℝ) * X ^ (3 / 4 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ)) *
          (L ^ (2 : ℝ) * L ^ (3 / 2 : ℝ) * L ^ ((c : ℝ) / 4)) := by
        rw [e1, e2, e3]; ring
    _ ≤ (2 * A) ^ (1 / 2 : ℝ) * 2 ^ (3 / 4 : ℝ) * K0 ^ (1 / 4 : ℝ) *
          ((N : ℝ) ^ 2 * (N : ℝ) ^ (4 / 5 : ℝ)) * L ^ (c + 4) := by
        rw [hXN]
        apply mul_le_mul_of_nonneg_left hLexp
        positivity
    _ = _ := by ring

/-- The inputs of Section 5 with (5.11) replaced by its sources: for `N > N₀`, `X = N²`, some
`X₁`, measurable minor arcs `mi` with Lemma 1 at a level `P ≥ X^{2/5}`, the fourth moment
`Moment510`, and the major arc output (5.16) with Case 1 (5.14). -/
def Section5LemmaInput (ε : ℝ) : Prop :=
  ∃ (A K0 : ℝ) (c C M N0 : ℕ), 0 ≤ A ∧ 0 ≤ K0 ∧ 0 < C ∧ ∀ N : ℕ, N0 < N →
    ∃ (X1 P : ℝ) (mi : Set ℝ) (𝓡 : Finset ℕ), MeasurableSet mi ∧
    ((N : ℝ) ^ 2) ^ (2 / 5 : ℝ) ≤ P ∧ Lemma1On A X1 ((N : ℝ) ^ 2) P mi ∧ Moment510 K0 c N ∧
    (∀ m ∈ Icc 1 N, (Reduction3.R1 (S X1 ((N : ℝ) ^ 2)) mi (2 * m ^ 2)).re ≤
      ((N : ℝ) ^ 2) ^ (1 - ε) → ∃ R0 ∈ 𝓡, R0 ∣ C * m ^ 2) ∧
    (∀ R0 ∈ 𝓡, ((N : ℝ) ^ 2) ^ (7 / 25 : ℝ) ≤ R0) ∧ 𝓡.card ≤ M

theorem section5MajorInput_of_lemma {ε : ℝ} (h : Section5LemmaInput ε) :
    Reduction5.Section5MajorInput ε := by
  obtain ⟨A, K0, c, C, M, N0, hA, hK0, hC, hin⟩ := h
  refine ⟨(2 * A) ^ (1 / 2 : ℝ) * 2 ^ (3 / 4 : ℝ) * K0 ^ (1 / 4 : ℝ), c + 4, C, M, max N0 2, hC,
    fun N hN => ?_⟩
  obtain ⟨X1, P, mi, 𝓡, hmi, hP, hL1, hW, hMa, hPs, hM⟩ :=
    hin N (lt_of_le_of_lt (le_max_left _ _) hN)
  exact ⟨X1, mi, 𝓡, hmi,
    minor511_of_lemma1 hA hK0 (by have := le_max_right N0 2; omega) hP mi hmi hL1 hW,
    hMa, hPs, hM⟩

/-- CONDITIONAL ON Lemma 1, `Moment510` and the major arc output, `Section5LemmaInput ε` for
every `ε > 0`: Theorem 5, `E₂(N) ≪_ε N^{4/5+ε}`. -/
theorem theorem5_of_lemma (h : ∀ ε : ℝ, 0 < ε → Section5LemmaInput ε) :
    LeanLab.ExceptionalSet.Pintz2021.Theorem5 :=
  Reduction5.theorem5_of_major fun ε hε => section5MajorInput_of_lemma (h ε hε)

/-! ### (5.10) for unimodular weights from (5.10) itself -/

/-- The fourth moment of a trigonometric polynomial: `∫ ‖∑_{m ∈ s} v(m) e(k(m)β)‖⁴` is
`∑_j ‖∑_{k(m₁)+k(m₂)=j} v(m₁) v(m₂)‖²`. -/
theorem fourth_moment (s : Finset ℕ) (k : ℕ → ℕ) (D : ℕ) (hD : ∀ m ∈ s, 2 * k m < D)
    (v : ℕ → ℂ) :
    ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖∑ m ∈ s, v m * e (k m * β)‖ ^ 4 =
      ∑ j ∈ range D, ‖∑ p ∈ (s ×ˢ s).filter (fun p => k p.1 + k p.2 = j), v p.1 * v p.2‖ ^ 2 := by
  set c : ℕ → ℂ := fun j => ∑ p ∈ (s ×ˢ s).filter (fun p => k p.1 + k p.2 = j), v p.1 * v p.2
  have hsq : ∀ β : ℝ, (∑ m ∈ s, v m * e (k m * β)) ^ 2 = ∑ j ∈ range D, c j * e (j * β) := by
    intro β
    rw [sq, sum_mul_sum, ← sum_product']
    have hmaps : ∀ p ∈ s ×ˢ s, k p.1 + k p.2 ∈ range D := by
      intro p hp
      obtain ⟨h1, h2⟩ := mem_product.mp hp
      have := hD _ h1; have := hD _ h2
      rw [mem_range]; omega
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine sum_congr rfl fun j _ => ?_
    simp only [c, sum_mul]
    refine sum_congr rfl fun p hp => ?_
    have hj := (mem_filter.mp hp).2
    have : e (k p.1 * β) * e (k p.2 * β) = e (j * β) := by
      rw [← e_add, ← hj]; congr 1; push_cast; ring
    calc v p.1 * e (k p.1 * β) * (v p.2 * e (k p.2 * β))
        = v p.1 * v p.2 * (e (k p.1 * β) * e (k p.2 * β)) := by ring
      _ = _ := by rw [this]
  have hpt : ∀ β : ℝ, ‖∑ m ∈ s, v m * e (k m * β)‖ ^ 4 = ‖∑ j ∈ range D, c j * e (j * β)‖ ^ 2 := by
    intro β; rw [← hsq, norm_pow]; ring
  simp_rw [hpt]
  exact parseval c D

/-- `Moment510` follows from (5.10) for `f(α) = ∑_{n ≤ N} e(2αn²)`, display (5.9). -/
theorem weighted_le_unweighted (N : ℕ) (u : ℕ → ℂ) (hu : ∀ m, ‖u m‖ ≤ 1) :
    ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖∑ m ∈ Icc 1 N, u m * e (-((2 * m ^ 2 : ℕ) * β))‖ ^ 4 ≤
      ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖∑ m ∈ Icc 1 N, e ((2 * m ^ 2 : ℕ) * β)‖ ^ 4 := by
  set k : ℕ → ℕ := fun m => 2 * m ^ 2
  set D : ℕ := 4 * N ^ 2 + 1
  have hD : ∀ m ∈ Icc 1 N, 2 * k m < D := by
    intro m hm
    have := (mem_Icc.mp hm).2
    have : m ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left this 2
    simp only [k, D]; omega
  have hconj : ∀ β : ℝ, ‖∑ m ∈ Icc 1 N, u m * e (-((2 * m ^ 2 : ℕ) * β))‖ =
      ‖∑ m ∈ Icc 1 N, (starRingEnd ℂ) (u m) * e (k m * β)‖ := by
    intro β
    rw [← Complex.norm_conj, map_sum]
    congr 1; refine sum_congr rfl fun m _ => ?_
    rw [map_mul, e_neg, Complex.conj_conj]
  have hone : ∀ β : ℝ, ∑ m ∈ Icc 1 N, e ((2 * m ^ 2 : ℕ) * β) =
      ∑ m ∈ Icc 1 N, (fun _ => (1 : ℂ)) m * e (k m * β) := by
    intro β; refine sum_congr rfl fun m _ => by simp [k]
  simp_rw [hconj, hone]
  rw [fourth_moment _ k D hD, fourth_moment _ k D hD]
  apply sum_le_sum
  intro j _
  apply pow_le_pow_left₀ (norm_nonneg _)
  calc ‖∑ p ∈ (Icc 1 N ×ˢ Icc 1 N).filter (fun p => k p.1 + k p.2 = j),
        (starRingEnd ℂ) (u p.1) * (starRingEnd ℂ) (u p.2)‖
      ≤ ∑ p ∈ (Icc 1 N ×ˢ Icc 1 N).filter (fun p => k p.1 + k p.2 = j),
        ‖(starRingEnd ℂ) (u p.1) * (starRingEnd ℂ) (u p.2)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ (Icc 1 N ×ˢ Icc 1 N).filter (fun p => k p.1 + k p.2 = j), (1 : ℝ) := by
        apply sum_le_sum; intro p _
        rw [norm_mul, Complex.norm_conj, Complex.norm_conj]
        have h1 := hu p.1; have h2 := hu p.2
        nlinarith [norm_nonneg (u p.1), norm_nonneg (u p.2)]
    _ = ‖∑ p ∈ (Icc 1 N ×ˢ Icc 1 N).filter (fun p => k p.1 + k p.2 = j),
        (fun _ => (1 : ℂ)) p.1 * (fun _ => (1 : ℂ)) p.2‖ := by
        simp only [mul_one, sum_const, nsmul_eq_mul, Complex.norm_natCast]

/-- Display (5.10), `∫₀¹ |f(α)|⁴ dα ≤ K₀ N² L^c` with `f(α) = ∑_{n ≤ N} e(2αn²)`, `L = log N²`. -/
def Display510 (K0 : ℝ) (c N : ℕ) : Prop :=
  ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖∑ m ∈ Icc 1 N, e ((2 * m ^ 2 : ℕ) * β)‖ ^ 4 ≤
    K0 * (N : ℝ) ^ 2 * Real.log ((N : ℝ) ^ 2) ^ c

theorem moment510_of_display510 {K0 : ℝ} {c N : ℕ} (h : Display510 K0 c N) :
    Moment510 K0 c N := fun u hu => (weighted_le_unweighted N u hu).trans h

/-- The Section 5 inputs as the paper names them: Lemma 1 (1.10) on the minor arcs at a level
`P ≥ X^{2/5}`, display (5.10), and the major arc output (5.16) with Case 1 (5.14). -/
def Section5PaperInput (ε : ℝ) : Prop :=
  ∃ (A K0 : ℝ) (c C M N0 : ℕ), 0 ≤ A ∧ 0 ≤ K0 ∧ 0 < C ∧ ∀ N : ℕ, N0 < N →
    ∃ (X1 P : ℝ) (mi : Set ℝ) (𝓡 : Finset ℕ), MeasurableSet mi ∧
    ((N : ℝ) ^ 2) ^ (2 / 5 : ℝ) ≤ P ∧ Lemma1On A X1 ((N : ℝ) ^ 2) P mi ∧ Display510 K0 c N ∧
    (∀ m ∈ Icc 1 N, (Reduction3.R1 (S X1 ((N : ℝ) ^ 2)) mi (2 * m ^ 2)).re ≤
      ((N : ℝ) ^ 2) ^ (1 - ε) → ∃ R0 ∈ 𝓡, R0 ∣ C * m ^ 2) ∧
    (∀ R0 ∈ 𝓡, ((N : ℝ) ^ 2) ^ (7 / 25 : ℝ) ≤ R0) ∧ 𝓡.card ≤ M

/-- CONDITIONAL ON Lemma 1, (5.10) and the major arc output for every `ε > 0`: Theorem 5. -/
theorem theorem5_of_paperInput (h : ∀ ε : ℝ, 0 < ε → Section5PaperInput ε) :
    LeanLab.ExceptionalSet.Pintz2021.Theorem5 := by
  apply theorem5_of_lemma
  intro ε hε
  obtain ⟨A, K0, c, C, M, N0, hA, hK0, hC, hin⟩ := h ε hε
  refine ⟨A, K0, c, C, M, N0, hA, hK0, hC, fun N hN => ?_⟩
  obtain ⟨X1, P, mi, 𝓡, hmi, hP, hL1, hW, hMa, hPs, hM⟩ := hin N hN
  exact ⟨X1, P, mi, 𝓡, hmi, hP, hL1, moment510_of_display510 hW, hMa, hPs, hM⟩

end LeanLab.Pintz2021.Holder511

#print axioms LeanLab.Pintz2021.Holder511.holder_interval
#print axioms LeanLab.Pintz2021.Holder511.sum_R2_squares_le
#print axioms LeanLab.Pintz2021.Holder511.minor511_of_lemma1
#print axioms LeanLab.Pintz2021.Holder511.section5MajorInput_of_lemma
#print axioms LeanLab.Pintz2021.Holder511.theorem5_of_lemma
#print axioms LeanLab.Pintz2021.Holder511.fourth_moment
#print axioms LeanLab.Pintz2021.Holder511.weighted_le_unweighted
#print axioms LeanLab.Pintz2021.Holder511.moment510_of_display510
#print axioms LeanLab.Pintz2021.Holder511.theorem5_of_paperInput

