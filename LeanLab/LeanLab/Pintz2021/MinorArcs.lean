/-
P0054 J. Pintz 2021, Section 3, display (3.1): the minor arc mean square from Lemma 1 and
Parseval. Unit U-6771, session 20261020T2317Z-cloud53.

* `bessel`: Bessel's inequality on `[-1/2, 1/2]` for any `g` with `g` and `‖g‖²` integrable,
  against the frequencies `0, …, M-1`; built on the lab's `PNTPort.Gallagher.parseval`.
* `sum_R2_sq_le`: for `S(β) = ∑ a(n) e(nβ)` and any measurable set `mi` on which `‖S‖ ≤ B`,
  the minor arc parts `R₂(m) = ∫_{mi} S(β)² e(-mβ) dβ` satisfy
  `∑_{m < M} ‖R₂(m)‖² ≤ B² ∑ ‖a(n)‖²`, the first two steps of (3.1).
* `minor31_of_lemma1`: with `a(n) = log n` on the primes of `(X₁, X]` as in (1.1) and Lemma 1,
  `‖S‖ ≤ A (X/√P + X^{4/5}) L⁴` on `mi`, at `P = X^{7/25}`:
  `∑_{m < M} ‖R₂(m)‖² ≤ 8 A² X³ L^{10} / P`, the input (3.1) of `Section3Input` with `k = 10`.
  The paper prints `X³ L⁵ / P`; squaring the `L⁴` of (1.10) gives `L⁸`, Q-6771d.
Lemma 1, Vinogradov's minor arc bound, is a hypothesis, CONDITIONAL. The paper's `𝔪` of (1.3)
lives on `[1/Q, 1 + 1/Q]`; here any measurable `mi` in `[-1/2, 1/2]`, the same by periodicity.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-21.
-/
import Mathlib
import LeanLab.PNTPort.Gallagher.Basic

namespace LeanLab.Pintz2021.MinorArcs

open Complex Finset MeasureTheory Real
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Gallagher

/-- The `n`-th Fourier coefficient on `[-1/2, 1/2]`. -/
noncomputable def coef (g : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ β in (-(1 / 2 : ℝ))..(1 / 2), g β * e (-(n * β))

/-- **Bessel's inequality** on `[-1/2, 1/2]` for the frequencies `0, …, M-1`. -/
theorem bessel (g : ℝ → ℂ) (hg : IntervalIntegrable g volume (-(1 / 2)) (1 / 2))
    (hg2 : IntervalIntegrable (fun β => ‖g β‖ ^ 2) volume (-(1 / 2)) (1 / 2)) (M : ℕ) :
    ∑ n ∈ range M, ‖coef g n‖ ^ 2 ≤ ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖g β‖ ^ 2 := by
  set c := coef g
  set h : ℝ → ℂ := fun β => ∑ n ∈ range M, c n * e (n * β) with hh
  have hhc : Continuous h := continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_e_mul _)
  -- the cross term
  have hcross_int : IntervalIntegrable (fun β => g β * (starRingEnd ℂ) (h β)) volume
      (-(1 / 2)) (1 / 2) :=
    hg.mul_continuousOn ((Complex.continuous_conj.comp hhc).continuousOn)
  have hcross : ∫ β in (-(1 / 2 : ℝ))..(1 / 2), g β * (starRingEnd ℂ) (h β) =
      ∑ n ∈ range M, ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
    have hpt : ∀ β, g β * (starRingEnd ℂ) (h β) =
        ∑ n ∈ range M, (starRingEnd ℂ) (c n) * (g β * e (-(n * β))) := by
      intro β
      simp only [hh, map_sum, map_mul, ← e_neg, mul_sum]
      refine sum_congr rfl fun n _ => by ring
    simp_rw [hpt]
    have hcn : ∀ n : ℕ, Continuous fun β : ℝ => e (-(n * β)) := fun n => by
      simpa [neg_mul] using continuous_e_mul (-(n : ℝ))
    rw [intervalIntegral.integral_finsetSum fun n _ =>
      (hg.mul_continuousOn (hcn n).continuousOn).const_mul _]
    refine sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul]
    show (starRingEnd ℂ) (c n) * c n = _
    rw [mul_comm, Complex.mul_conj', Complex.ofReal_pow]
  have hcross_re : ∫ β in (-(1 / 2 : ℝ))..(1 / 2), (g β * (starRingEnd ℂ) (h β)).re =
      ∑ n ∈ range M, ‖c n‖ ^ 2 := by
    have := (Complex.reCLM.intervalIntegral_comp_comm hcross_int)
    simp only [Complex.reCLM_apply] at this
    rw [this, hcross, ← Complex.ofReal_sum, Complex.ofReal_re]
  have hpars : ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖h β‖ ^ 2 = ∑ n ∈ range M, ‖c n‖ ^ 2 :=
    parseval c M
  -- pointwise expansion of `‖g - h‖²`
  have hexp : ∀ β, ‖g β - h β‖ ^ 2 =
      ‖g β‖ ^ 2 - 2 * (g β * (starRingEnd ℂ) (h β)).re + ‖h β‖ ^ 2 := by
    intro β
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]; ring
  have hre_int : IntervalIntegrable (fun β => (g β * (starRingEnd ℂ) (h β)).re) volume
      (-(1 / 2)) (1 / 2) := by
    exact ⟨hcross_int.1.re, hcross_int.2.re⟩
  have hh2 : IntervalIntegrable (fun β => ‖h β‖ ^ 2) volume (-(1 / 2)) (1 / 2) :=
    ((hhc.norm).pow 2).intervalIntegrable _ _
  have hnonneg : 0 ≤ ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖g β - h β‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun β _ => sq_nonneg _
  simp_rw [hexp] at hnonneg
  rw [intervalIntegral.integral_add (hg2.sub (hre_int.const_mul 2)) hh2,
    intervalIntegral.integral_sub hg2 (hre_int.const_mul 2), intervalIntegral.integral_const_mul,
    hcross_re, hpars] at hnonneg
  linarith

/-- The minor arc part, (1.8): `R₂(m) = ∫_{mi} S(β)² e(-mβ) dβ` on `[-1/2, 1/2]`. -/
noncomputable def R2 (S : ℝ → ℂ) (mi : Set ℝ) (m : ℕ) : ℂ :=
  coef (mi.indicator fun β => S β ^ 2) m

/-- The first two steps of (3.1): `∑_m ‖R₂(m)‖² ≤ ∫_{mi} ‖S‖⁴ ≤ B² ∫ ‖S‖² = B² ∑ ‖a(n)‖²`. -/
theorem sum_R2_sq_le (a : ℕ → ℂ) (K : ℕ) (mi : Set ℝ) (hmi : MeasurableSet mi) {B : ℝ}
    (hB : ∀ β ∈ mi, ‖∑ n ∈ range K, a n * e (n * β)‖ ≤ B) (M : ℕ) :
    ∑ m ∈ range M, ‖R2 (fun β => ∑ n ∈ range K, a n * e (n * β)) mi m‖ ^ 2 ≤
      B ^ 2 * ∑ n ∈ range K, ‖a n‖ ^ 2 := by
  set S : ℝ → ℂ := fun β => ∑ n ∈ range K, a n * e (n * β) with hS
  have hSc : Continuous S := continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_e_mul _)
  set g : ℝ → ℂ := mi.indicator fun β => S β ^ 2
  have hS2 : IntervalIntegrable (fun β => S β ^ 2) volume (-(1 / 2)) (1 / 2) :=
    (hSc.pow 2).intervalIntegrable _ _
  have hg : IntervalIntegrable g volume (-(1 / 2)) (1 / 2) :=
    ⟨hS2.1.indicator hmi, hS2.2.indicator hmi⟩
  have hgpt : ∀ β, ‖g β‖ ^ 2 = mi.indicator (fun β => ‖S β‖ ^ 4) β := by
    intro β
    by_cases hβ : β ∈ mi
    · simp only [g, Set.indicator_of_mem hβ, norm_pow]; ring
    · simp [g, Set.indicator_of_notMem hβ]
  have hS4 : IntervalIntegrable (fun β => ‖S β‖ ^ 4) volume (-(1 / 2)) (1 / 2) :=
    ((hSc.norm).pow 4).intervalIntegrable _ _
  have hg2 : IntervalIntegrable (fun β => ‖g β‖ ^ 2) volume (-(1 / 2)) (1 / 2) := by
    simp_rw [hgpt]; exact ⟨hS4.1.indicator hmi, hS4.2.indicator hmi⟩
  have hbes := bessel g hg hg2 M
  have hpt : ∀ β, ‖g β‖ ^ 2 ≤ B ^ 2 * ‖S β‖ ^ 2 := by
    intro β
    rw [hgpt]
    by_cases hβ : β ∈ mi
    · rw [Set.indicator_of_mem hβ]
      have h1 := hB β hβ
      have h0 : 0 ≤ ‖S β‖ := norm_nonneg _
      have : ‖S β‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ h0 h1 2
      nlinarith [sq_nonneg (‖S β‖)]
    · rw [Set.indicator_of_notMem hβ]; positivity
  have hmono : ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖g β‖ ^ 2 ≤
      ∫ β in (-(1 / 2 : ℝ))..(1 / 2), B ^ 2 * ‖S β‖ ^ 2 :=
    intervalIntegral.integral_mono_on (by norm_num) hg2
      ((((hSc.norm).pow 2).intervalIntegrable _ _).const_mul _) fun β _ => hpt β
  rw [intervalIntegral.integral_const_mul, parseval a K] at hmono
  exact hbes.trans hmono

/-- The coefficients of (1.1): `a(n) = log n` for primes `n ∈ (X₁, X]`, else `0`. -/
noncomputable def aS (X1 X : ℝ) (n : ℕ) : ℂ :=
  if n.Prime ∧ X1 < n ∧ (n : ℝ) ≤ X then (Real.log n : ℂ) else 0

/-- `S(α)` of (1.1), with the frequencies `n ≤ X`. -/
noncomputable def S (X1 X : ℝ) (β : ℝ) : ℂ :=
  ∑ n ∈ range (⌊X⌋₊ + 1), aS X1 X n * e (n * β)

/-- `∑ ‖a(n)‖² ≤ 2 X (log X)²` for `X ≥ 1`: at most `X + 1 ≤ 2X` terms, each at most `log² X`. -/
theorem sum_aS_sq_le (X1 : ℝ) {X : ℝ} (hX : 1 ≤ X) :
    ∑ n ∈ range (⌊X⌋₊ + 1), ‖aS X1 X n‖ ^ 2 ≤ 2 * X * Real.log X ^ 2 := by
  have hterm : ∀ n ∈ range (⌊X⌋₊ + 1), ‖aS X1 X n‖ ^ 2 ≤ Real.log X ^ 2 := by
    intro n _
    unfold aS
    split_ifs with h
    · obtain ⟨hp, _, hnX⟩ := h
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hp.one_lt.le
      have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
      exact pow_le_pow_left₀ hlog0 (Real.log_le_log (by linarith) hnX) 2
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
  calc ∑ n ∈ range (⌊X⌋₊ + 1), ‖aS X1 X n‖ ^ 2
      ≤ ∑ _n ∈ range (⌊X⌋₊ + 1), Real.log X ^ 2 := sum_le_sum hterm
    _ = (⌊X⌋₊ + 1 : ℕ) * Real.log X ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ 2 * X * Real.log X ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have := Nat.floor_le (by linarith : (0 : ℝ) ≤ X)
        push_cast; linarith

/-- Lemma 1, (1.10), at the level `P`, as a hypothesis on the set `mi`:
`‖S(α)‖ ≤ A (X/√P + X^{4/5}) L⁴` for `α ∈ mi`, `L = log X`. -/
def Lemma1On (A X1 X P : ℝ) (mi : Set ℝ) : Prop :=
  ∀ β ∈ mi, ‖S X1 X β‖ ≤ A * (X / Real.sqrt P + X ^ (4 / 5 : ℝ)) * Real.log X ^ 4

/-- CONDITIONAL ON Lemma 1 on `mi`: (3.1) at `P = X^{7/25}`,
`∑_{m < M} ‖R₂(m)‖² ≤ 8 A² X³ L^{10} / P`. -/
theorem minor31_of_lemma1 {A X1 X : ℝ} (hA : 0 ≤ A) (hX : 1 ≤ X) (mi : Set ℝ)
    (hmi : MeasurableSet mi) (h1 : Lemma1On A X1 X (X ^ (7 / 25 : ℝ)) mi) (M : ℕ) :
    ∑ m ∈ range M, ‖R2 (S X1 X) mi m‖ ^ 2 ≤
      8 * A ^ 2 * X ^ 3 * Real.log X ^ 10 / X ^ (7 / 25 : ℝ) := by
  have hX0 : 0 < X := by linarith
  have hL0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have hP : 0 < X ^ (7 / 25 : ℝ) := rpow_pos_of_pos hX0 _
  -- `X/√P = X^{43/50}` and `X^{4/5} ≤ X^{43/50}`
  have hsqrt : X / Real.sqrt (X ^ (7 / 25 : ℝ)) = X ^ (43 / 50 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← rpow_mul hX0.le, div_eq_iff (rpow_pos_of_pos hX0 _).ne',
      ← rpow_add hX0]
    norm_num
  have h45 : X ^ (4 / 5 : ℝ) ≤ X ^ (43 / 50 : ℝ) := rpow_le_rpow_of_exponent_le hX (by norm_num)
  set B : ℝ := A * (2 * X ^ (43 / 50 : ℝ)) * Real.log X ^ 4
  have hB : ∀ β ∈ mi, ‖S X1 X β‖ ≤ B := by
    intro β hβ
    have := h1 β hβ
    rw [hsqrt] at this
    refine this.trans ?_
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hL0 4)
    exact mul_le_mul_of_nonneg_left (by linarith) hA
  have hmain := sum_R2_sq_le (aS X1 X) (⌊X⌋₊ + 1) mi hmi hB M
  have hsum := sum_aS_sq_le X1 hX
  have hB0 : 0 ≤ B ^ 2 := sq_nonneg _
  have hfin : B ^ 2 * (2 * X * Real.log X ^ 2) =
      8 * A ^ 2 * X ^ 3 * Real.log X ^ 10 / X ^ (7 / 25 : ℝ) := by
    have hpow : (X ^ (43 / 50 : ℝ)) ^ 2 * X = X ^ 3 / X ^ (7 / 25 : ℝ) := by
      rw [eq_div_iff hP.ne', ← rpow_natCast, ← rpow_natCast, ← rpow_mul hX0.le]
      rw [show X ^ (((43 / 50 : ℝ)) * ((2 : ℕ) : ℝ)) * X * X ^ (7 / 25 : ℝ) =
          X ^ (((43 / 50 : ℝ)) * ((2 : ℕ) : ℝ)) * X ^ (1 : ℝ) * X ^ (7 / 25 : ℝ) by
            rw [rpow_one]]
      rw [← rpow_add hX0, ← rpow_add hX0]; norm_num
    simp only [B]
    rw [show 8 * A ^ 2 * X ^ 3 * Real.log X ^ 10 / X ^ (7 / 25 : ℝ) =
      8 * A ^ 2 * Real.log X ^ 10 * (X ^ 3 / X ^ (7 / 25 : ℝ)) by ring, ← hpow]
    ring
  calc ∑ m ∈ range M, ‖R2 (S X1 X) mi m‖ ^ 2 ≤ B ^ 2 * ∑ n ∈ range (⌊X⌋₊ + 1), ‖aS X1 X n‖ ^ 2 :=
        hmain
    _ ≤ B ^ 2 * (2 * X * Real.log X ^ 2) := mul_le_mul_of_nonneg_left hsum hB0
    _ = _ := hfin

end LeanLab.Pintz2021.MinorArcs

#print axioms LeanLab.Pintz2021.MinorArcs.bessel
#print axioms LeanLab.Pintz2021.MinorArcs.sum_R2_sq_le
#print axioms LeanLab.Pintz2021.MinorArcs.sum_aS_sq_le
#print axioms LeanLab.Pintz2021.MinorArcs.minor31_of_lemma1

