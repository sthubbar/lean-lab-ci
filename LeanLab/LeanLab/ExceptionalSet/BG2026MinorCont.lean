/-
The CONTINUOUS minor arc mean square of P0029 Bhowmik, Grimmelt, The exceptional set of the Goldbach
problem, arXiv 2607.27282v2, eq 4.4 page 14 and Lemma 4.2 page 16, and Theorem 8.2 at `X^{7/12}`
resting on the printed CONTINUOUS major arc formula, unit U-1343, track T1. New module;
BG2026Prop81Chain.lean (U-1335) is imported and not changed.

Setting, as in U-1335: `L = ⌊X⌋ + 1`, `S(α) = Σ_{n<L} Λ(n) e(nα)`, `R = X^ϑ`, `𝔪 = minorSet ϑ X` the
set of `α` with `|α - a/q| > R/(qL)` for all `q ≤ R`, all `a`. Then, eq 4.4,
`r_𝔪(N) = ∫_0^1 1_𝔪(α) S(α)² e(-Nα) dα`, `r_𝔐(N) = ∫_0^1 1_{𝔪ᶜ}(α) S(α)² e(-Nα) dα`, and
`r_𝔐(N) + r_𝔪(N) = r₂(N)` for `N < L`, `r2_eq_integral`, `rMajI_add_rMinI`.

Lemma 4.2 proof, continuous form: `r_𝔪(N)` is the `N`-th Fourier coefficient of `g = 1_𝔪 S²` on
`[0, 1]`, so Mathlib's Parseval `hasSum_sq_fourierCoeffOn` gives Bessel
`Σ_{N ∈ F} |r_𝔪(N)|² ≤ ∫_0^1 |g|² = ∫_𝔪 |S|⁴ ≤ sup_𝔪 |S|² ∫_0^1 |S|² = sup_𝔪 |S|² Σ_{n<L} Λ(n)²`,
`bessel_minor`, `integral_norm_sq_S`, `minorL2_cont_of_sup`.

Remaining inputs of `theorem82σ_seven_twelfths_cont`: `MajorFormula81C GS (5/12) (rMajI (5/12))`, the
printed major arc formula for the complex continuous integral over `𝔐`, `Display81Mult GS` and
`MPRTheorem11`. The discrete caveat of U-1335 is removed. Convention kept from U-1335: the arcs have
width `R/(qL)` with `L = ⌊X⌋ + 1`, and `S` has length `L` for every `N ≤ X`; the print writes `R/(qN)`
with `N` the length of `S`.

AI wrote this Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.BG2026Prop81Chain

namespace LeanLab.ExceptionalSet.BG2026
open Real Finset ArithmeticFunction MeasureTheory
open ComplexConjugate

noncomputable section

/-! ### `e(x)` and orthogonality on `[0, 1]` -/

/-- `e(x) = exp(2πix)`. -/
def eC (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

theorem eC_continuous : Continuous eC := by unfold eC; fun_prop

theorem norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  rw [show 2 * (π : ℂ) * Complex.I * x = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem conj_eC (x : ℝ) : conj (eC x) = eC (-x) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]

/-- `∫_0^1 e(kx) dx = [k = 0]` for integers `k`. PROVED. -/
theorem integral_eC_int (k : ℤ) :
    ∫ x in (0 : ℝ)..1, eC (k * x) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [eC]
  · have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hc : (2 * π * Complex.I * k : ℂ) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [this, Complex.I_ne_zero, hk']
    have e : ∀ x : ℝ, eC (k * x) = Complex.exp ((2 * π * Complex.I * k) * x) := by
      intro x; unfold eC; push_cast; ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * π * Complex.I * k) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * π * Complex.I * k) * ((1 : ℝ) : ℂ) = k * (2 * π * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [h1]; simp

theorem intervalIntegrable_term (c : ℂ) (k : ℤ) :
    IntervalIntegrable (fun x : ℝ => c * eC (k * x)) volume 0 1 :=
  (continuous_const.mul (eC_continuous.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _

/-- Integration of a double exponential sum with integer frequencies. PROVED. -/
theorem integral_double_sum (A B : Finset ℕ) (c : ℕ → ℕ → ℂ) (f : ℕ → ℕ → ℤ) :
    ∫ x in (0 : ℝ)..1, ∑ n ∈ A, ∑ m ∈ B, c n m * eC (f n m * x) =
      ∑ n ∈ A, ∑ m ∈ B, c n m * (if f n m = 0 then 1 else 0) := by
  have hi : ∀ n, IntervalIntegrable (fun x : ℝ => ∑ m ∈ B, c n m * eC (f n m * x)) volume 0 1 := by
    intro n
    exact (continuous_finset_sum _ fun m _ =>
      continuous_const.mul (eC_continuous.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (fun n _ => hi n)]
  refine sum_congr rfl (fun n _ => ?_)
  rw [intervalIntegral.integral_finsetSum (fun m _ => intervalIntegrable_term _ _)]
  refine sum_congr rfl (fun m _ => ?_)
  rw [intervalIntegral.integral_const_mul, integral_eC_int]

/-! ### `S` and the exact identity of eq 4.4 -/

theorem SΛ_eq_eC (L : ℕ) (α : ℝ) : SΛ L α = ∑ n ∈ range L, (Λ n : ℂ) * eC (n * α) := by
  unfold SΛ eC
  refine sum_congr rfl (fun n _ => ?_)
  push_cast; ring_nf

theorem SΛ_continuous (L : ℕ) : Continuous (SΛ L) := by
  have : SΛ L = fun α => ∑ n ∈ range L, (Λ n : ℂ) * eC (n * α) := funext (SΛ_eq_eC L)
  rw [this]
  exact continuous_finset_sum _ fun n _ =>
    continuous_const.mul (eC_continuous.comp (continuous_const.mul continuous_id))

theorem norm_SΛ_le (L : ℕ) (α : ℝ) : ‖SΛ L α‖ ≤ ∑ n ∈ range L, Λ n := by
  rw [SΛ_eq_eC]
  refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl (fun n _ => ?_)))
  rw [norm_mul, norm_eC, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]

/-- Eq 4.4, page 14, exact: `∫_0^1 S(α)² e(-Nα) dα = r₂(N)` for `N < L`. PROVED. -/
theorem r2_eq_integral {L N : ℕ} (hN : N < L) :
    ∫ α in (0 : ℝ)..1, SΛ L α ^ 2 * eC (-(N * α)) = (r2 N : ℂ) := by
  have e1 : ∀ α : ℝ, SΛ L α ^ 2 * eC (-(N * α)) = ∑ n ∈ range L, ∑ m ∈ range L,
      ((Λ n : ℂ) * Λ m) * eC (((n + m - N : ℤ) : ℝ) * α) := by
    intro α
    rw [SΛ_eq_eC, sq, sum_mul_sum, sum_mul]
    refine sum_congr rfl (fun n _ => ?_)
    rw [sum_mul]
    refine sum_congr rfl (fun m _ => ?_)
    have : eC (n * α) * eC (m * α) * eC (-(N * α)) = eC (((n + m - N : ℤ) : ℝ) * α) := by
      unfold eC
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [← this]; ring
  simp_rw [e1]
  rw [integral_double_sum]
  have e2 : ∀ n ∈ range L, ∑ m ∈ range L, ((Λ n : ℂ) * Λ m) *
      (if ((n : ℤ) + m - N) = 0 then 1 else 0) = if n ≤ N then (Λ n : ℂ) * Λ (N - n) else 0 := by
    intro n hn
    rw [mem_range] at hn
    split_ifs with hnN
    · rw [sum_eq_single (N - n)]
      · rw [if_pos (by omega)]; ring
      · intro b _ hb; rw [if_neg (by omega)]; simp
      · intro h; exfalso; rw [mem_range] at h; omega
    · apply sum_eq_zero; intro m _; rw [if_neg (by omega)]; simp
  rw [sum_congr rfl e2, ← sum_filter]
  have hf : (range L).filter (fun n => n ≤ N) = range (N + 1) := by
    ext n; simp only [mem_filter, mem_range]; omega
  rw [hf]
  unfold r2
  push_cast
  rfl

/-- `∫_0^1 |S(α)|² dα = Σ_{n<L} Λ(n)²`. PROVED. -/
theorem integral_norm_sq_S (L : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖SΛ L α‖ ^ 2 = ∑ n ∈ range L, (Λ n) ^ 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have e1 : ∀ α : ℝ, ((‖SΛ L α‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ range L, ∑ m ∈ range L,
      ((Λ n : ℂ) * Λ m) * eC (((n - m : ℤ) : ℝ) * α) := by
    intro α
    rw [Complex.ofReal_pow, ← Complex.mul_conj', SΛ_eq_eC, map_sum, sum_mul_sum]
    refine sum_congr rfl (fun n _ => sum_congr rfl (fun m _ => ?_))
    rw [map_mul, Complex.conj_ofReal, conj_eC]
    have : eC (n * α) * eC (-(m * α)) = eC (((n - m : ℤ) : ℝ) * α) := by
      unfold eC
      rw [← Complex.exp_add]
      congr 1; push_cast; ring
    rw [← this]; ring
  simp_rw [e1]
  rw [integral_double_sum]
  push_cast
  refine sum_congr rfl (fun n hn => ?_)
  rw [sum_eq_single n]
  · simp; ring
  · intro b _ hb; rw [if_neg (by omega)]; simp
  · intro h; exact absurd hn h

/-! ### The continuous minor and major parts -/

/-- The minor arcs `𝔪(R)`, `R = X^ϑ`, length `L = ⌊X⌋ + 1`, as a subset of `ℝ`. -/
def minorSet (ϑ X : ℝ) : Set ℝ := {α | Minor (Ld X) (X ^ ϑ) α}

theorem measurableSet_minorSet (ϑ X : ℝ) : MeasurableSet (minorSet ϑ X) := by
  have e : minorSet ϑ X = ⋂ q : ℕ, ⋂ a : ℤ, {α : ℝ | 0 < q → (q : ℝ) ≤ X ^ ϑ →
      X ^ ϑ / (q * Ld X) < |α - a / q|} := by
    ext α; simp [minorSet, Minor, Set.mem_iInter]
  rw [e]
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun a => ?_
  by_cases h : 0 < q ∧ (q : ℝ) ≤ X ^ ϑ
  · have e2 : {α : ℝ | 0 < q → (q : ℝ) ≤ X ^ ϑ → X ^ ϑ / (q * Ld X) < |α - a / q|} =
        {α : ℝ | X ^ ϑ / (q * Ld X) < |α - a / q|} := by
      ext α; simp [h.1, h.2]
    rw [e2]
    exact measurableSet_lt measurable_const (by fun_prop)
  · have e2 : {α : ℝ | 0 < q → (q : ℝ) ≤ X ^ ϑ → X ^ ϑ / (q * Ld X) < |α - a / q|} = Set.univ := by
      ext α; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ h
    rw [e2]; exact MeasurableSet.univ

/-- `g = 1_𝔪 S²`. -/
def gMin (ϑ X : ℝ) (α : ℝ) : ℂ := (minorSet ϑ X).indicator (fun α => SΛ (Ld X) α ^ 2) α

/-- Eq 4.4: `r_𝔪(N) = ∫_𝔪 S(α)² e(-Nα) dα`, integral over `[0, 1]`. -/
def rMinI (ϑ X : ℝ) (N : ℕ) : ℂ :=
  ∫ α in (0 : ℝ)..1, (minorSet ϑ X).indicator (fun α => SΛ (Ld X) α ^ 2 * eC (-(N * α))) α

/-- Eq 4.4: `r_𝔐(N) = ∫_𝔐 S(α)² e(-Nα) dα`, `𝔐 = [0,1) \ 𝔪`. -/
def rMajI (ϑ X : ℝ) (N : ℕ) : ℂ :=
  ∫ α in (0 : ℝ)..1, (minorSet ϑ X)ᶜ.indicator (fun α => SΛ (Ld X) α ^ 2 * eC (-(N * α))) α

def rMinIR (ϑ X : ℝ) (N : ℕ) : ℝ := (rMinI ϑ X N).re

/-- Defined so that the split is exact; equal to `Re r_𝔐(N)` for `N ≤ X`, `rMajIR_eq`. -/
def rMajIR (ϑ X : ℝ) (N : ℕ) : ℝ := r2 N - rMinIR ϑ X N

theorem split_I (ϑ : ℝ) : ∀ X N, r2 N = rMajIR ϑ X N + rMinIR ϑ X N := by
  intro X N; unfold rMajIR; ring

theorem intervalIntegrable_ind {s : Set ℝ} (hs : MeasurableSet s) (L N : ℕ) :
    IntervalIntegrable (s.indicator (fun α => SΛ L α ^ 2 * eC (-(N * α)))) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hc : Continuous (fun α => SΛ L α ^ 2 * eC (-(N * α))) :=
    ((SΛ_continuous L).pow 2).mul (eC_continuous.comp (by fun_prop))
  exact (hc.integrableOn_Ioc).indicator hs

/-- The exact split of eq 4.4: `r_𝔐(N) + r_𝔪(N) = r₂(N)` for `N < L`. PROVED. -/
theorem rMajI_add_rMinI (ϑ X : ℝ) {N : ℕ} (hN : N < Ld X) :
    rMajI ϑ X N + rMinI ϑ X N = (r2 N : ℂ) := by
  have hs := measurableSet_minorSet ϑ X
  unfold rMajI rMinI
  rw [← intervalIntegral.integral_add (intervalIntegrable_ind hs.compl _ _)
    (intervalIntegrable_ind hs _ _), ← r2_eq_integral hN]
  congr 1; ext α
  rw [add_comm]
  exact Set.indicator_self_add_compl_apply _ _ _

/-- For `N ≤ X`, `rMajIR` is the real part of the CONTINUOUS major arc integral. PROVED. -/
theorem rMajIR_eq (ϑ X : ℝ) {N : ℕ} (hN : N < Ld X) : rMajIR ϑ X N = (rMajI ϑ X N).re := by
  have h := rMajI_add_rMinI ϑ X hN
  unfold rMajIR rMinIR
  have : rMajI ϑ X N = (r2 N : ℂ) - rMinI ϑ X N := by rw [← h]; ring
  rw [this, Complex.sub_re, Complex.ofReal_re]

/-! ### Bessel by Parseval on the circle -/

theorem gMin_memLp (ϑ X : ℝ) : MemLp (gMin ϑ X) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hs := measurableSet_minorSet ϑ X
  have hc : Continuous (fun α => SΛ (Ld X) α ^ 2) := (SΛ_continuous _).pow 2
  refine MemLp.of_bound ((hc.aestronglyMeasurable).indicator hs) ((∑ n ∈ range (Ld X), Λ n) ^ 2)
    (ae_of_all _ fun α => ?_)
  unfold gMin
  rw [norm_indicator_eq_indicator_norm]
  refine (Set.indicator_le_self' (fun _ _ => by positivity) α).trans ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_SΛ_le _ _) 2

theorem fourierCoeffOn_gMin (ϑ X : ℝ) (N : ℕ) :
    fourierCoeffOn (zero_lt_one' ℝ) (gMin ϑ X) (N : ℤ) = rMinI ϑ X N := by
  rw [fourierCoeffOn_eq_integral]
  unfold rMinI
  rw [show (1 : ℝ) / (1 - 0) = 1 by norm_num, one_smul]
  refine intervalIntegral.integral_congr (fun α _ => ?_)
  rw [fourier_coe_apply, smul_eq_mul, Set.indicator_mul_left]
  unfold gMin eC
  rw [mul_comm]
  congr 2
  push_cast; ring

/-- Bessel for the continuous minor part: `Σ_{N ∈ F} |r_𝔪(N)|² ≤ ∫_0^1 |1_𝔪 S²|²`. PROVED, from
Mathlib's Parseval `hasSum_sq_fourierCoeffOn`. -/
theorem bessel_minor (ϑ X : ℝ) (F : Finset ℕ) :
    ∑ N ∈ F, ‖rMinI ϑ X N‖ ^ 2 ≤ ∫ α in (0 : ℝ)..1, ‖gMin ϑ X α‖ ^ 2 := by
  have h := hasSum_sq_fourierCoeffOn (zero_lt_one' ℝ) (gMin_memLp ϑ X)
  have h2 := sum_le_hasSum (F.map Nat.castEmbedding) (fun _ _ => by positivity) h
  rw [sum_map] at h2
  simp only [Nat.castEmbedding_apply, fourierCoeffOn_gMin] at h2
  simpa using h2

/-- `∫_0^1 |1_𝔪 S²|² ≤ Q² ∫_0^1 |S|²` when `|S| ≤ Q` on `𝔪`. PROVED. -/
theorem integral_gMin_le (ϑ X Q : ℝ) (hQ : ∀ α ∈ minorSet ϑ X, ‖SΛ (Ld X) α‖ ≤ Q) :
    ∫ α in (0 : ℝ)..1, ‖gMin ϑ X α‖ ^ 2 ≤ Q ^ 2 * ∑ n ∈ range (Ld X), (Λ n) ^ 2 := by
  rw [← integral_norm_sq_S, ← intervalIntegral.integral_const_mul]
  have hs := measurableSet_minorSet ϑ X
  have e : (fun α => ‖gMin ϑ X α‖ ^ 2) =
      (minorSet ϑ X).indicator (fun α => ‖SΛ (Ld X) α‖ ^ 4) := by
    ext α; unfold gMin
    by_cases h : α ∈ minorSet ϑ X
    · simp [h, norm_pow]; ring
    · simp [h]
  have hi1 : IntervalIntegrable (fun α => ‖gMin ϑ X α‖ ^ 2) volume 0 1 := by
    rw [e, intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact ((((SΛ_continuous _).norm.pow 4)).integrableOn_Ioc).indicator hs
  have hi2 : IntervalIntegrable (fun α => Q ^ 2 * ‖SΛ (Ld X) α‖ ^ 2) volume 0 1 :=
    (continuous_const.mul ((SΛ_continuous _).norm.pow 2)).intervalIntegrable _ _
  refine intervalIntegral.integral_mono_on zero_le_one hi1 hi2 (fun α _ => ?_)
  rw [congrFun e α]
  by_cases h : α ∈ minorSet ϑ X
  · rw [Set.indicator_of_mem h]
    have h1 := hQ α h
    have h2 : ‖SΛ (Ld X) α‖ ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have : ‖SΛ (Ld X) α‖ ^ 4 = ‖SΛ (Ld X) α‖ ^ 2 * ‖SΛ (Ld X) α‖ ^ 2 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right h2 (by positivity)
  · rw [Set.indicator_of_notMem h]; positivity

/-! ### Lemma 4.2, continuous form, and the chain -/

/-- `MinorL2` for the CONTINUOUS minor part `r_𝔪(N) = ∫_𝔪 S² e(-Nα)` of eq 4.4, as in the proof of
Lemma 4.2, page 16: `Σ_{X/2 ≤ N ≤ X} |r_𝔪(N)|² ≤ ∫_𝔪 |S|⁴ ≤ sup_𝔪 |S|² Σ_{n<L} Λ(n)²`.
CONDITIONAL ON `MinorArcSup κ`. -/
theorem minorL2_cont_of_sup {ϑ κ : ℝ} (hϑ : 0 ≤ ϑ) (hκ : 0 ≤ κ) (hS : MinorArcSup κ) :
    MinorL2 ϑ κ (rMinIR ϑ) := by
  intro ε hε
  set e := ε / 4 with he
  have he0 : 0 < e := by positivity
  obtain ⟨Cs, hCs, hsup⟩ := hS e he0
  refine ⟨2 * Cs ^ 2 / e ^ 2 * 2 ^ ε * (8 + 2 ^ (2 * κ + 1)), by positivity, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  set L := Ld X with hLd
  have hL1 : 1 ≤ L := by rw [hLd]; unfold Ld; omega
  have hLR1 : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hLR0 : (0 : ℝ) < L := by linarith
  have hL2X : (L : ℝ) ≤ 2 * X := by
    rw [hLd]; unfold Ld; push_cast
    have := Nat.floor_le hX0.le; linarith
  set R := X ^ ϑ with hR
  have hR1 : 1 ≤ R := Real.one_le_rpow hX hϑ
  have hR0 : 0 < R := by linarith
  set Q := Cs * (L : ℝ) ^ e * (L / Real.sqrt R + (L : ℝ) ^ κ) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hpt : ∀ α ∈ minorSet ϑ X, ‖SΛ L α‖ ≤ Q := by
    intro α hα
    exact hsup L R α hL1 hR1 hα
  have stepAB : ∑ N ∈ Icc ⌈X / 2⌉₊ ⌊X⌋₊, rMinIR ϑ X N ^ 2 ≤ Q ^ 2 * ∑ n ∈ range L, (Λ n) ^ 2 := by
    calc ∑ N ∈ Icc ⌈X / 2⌉₊ ⌊X⌋₊, rMinIR ϑ X N ^ 2
        ≤ ∑ N ∈ Icc ⌈X / 2⌉₊ ⌊X⌋₊, ‖rMinI ϑ X N‖ ^ 2 := by
          apply sum_le_sum; intro N _
          unfold rMinIR
          have := Complex.abs_re_le_norm (rMinI ϑ X N)
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ ≤ ∫ α in (0 : ℝ)..1, ‖gMin ϑ X α‖ ^ 2 := bessel_minor ϑ X _
      _ ≤ Q ^ 2 * ∑ n ∈ range L, (Λ n) ^ 2 := integral_gMin_le ϑ X Q hpt
  have hlog : Real.log L ≤ (L : ℝ) ^ e / e := Real.log_le_rpow_div hLR0.le he0
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hLR1
  have stepC : ∑ n ∈ range L, (Λ n) ^ 2 ≤ L * ((L : ℝ) ^ e / e) ^ 2 := by
    calc ∑ n ∈ range L, (Λ n) ^ 2 ≤ ∑ n ∈ range L, ((L : ℝ) ^ e / e) ^ 2 := by
          apply sum_le_sum; intro n hn
          rw [mem_range] at hn
          have h1 : Λ n ≤ Real.log L := by
            refine vonMangoldt_le_log.trans ?_
            rcases Nat.eq_zero_or_pos n with h | h
            · subst h; simpa using hlog0
            · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hn.le)
          exact pow_le_pow_left₀ vonMangoldt_nonneg (h1.trans hlog) 2
      _ = L * ((L : ℝ) ^ e / e) ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]
  set P := (L : ℝ) ^ e with hP
  have hP0 : 0 ≤ P := by positivity
  set K := (L : ℝ) ^ κ with hK
  have hK0 : 0 ≤ K := by positivity
  have claim1 : Q ^ 2 ≤ 2 * Cs ^ 2 * P ^ 2 * (L ^ 2 / R + K ^ 2) := by
    have hsq : (L / Real.sqrt R) ^ 2 = L ^ 2 / R := by
      rw [div_pow, Real.sq_sqrt hR0.le]
    have : (L / Real.sqrt R + K) ^ 2 ≤ 2 * ((L / Real.sqrt R) ^ 2 + K ^ 2) := by
      nlinarith [sq_nonneg (L / Real.sqrt R - K)]
    rw [hsq] at this
    calc Q ^ 2 = Cs ^ 2 * P ^ 2 * (L / Real.sqrt R + K) ^ 2 := by rw [hQ]; ring
      _ ≤ Cs ^ 2 * P ^ 2 * (2 * (L ^ 2 / R + K ^ 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * Cs ^ 2 * P ^ 2 * (L ^ 2 / R + K ^ 2) := by ring
  have claim2 : P ^ 4 ≤ 2 ^ ε * X ^ ε := by
    have e4 : P ^ 4 = (L : ℝ) ^ ε := by
      rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hLR0.le, he]; norm_num
    rw [e4, ← Real.mul_rpow (by norm_num) hX0.le]
    exact Real.rpow_le_rpow hLR0.le hL2X hε.le
  have claim3 : (L : ℝ) ^ 3 / R ≤ 8 * X ^ (3 - ϑ) := by
    rw [Real.rpow_sub hX0, div_le_iff₀ hR0]
    have : X ^ (3 : ℝ) = X ^ 3 := by norm_cast
    rw [this, hR]
    have hL3 : (L : ℝ) ^ 3 ≤ (2 * X) ^ 3 := pow_le_pow_left₀ hLR0.le hL2X 3
    have : 8 * (X ^ 3 / X ^ ϑ) * X ^ ϑ = 8 * X ^ 3 := by
      field_simp
    rw [this]; nlinarith
  have claim4 : (L : ℝ) * K ^ 2 ≤ 2 ^ (2 * κ + 1) * X ^ (2 * κ + 1) := by
    have e1 : (L : ℝ) * K ^ 2 = (L : ℝ) ^ (2 * κ + 1) := by
      rw [hK, ← Real.rpow_natCast, ← Real.rpow_mul hLR0.le, Real.rpow_add hLR0, Real.rpow_one]
      push_cast; ring
    rw [e1, ← Real.mul_rpow (by norm_num) hX0.le]
    exact Real.rpow_le_rpow hLR0.le hL2X (by linarith)
  have hX3 : 0 ≤ X ^ (3 - ϑ) := by positivity
  have hX4 : 0 ≤ X ^ (2 * κ + 1) := by positivity
  have hXε : 0 ≤ X ^ ε := by positivity
  have h2κ : 0 ≤ (2 : ℝ) ^ (2 * κ + 1) := by positivity
  have h2ε : 0 ≤ (2 : ℝ) ^ ε := by positivity
  calc ∑ N ∈ Icc ⌈X / 2⌉₊ ⌊X⌋₊, rMinIR ϑ X N ^ 2
      ≤ Q ^ 2 * (L * (P / e) ^ 2) :=
        stepAB.trans (mul_le_mul_of_nonneg_left stepC (by positivity))
    _ ≤ 2 * Cs ^ 2 * P ^ 2 * (L ^ 2 / R + K ^ 2) * (L * (P / e) ^ 2) :=
        mul_le_mul_of_nonneg_right claim1 (by positivity)
    _ = 2 * Cs ^ 2 / e ^ 2 * P ^ 4 * ((L : ℝ) ^ 3 / R + L * K ^ 2) := by
        field_simp
    _ ≤ 2 * Cs ^ 2 / e ^ 2 * (2 ^ ε * X ^ ε) *
          (8 * X ^ (3 - ϑ) + 2 ^ (2 * κ + 1) * X ^ (2 * κ + 1)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left claim2 (by positivity)) (by linarith)
          (by positivity) (by positivity)
    _ ≤ 2 * Cs ^ 2 / e ^ 2 * 2 ^ ε * (8 + 2 ^ (2 * κ + 1)) * X ^ ε *
          (X ^ (3 - ϑ) + X ^ (2 * κ + 1)) := by
        have : 8 * X ^ (3 - ϑ) + 2 ^ (2 * κ + 1) * X ^ (2 * κ + 1) ≤
            (8 + 2 ^ (2 * κ + 1)) * (X ^ (3 - ϑ) + X ^ (2 * κ + 1)) := by nlinarith
        have hc : 0 ≤ 2 * Cs ^ 2 / e ^ 2 * (2 ^ ε * X ^ ε) := by positivity
        calc 2 * Cs ^ 2 / e ^ 2 * (2 ^ ε * X ^ ε) *
              (8 * X ^ (3 - ϑ) + 2 ^ (2 * κ + 1) * X ^ (2 * κ + 1))
            ≤ 2 * Cs ^ 2 / e ^ 2 * (2 ^ ε * X ^ ε) *
              ((8 + 2 ^ (2 * κ + 1)) * (X ^ (3 - ϑ) + X ^ (2 * κ + 1))) :=
              mul_le_mul_of_nonneg_left this hc
          _ = _ := by ring


/-- The major arc formula of the page 31 Sketch for the COMPLEX continuous integral
`r_𝔐(N) = ∫_𝔐 S(α)² e(-Nα) dα`, CITED from Pintz [20, Thm 1]: for every even `N ∈ [X/2, X]`,
`|r_𝔐(N) - main| ≤ C (𝔖(N) X (δ̃L)^{c'} + 𝔖(N) N r̃/φ(r̃)² + X^{1-ε₀})`. -/
def MajorFormula81C (GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ) (ϑ : ℝ) (rMaj : ℝ → ℕ → ℂ) :
    Prop :=
  ∃ h c' ε0 C : ℝ, 0 < h ∧ 0 < c' ∧ 0 < ε0 ∧ 0 < C ∧
    ∀ X : ℝ, 2 ≤ X → ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (δt : ℝ),
    Siegel81 ϑ h X r χ δt →
      ∀ N ∈ evenWin X, ‖rMaj X N - (main83 GS r χ δt N : ℂ)‖ ≤ C * err83 c' ε0 X r δt N

theorem lt_Ld_of_mem_evenWin {X : ℝ} {N : ℕ} (hN : N ∈ evenWin X) : N < Ld X := by
  simp only [evenWin, mem_filter, mem_Icc] at hN
  unfold Ld; omega

/-- The printed complex form at the continuous `r_𝔐` gives the real form at `rMajIR`. PROVED. -/
theorem majorFormula81_of_cont {GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ} {ϑ : ℝ}
    (hM : MajorFormula81C GS ϑ (rMajI ϑ)) : MajorFormula81 GS ϑ (rMajIR ϑ) := by
  obtain ⟨h, c', ε0, C, hh, hc', hε0, hC, hb⟩ := hM
  refine ⟨h, c', ε0, C, hh, hc', hε0, hC, fun X hX r _ χ δt hS N hN => ?_⟩
  rw [rMajIR_eq ϑ X (lt_Ld_of_mem_evenWin hN)]
  refine le_trans ?_ (hb X hX r χ δt hS N hN)
  have := Complex.abs_re_le_norm (rMajI ϑ X N - (main83 GS r χ δt N : ℂ))
  rwa [Complex.sub_re, Complex.ofReal_re] at this

/-- Theorem 8.2 with `X^{7/12}` exceptions, `A > 12/5`, with the major arc input at the printed
CONTINUOUS major arc integral. CONDITIONAL ON `MajorFormula81C GS (5/12) (rMajI (5/12))`,
`Display81Mult GS` and `MPRTheorem11`. -/
theorem theorem82σ_seven_twelfths_cont {GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ}
    (hM : MajorFormula81C GS (5 / 12) (rMajI (5 / 12))) (hD : Display81Mult GS)
    (hMPR : MPRTheorem11) : Theorem82σ (7 / 12) := by
  have hm : MinorL2 (5 / 12) (19 / 24) (rMinIR (5 / 12)) :=
    minorL2_cont_of_sup (by norm_num) (by norm_num) (minorArcSup_of_MPR hMPR)
  have hU : Prop81PrintUnif GS (5 / 12) (7 / 12) :=
    prop81PrintUnif_of_parts (split_I _) (by norm_num) (majorFormula81_of_cont hM) hm
  exact theorem82σ_of_prop81σ _ (prop81AtMultiplesσ_of_prop81 (by norm_num) (by norm_num)
    (prop81_of_printUnif hU hD))

/-- Vacuity test for `minorSet`: at `X = 4`, `ϑ = 0`, so `L = 5`, `R = 1`, the point `3/10` lies on
`𝔪(1)`. PROVED. -/
theorem vacuity_minorSet : (3 / 10 : ℝ) ∈ minorSet 0 4 := by
  have h := mem_minorJ vacuity_minorJ
  have hM : Md 4 = 10 := by unfold Md Ld; norm_num
  rw [hM] at h
  unfold minorSet
  simpa using h

/-- Vacuity test for the eq 4.4 identity: its hypothesis `N < L` holds at `L = 3`, `N = 2`. PROVED. -/
theorem vacuity_r2_integral : ∫ α in (0 : ℝ)..1, SΛ 3 α ^ 2 * eC (-((2 : ℕ) * α)) = (r2 2 : ℂ) :=
  r2_eq_integral (by norm_num)

end

end LeanLab.ExceptionalSet.BG2026
