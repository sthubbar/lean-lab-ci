/-
CODEX task85 status: eight original leaves now have proofs. The remaining hybrid_large_sieve assertion is refuted in HybridShiftBarrier for unrestricted M. Its sealed declaration is unchanged pending review. The zero sum assemblies remain conditional on their density and zero free hypotheses.
AI wrote the Lean code. Binary Goldbach is open.
-/
/-
P0015 Montgomery and Vaughan 1975, The exceptional set in Goldbach's problem, Acta Arith. 27,
353-370. Unit U-1524, run 20261025T2003Z-426, ARCHITECT DECOMPOSE.

File c of three: the Gallagher-type zero density and exceptional zero bookkeeping behind
(7.1), Gallagher's Theorem 7 as modified in section 7, split into LEAF lemmas. The analytic
inputs are Gallagher's hybrid large sieve and the zero detection by a mollifier; what turns a
density estimate `N*(α, T) ≪ T^{c(1-α)}` plus a zero-free region `β ≤ 1 - η` into the saving
`Σ_ρ x^{β-1} ≪ x^{-η/2}` is finitary and is assembled here with zero sorry.

SOURCE: the impan.pl scan could not be fetched in this unit (WebFetch CLIENT_ERROR). The leaves
follow P. X. Gallagher, A large sieve density estimate near σ = 1, Invent. Math. 11 (1970)
329-339, Theorems 2 and 4 and section 4; Montgomery, Topics, LNM 227, Ch. 12 (zero detection),
Theorem 6.4 (hybrid sieve); Iwaniec-Kowalski, Analytic Number Theory, Sections 10.1 to 10.4
(density by large sieve) and 5.9 (Deuring-Heilbronn).

Leaves (sorry): `layer_cake_sum`, `count_integral_le`, `integral_ratio_le`, `card_chars_le`,
`hybrid_large_sieve`, `mollifier_coeff_one`, `mollifier_coeff_vanish`, `mollifier_coeff_le`,
`spaced_subfamily`.
Proved bookkeeping: `norm_cpow_div_le`, `zero_free_term`, `deuring_heilbronn_term`.
Assemblies, zero sorry: `zero_sum_le` CONDITIONAL ON the density count `hcount` and the
zero-free bound `β ≤ 1 - η` taken as hypotheses, from `layer_cake_sum`, `count_integral_le`,
`integral_ratio_le`; `zero_sum_le_exp`, the form `≤ 3A exp(-c log x/(2 log P))` of (7.1).

AI-written Lean code, Claude, unit U-1524. Checked only by the Lean kernel.
KNOWN mathematics. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.PNTPort.LargeSieve.Multiplicative

namespace LeanLab.ExceptionalSet.Decomp1524c

open Real MeasureTheory Finset
open MeasureTheory SchwartzMap FourierTransform
open scoped SchwartzMap Topology ContDiff ENNReal

attribute [local instance] Classical.propDecidable

/-! ### From a density count to a zero sum -/

/-- LEAF. Layer cake for a finite family of zeros: if `σ₀ ≤ β_i ≤ 1` and `x > 1` then
`Σ_i x^{β_i-1} = x^{σ₀-1} #I + ∫_{σ₀}^{1} log x · x^{α-1} #{i : β_i ≥ α} dα`, since
`x^{β-1} - x^{σ₀-1} = ∫_{σ₀}^{β} log x · x^{α-1} dα`. Gallagher 1970 section 4;
Iwaniec-Kowalski Section 10.4. Unit U-1524. -/
theorem layer_cake_sum {ι : Type*} (I : Finset ι) (β : ι → ℝ) {σ₀ x : ℝ} (hx : 1 < x)
    (hβ : ∀ i ∈ I, σ₀ ≤ β i ∧ β i ≤ 1) :
    ∑ i ∈ I, x ^ (β i - 1) = x ^ (σ₀ - 1) * I.card +
      ∫ α in σ₀..1, Real.log x * x ^ (α - 1) * ((I.filter (fun i => α ≤ β i)).card : ℝ) := by
  classical
  have hx0 : 0 < x := by linarith
  let f : ℝ → ℝ := fun a => Real.log x * x^(a-1)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hd (t : ℝ) : HasDerivAt (fun a : ℝ => x^(a-1)) (f t) t := by
    simpa [f] using HasDerivAt.const_rpow hx0 ((hasDerivAt_id t).sub_const 1)
  have hpoint (a : ℝ) : Real.log x * x^(a-1) * ((I.filter (fun i => a ≤ β i)).card : ℝ) =
      ∑ i ∈ I, (Set.Iic (β i)).indicator f a := by
    simp only [Set.indicator_apply, Set.mem_Iic]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    dsimp [f]
    ring
  have hint (i : ι) : IntervalIntegrable ((Set.Iic (β i)).indicator f) volume σ₀ 1 := by
    have hh := hf.intervalIntegrable (μ := volume) (a := σ₀) (b := 1)
    exact ⟨hh.1.indicator measurableSet_Iic, hh.2.indicator measurableSet_Iic⟩
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finset_sum (fun i hi => hint i)]
  have he (i : ι) (hi : i ∈ I) : ∫ a in σ₀..1, (Set.Iic (β i)).indicator f a =
      x^(β i-1)-x^(σ₀-1) := by
    change (∫ a in σ₀..1, {a : ℝ | a ≤ β i}.indicator f a) = _
    rw [intervalIntegral.integral_indicator (f := f) (μ := volume) (hβ i hi)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t) (hf.intervalIntegrable _ _)
  rw [Finset.sum_congr rfl he, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- LEAF. Inserting the density count: if `σ₀ ≤ β_i ≤ 1 - η`, `η ≥ 0`, `x > 1`, `Y > 0`, `A ≥ 0`
and `#{i : β_i ≥ α} ≤ A Y^{1-α}` for `α ∈ [σ₀, 1]`, then
`∫_{σ₀}^{1} log x · x^{α-1} #{β_i ≥ α} dα ≤ A ∫_{σ₀}^{1-η} log x (Y/x)^{1-α} dα`.
Gallagher 1970 section 4; Iwaniec-Kowalski Section 10.4. Unit U-1524. -/
theorem count_integral_le {ι : Type*} (I : Finset ι) (β : ι → ℝ) {σ₀ η x Y A : ℝ}
    (hx : 1 < x) (hY : 0 < Y) (hA : 0 ≤ A) (hη : 0 ≤ η) (hσ : σ₀ ≤ 1 - η)
    (hβ : ∀ i ∈ I, σ₀ ≤ β i ∧ β i ≤ 1 - η)
    (hcount : ∀ α ∈ Set.Icc σ₀ 1, ((I.filter (fun i => α ≤ β i)).card : ℝ) ≤ A * Y ^ (1 - α)) :
    ∫ α in σ₀..1, Real.log x * x ^ (α - 1) * ((I.filter (fun i => α ≤ β i)).card : ℝ) ≤
      A * ∫ α in σ₀..(1 - η), Real.log x * (Y / x) ^ (1 - α) := by
  classical
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Real.log x := (Real.log_pos hx).le
  let f : ℝ → ℝ := fun a => Real.log x * x^(a-1)
  let g : ℝ → ℝ := fun a => f a * ((I.filter (fun i => a ≤ β i)).card : ℝ)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hgpoint (a : ℝ) : g a = ∑ i ∈ I, (Set.Iic (β i)).indicator f a := by
    simp only [Set.indicator_apply, Set.mem_Iic]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    dsimp [g]
    ring
  have hg (a b : ℝ) : IntervalIntegrable g volume a b := by
    have hh : g = fun t => ∑ i ∈ I, (Set.Iic (β i)).indicator f t := funext hgpoint
    rw [hh]
    have hi : ∀ i ∈ I, IntervalIntegrable ((Set.Iic (β i)).indicator f) volume a b := by
      intro i hi
      have hfint := hf.intervalIntegrable (μ := volume) a b
      exact ⟨hfint.1.indicator measurableSet_Iic, hfint.2.indicator measurableSet_Iic⟩
    convert IntervalIntegrable.sum I hi using 1
    ext t
    simp only [Finset.sum_apply]
  have hz : ∫ a in (1-η)..1, g a = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with a
    intro ha
    rw [Set.uIoc_of_le (by linarith : 1-η ≤ 1)] at ha
    have he : I.filter (fun i => a ≤ β i) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi
      linarith [(hβ i hi).2, ha.1]
    simp [g, he]
  have heq : (∫ a in σ₀..1, g a) = ∫ a in σ₀..(1-η), g a := by
    have hh := intervalIntegral.integral_add_adjacent_intervals (hg σ₀ (1-η)) (hg (1-η) 1)
    rw [hz, add_zero] at hh
    exact hh.symm
  change (∫ a in σ₀..1, g a) ≤ _
  rw [heq, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hσ (hg σ₀ (1-η))
    ((by fun_prop : Continuous (fun a : ℝ => A * (Real.log x * (Y/x)^(1-a)))).intervalIntegrable _ _)
  intro a ha
  have hc := hcount a ⟨ha.1, by linarith [ha.2]⟩
  have hpow : x^(a-1) * Y^(1-a) = (Y/x)^(1-a) := by
    rw [Real.div_rpow hY.le hx0.le, div_eq_mul_inv, ← Real.rpow_neg hx0.le, neg_sub]
    ring
  calc g a ≤ f a * (A * Y^(1-a)) := mul_le_mul_of_nonneg_left hc (by dsimp [f]; positivity)
    _ = A * (Real.log x * (Y/x)^(1-a)) := by dsimp [f]; rw [← hpow]; ring

/-- LEAF. The closed form: for `x > 1`, `0 < Y ≤ √x`, `η ≥ 0`, `σ₀ ≤ 1 - η`,
`∫_{σ₀}^{1-η} log x (Y/x)^{1-α} dα ≤ 2 x^{-η/2}`, since with `r = Y/x ≤ x^{-1/2}` the integral is
at most `log x · r^η / log(1/r)` and `log(1/r) ≥ (log x)/2`. Gallagher 1970 section 4.
Unit U-1524. -/
theorem integral_ratio_le {σ₀ η x Y : ℝ} (hx : 1 < x) (hY : 0 < Y) (hYx : Y ≤ Real.sqrt x)
    (hη : 0 ≤ η) (hσ : σ₀ ≤ 1 - η) :
    ∫ α in σ₀..(1 - η), Real.log x * (Y / x) ^ (1 - α) ≤ 2 * x ^ (-η / 2) := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  let r := Y/x
  have hr0 : 0 < r := div_pos hY hx0
  have hlog : Real.log r ≤ -(Real.log x)/2 := by
    have hh := Real.log_le_log hY hYx
    rw [Real.log_sqrt hx0.le] at hh
    dsimp [r]
    rw [Real.log_div hY.ne' hx0.ne']
    linarith
  have hlog0 : Real.log r < 0 := by linarith
  let c := -(Real.log x / Real.log r)
  have hc0 : 0 ≤ c := by dsimp [c]; exact neg_nonneg.mpr (div_nonpos_of_nonneg_of_nonpos hL.le hlog0.le)
  have hc2 : c ≤ 2 := by
    dsimp [c]
    have hh : -2 ≤ Real.log x / Real.log r := (le_div_iff_of_neg hlog0).2 (by linarith)
    linarith
  have hd : ∀ t : ℝ, HasDerivAt (fun a : ℝ => c * r^(1-a)) (Real.log x * r^(1-t)) t := by
    intro t
    have hh := HasDerivAt.const_rpow hr0 ((hasDerivAt_id t).const_sub 1)
    convert hh.const_mul c using 1 <;> dsimp [c] <;> field_simp [hlog0.ne] <;> ring
  have hi : IntervalIntegrable (fun a : ℝ => Real.log x * r^(1-a)) volume σ₀ (1-η) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t) hi
  change (∫ a in σ₀..(1-η), Real.log x * r^(1-a)) ≤ _
  rw [hint]
  have he : (1-(1-η) : ℝ) = η := by ring
  rw [he]
  have hr : r^η ≤ x^(-η/2) := by
    rw [Real.rpow_def_of_pos hr0, Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hlog hη]
  have hnon : 0 ≤ r^(1-σ₀) := by positivity
  calc c * r^η - c * r^(1-σ₀) ≤ c * r^η := by nlinarith [mul_nonneg hc0 hnon]
    _ ≤ 2 * x^(-η/2) := mul_le_mul hc2 hr (by positivity) (by norm_num)

/-- **Zero sum from a density estimate**, PROVED from `layer_cake_sum`, `count_integral_le`,
`integral_ratio_le`; CONDITIONAL ON the density count `hcount`, `#{β_i ≥ α} ≤ A Y^{1-α}`
(Gallagher 1970 Theorem 4 with `Y = T^c`), and the zero-free region `β_i ≤ 1 - η`, both taken
as hypotheses: for `x > 1`, `0 < Y ≤ √x`, `0 ≤ η ≤ 1 - σ₀`,
`Σ_i x^{β_i - 1} ≤ 3 A x^{-η/2}`. Gallagher 1970 section 4; Montgomery-Vaughan 1975 (7.1).
Unit U-1524. -/
theorem zero_sum_le {ι : Type*} (I : Finset ι) (β : ι → ℝ) {σ₀ η x Y A : ℝ}
    (hx : 1 < x) (hY : 0 < Y) (hYx : Y ≤ Real.sqrt x) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hσ : σ₀ ≤ 1 - η) (hβ : ∀ i ∈ I, σ₀ ≤ β i ∧ β i ≤ 1 - η)
    (hcount : ∀ α ∈ Set.Icc σ₀ 1, ((I.filter (fun i => α ≤ β i)).card : ℝ) ≤ A * Y ^ (1 - α)) :
    ∑ i ∈ I, x ^ (β i - 1) ≤ 3 * A * x ^ (-η / 2) := by
  have hx0 : 0 < x := by linarith
  have hβ' : ∀ i ∈ I, σ₀ ≤ β i ∧ β i ≤ 1 := fun i hi =>
    ⟨(hβ i hi).1, by linarith [(hβ i hi).2]⟩
  rw [layer_cake_sum I β hx hβ']
  have h1 := count_integral_le I β hx hY hA hη hσ hβ hcount
  have h2 := integral_ratio_le hx hY hYx hη hσ
  -- the first term
  have hσ1 : σ₀ ≤ 1 := by linarith
  have hcard : (I.card : ℝ) ≤ A * Y ^ (1 - σ₀) := by
    have := hcount σ₀ ⟨le_rfl, hσ1⟩
    have hf : I.filter (fun i => σ₀ ≤ β i) = I :=
      Finset.filter_true_of_mem (fun i hi => (hβ i hi).1)
    rwa [hf] at this
  have hsqrt : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
  have hratio : Y / x ≤ x ^ (-(1 / 2) : ℝ) := by
    rw [Real.rpow_neg hx0.le, div_le_iff₀ hx0]
    have hx12 : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
      rw [← Real.rpow_add hx0]; norm_num
    have hpos : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hinv : (x ^ (1 / 2 : ℝ))⁻¹ * x = x ^ (1 / 2 : ℝ) := by
      rw [inv_mul_eq_div, div_eq_iff hpos.ne']
      exact hx12.symm
    rw [hinv, ← hsqrt]
    exact hYx
  have hfirst : x ^ (σ₀ - 1) * (A * Y ^ (1 - σ₀)) ≤ A * x ^ (-η / 2) := by
    have heq : x ^ (σ₀ - 1) * (A * Y ^ (1 - σ₀)) = A * (Y / x) ^ (1 - σ₀) := by
      rw [Real.div_rpow hY.le hx0.le, div_eq_mul_inv, ← Real.rpow_neg hx0.le, neg_sub]
      ring
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ hA
    calc (Y / x) ^ (1 - σ₀) ≤ (x ^ (-(1 / 2) : ℝ)) ^ (1 - σ₀) :=
          Real.rpow_le_rpow (div_nonneg hY.le hx0.le) hratio (by linarith)
      _ = x ^ (-(1 / 2) * (1 - σ₀)) := by rw [← Real.rpow_mul hx0.le]
      _ ≤ x ^ (-η / 2) := by
          apply Real.rpow_le_rpow_of_exponent_le hx.le
          linarith
  have hxσ : 0 ≤ x ^ (σ₀ - 1) := Real.rpow_nonneg hx0.le _
  have hfirst' : x ^ (σ₀ - 1) * (I.card : ℝ) ≤ A * x ^ (-η / 2) :=
    (mul_le_mul_of_nonneg_left hcard hxσ).trans hfirst
  have hsecond : A * ∫ α in σ₀..(1 - η), Real.log x * (Y / x) ^ (1 - α) ≤
      A * (2 * x ^ (-η / 2)) := mul_le_mul_of_nonneg_left h2 hA
  linarith

/-- **The saving of (7.1)**, PROVED from `zero_sum_le`: with the zero-free region
`β_i ≤ 1 - c/log P`, `P > 1`, `c ≥ 0`, `c/log P ≤ 1 - σ₀`, and the density count,
`Σ_i x^{β_i-1} ≤ 3 A exp(-c log x / (2 log P))`. CONDITIONAL ON `hcount` as in `zero_sum_le`.
Gallagher 1970 Theorem 7; Montgomery-Vaughan 1975 (7.1), p. 365. Unit U-1524. -/
theorem zero_sum_le_exp {ι : Type*} (I : Finset ι) (β : ι → ℝ) {σ₀ c P x Y A : ℝ}
    (hx : 1 < x) (hY : 0 < Y) (hYx : Y ≤ Real.sqrt x) (hA : 0 ≤ A) (hP : 1 < P) (hc : 0 ≤ c)
    (hσ : σ₀ ≤ 1 - c / Real.log P) (hβ : ∀ i ∈ I, σ₀ ≤ β i ∧ β i ≤ 1 - c / Real.log P)
    (hcount : ∀ α ∈ Set.Icc σ₀ 1, ((I.filter (fun i => α ≤ β i)).card : ℝ) ≤ A * Y ^ (1 - α)) :
    ∑ i ∈ I, x ^ (β i - 1) ≤ 3 * A * Real.exp (-(c * Real.log x / (2 * Real.log P))) := by
  have hlogP : 0 < Real.log P := Real.log_pos hP
  have hη : 0 ≤ c / Real.log P := div_nonneg hc hlogP.le
  have h := zero_sum_le I β hx hY hYx hA hη hσ hβ hcount
  have hx0 : 0 < x := by linarith
  have heq : x ^ (-(c / Real.log P) / 2) = Real.exp (-(c * Real.log x / (2 * Real.log P))) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    field_simp
  rwa [heq] at h

/-! ### Single zero bookkeeping, proved -/

/-- `|x^ρ/ρ| ≤ 2 x^{Re ρ}` for `x > 0` and `Re ρ ≥ 1/2`. PROVED. Unit U-1524. -/
theorem norm_cpow_div_le {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ : 1 / 2 ≤ ρ.re) :
    ‖(x : ℂ) ^ ρ / ρ‖ ≤ 2 * x ^ ρ.re := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hn : 1 / 2 ≤ ‖ρ‖ := hρ.trans (Complex.re_le_norm ρ)
  have hpos : 0 < ‖ρ‖ := by linarith
  have hxr : 0 ≤ x ^ ρ.re := Real.rpow_nonneg hx.le _
  rw [div_le_iff₀ hpos]
  nlinarith

/-- A zero in the region `β ≤ 1 - c/log P`, `c ≥ 0`, gives `x^{β-1} ≤ exp(-c log x/log P)` for
`x, P > 1`. PROVED. Montgomery-Vaughan 1975 section 7. Unit U-1524. -/
theorem zero_free_term {x P c β : ℝ} (hx : 1 < x) (hP : 1 < P)
    (hβ : β ≤ 1 - c / Real.log P) :
    x ^ (β - 1) ≤ Real.exp (-(c * Real.log x / Real.log P)) := by
  have hx0 : 0 < x := by linarith
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.mpr
  have hlx : 0 < Real.log x := Real.log_pos hx
  have : (β - 1) ≤ -(c / Real.log P) := by linarith
  calc Real.log x * (β - 1) ≤ Real.log x * (-(c / Real.log P)) :=
        mul_le_mul_of_nonneg_left this hlx.le
    _ = -(c * Real.log x / Real.log P) := by ring

/-- Deuring-Heilbronn shape: a zero with `β ≤ 1 - c log(c'/λ)/log P`, where `λ, c' > 0`, gives
`x^{β-1} ≤ (λ/c')^{c log x/log P}` for `x, P > 1`. PROVED. Iwaniec-Kowalski Theorem 5.28
shape; Montgomery-Vaughan 1975 section 7. Unit U-1524. -/
theorem deuring_heilbronn_term {x P c c' lam β : ℝ} (hx : 1 < x) (hP : 1 < P) (hlam : 0 < lam)
    (hc' : 0 < c') (hβ : β ≤ 1 - c * Real.log (c' / lam) / Real.log P) :
    x ^ (β - 1) ≤ (lam / c') ^ (c * Real.log x / Real.log P) := by
  have h := zero_free_term (c := c * Real.log (c' / lam)) hx hP hβ
  refine h.trans (le_of_eq ?_)
  rw [Real.rpow_def_of_pos (div_pos hlam hc')]
  congr 1
  rw [show lam / c' = (c' / lam)⁻¹ by rw [inv_div], Real.log_inv]
  ring

/-! ### Large sieve inputs to the density estimate -/

/-- LEAF. The number of characters mod `q` is at most `φ(q) ≤ q`, so
`Σ_{q ≤ Q} #{χ mod q} ≤ Q²`. Gallagher 1970 section 4 (counting pairs `(q, χ)`).
Unit U-1524. -/
theorem card_chars_le (Q : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, (Fintype.card (DirichletCharacter ℂ q) : ℝ) ≤ (Q : ℝ) ^ 2 := by
  calc ∑ q ∈ Finset.Icc 1 Q, (Fintype.card (DirichletCharacter ℂ q) : ℝ)
      ≤ ∑ _q ∈ Finset.Icc 1 Q, (Q : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
        letI : NeZero q := ⟨hq0.ne'⟩
        have hc := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
        rw [Nat.card_eq_fintype_card] at hc
        rw [hc]
        exact_mod_cast (Nat.totient_le q).trans (Finset.mem_Icc.mp hq).2
    _ = _ := by simp; ring

/-! ### Part 1: the Plancherel bridge for `L1 ∩ L2` functions -/

/-- An integrable function has the same Fourier pairing as its L2 class. -/
private theorem p_fourier_pairing (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2)
    (g : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, g x * 𝓕 f x =
      ∫ x : ℝ, g x * (𝓕 (h₂.toLp f) : Lp ℂ 2) x := by
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume)
    Real.continuous_fourierChar (L := (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ))
    (by fun_prop) g.integrable h₁
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    exact flip_innerₗ ℝ
  rw [hflip] at hswap
  have hd := congrArg (fun d : 𝓢'(ℝ, ℂ) => d g)
    (Lp.fourier_toTemperedDistribution_eq (h₂.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hd
  calc
    _ = ∫ x : ℝ, (𝓕 g) x * f x := by
      simpa only [SchwartzMap.fourier_coe, Real.fourier_eq,
        VectorFourier.fourierIntegral, innerₗ_apply_apply, smul_eq_mul] using hswap.symm
    _ = ∫ x : ℝ, (𝓕 g) x * (h₂.toLp f) x := by
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx]
    _ = _ := by simpa only [smul_eq_mul] using hd

/-- The Fourier integral represents the Fourier transform of the L2 class. -/
private theorem p_fourierIntegral_ae_eq (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (h₂.toLp f) : Lp ℂ 2) := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h₁
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    ((Lp.memLp (𝓕 (h₂.toLp f))).locallyIntegrable (by norm_num))
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  simpa using p_fourier_pairing f h₁ h₂ (hc'.toSchwartzMap hg')

/-- The square of the L2 norm is the integral of the squared pointwise norm. -/
private theorem p_integral_norm_sq_coe (u : Lp (α := ℝ) ℂ 2) :
    ∫ x : ℝ, ‖u x‖ ^ 2 = ‖u‖ ^ 2 := by
  have hi := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def (𝕜 := ℂ) u u)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) u u)] at hi
  simpa only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    using hi.symm

/-- Plancherel for the Fourier integral on L1 intersect L2. -/
private theorem p_integral_norm_sq_fourier (f : ℝ → ℂ) (h₁ : Integrable f)
    (h₂ : MemLp f 2) :
    ∫ t : ℝ, ‖𝓕 f t‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  calc
    _ = ∫ t : ℝ, ‖(𝓕 (h₂.toLp f) : Lp ℂ 2 volume) t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [p_fourierIntegral_ae_eq f h₁ h₂] with t ht
      rw [ht]
    _ = ‖𝓕 (h₂.toLp f)‖ ^ 2 := p_integral_norm_sq_coe _
    _ = ‖h₂.toLp f‖ ^ 2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ x : ℝ, ‖f x‖ ^ 2 := by
      rw [← p_integral_norm_sq_coe]
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx]

/-- The Fourier integral of an L1 intersect L2 function belongs to L2. -/
private theorem p_fourierIntegral_memLp (f : ℝ → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    MemLp (𝓕 f) 2 :=
  (memLp_congr_ae (p_fourierIntegral_ae_eq f h₁ h₂)).mpr (Lp.memLp _)

/-! ### Part 2: the moving frequency window at real centres -/

/-- The Fourier integral of an interval indicator is an interval integral. -/
private theorem wf_fourier_interval (b c : ℝ) (hbc : b ≤ c) (z : ℂ) (t : ℝ) :
    𝓕 ((Set.Ico b c).indicator (fun _ : ℝ => z)) t =
      (∫ x in b..c, Complex.exp ((-2 * Real.pi * t * Complex.I) * x)) * z := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have he (x : ℝ) : Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) =
      Complex.exp ((-2 * Real.pi * t * Complex.I) * x) := by
    congr 1
    push_cast
    ring
  simp_rw [he]
  have hind : (fun x : ℝ => Complex.exp ((-2 * Real.pi * t * Complex.I) * x) *
      (Set.Ico b c).indicator (fun _ => z) x) =
      (Set.Ico b c).indicator
        (fun x => Complex.exp ((-2 * Real.pi * t * Complex.I) * x) * z) := by
    funext x
    by_cases hx : x ∈ Set.Ico b c <;> simp [Set.indicator, hx]
  rw [hind]
  rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hbc, intervalIntegral.integral_mul_const]

/-- Bounded interval windows belong to every Lp space (real centres). -/
private theorem wf_win_memLp (s : Finset ℕ) (b : ℕ → ℂ) (freq : ℕ → ℝ) (h : ℝ) (p : ℝ≥0∞) :
    MemLp (fun x : ℝ => ∑ n ∈ s,
      (Set.Ico (freq n - h) (freq n)).indicator (fun _ => b n) x) p := by
  apply memLp_finsetSum
  intro n hn
  exact memLp_indicator_const p measurableSet_Ico.nullMeasurableSet (b n) (Or.inr (by simp))

/-- The real-centred window is integrable. -/
private theorem wf_win_integrable (s : Finset ℕ) (b : ℕ → ℂ) (freq : ℕ → ℝ) (h : ℝ) :
    Integrable (fun x : ℝ => ∑ n ∈ s,
      (Set.Ico (freq n - h) (freq n)).indicator (fun _ => b n) x) :=
  memLp_one_iff_integrable.mp (wf_win_memLp s b freq h 1)

/-- The real-centred window Fourier integral factors as an exponential sum and a common kernel. -/
private theorem wf_fourier_window (s : Finset ℕ) (b : ℕ → ℂ) (freq : ℕ → ℝ) {h : ℝ}
    (hh : 0 ≤ h) {t : ℝ} (ht : t ≠ 0) :
    𝓕 (fun x : ℝ => ∑ n ∈ s,
        (Set.Ico (freq n - h) (freq n)).indicator (fun _ => b n) x) t =
      ((1 - Complex.exp ((2 * Real.pi * t * h : ℝ) * Complex.I)) /
        (-2 * Real.pi * t * Complex.I)) *
      ∑ n ∈ s, b n * Complex.exp ((-2 * Real.pi * t * Complex.I) * (freq n)) := by
  let c : ℂ := -2 * Real.pi * t * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) (by exact_mod_cast ht)) Complex.I_ne_zero
  have hi (n : ℕ) : Integrable ((Set.Ico (freq n - h) (freq n)).indicator
      (fun _ => b n)) :=
    memLp_one_iff_integrable.mp (memLp_indicator_const 1 measurableSet_Ico.nullMeasurableSet
      (b n) (Or.inr (by simp)))
  have hsum : 𝓕 (fun x : ℝ => ∑ n ∈ s,
      (Set.Ico (freq n - h) (freq n)).indicator (fun _ => b n) x) t =
      ∑ n ∈ s, 𝓕 ((Set.Ico (freq n - h) (freq n)).indicator (fun _ => b n)) t := by
    rw [Real.fourier_eq]
    simp only [Finset.smul_sum]
    rw [integral_finsetSum]
    · rfl
    · intro n hn
      exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
        (L := innerₗ ℝ) (by fun_prop) t).2 (hi n)
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [wf_fourier_interval _ _ (by linarith) (b n) t]
  change (∫ x in freq n - h..freq n, Complex.exp (c * x)) * b n = _
  rw [integral_exp_mul_complex hc]
  have he : c * ((freq n - h : ℝ) : ℂ) = c * ((freq n : ℝ) : ℂ) + (-c * (h : ℂ)) := by
    push_cast
    ring
  have he' : -c * (h : ℂ) = ((2 * Real.pi * t * h : ℝ) : ℂ) * Complex.I := by
    dsimp [c]
    push_cast
    ring
  rw [he, Complex.exp_add, he']
  dsimp [c]
  ring

/-- The absolute size of the common interval Fourier kernel. -/
private theorem wf_kernel_norm (h t : ℝ) :
    ‖(1 - Complex.exp ((2 * Real.pi * t * h : ℝ) * Complex.I)) /
      (-2 * Real.pi * t * Complex.I)‖ =
      |Real.sin (Real.pi * t * h)| / (Real.pi * |t|) := by
  rw [norm_div, norm_sub_rev]
  have he : ((2 * Real.pi * t * h : ℝ) : ℂ) * Complex.I =
      Complex.I * ((2 * Real.pi * t * h : ℝ) : ℂ) := mul_comm _ _
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have ha : 2 * Real.pi * t * h / 2 = Real.pi * t * h := by ring
  rw [ha]
  simp only [Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
  norm_num
  ring

/-- Jordan's sine bound gives the required lower bound for the window kernel. -/
private theorem wf_kernel_lower {T t : ℝ} (hT : 0 < T) (ht : t ≠ 0) (hbound : |t| ≤ T) :
    1 / (Real.pi * T) ≤
      ‖(1 - Complex.exp ((2 * Real.pi * t * (1 / (2 * T)) : ℝ) * Complex.I)) /
        (-2 * Real.pi * t * Complex.I)‖ := by
  rw [wf_kernel_norm]
  have hp : 0 < Real.pi := Real.pi_pos
  have hta : 0 < |t| := abs_pos.mpr ht
  have harg : |Real.pi * t * (1 / (2 * T))| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_pos (by positivity : 0 < 1 / (2 * T))]
    calc Real.pi * |t| * (1 / (2 * T)) ≤ Real.pi * T * (1 / (2 * T)) := by gcongr
         _ = Real.pi / 2 := by field_simp
  have hs := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_mul, abs_of_pos hp,
    abs_of_pos (by positivity : 0 < 1 / (2 * T))] at hs
  apply (le_div_iff₀ (mul_pos hp hta)).mpr
  calc (1 / (Real.pi * T)) * (Real.pi * |t|) =
      2 / Real.pi * (Real.pi * |t| * (1 / (2 * T))) := by field_simp
       _ ≤ _ := hs

/-- Gallagher's bound for a real-frequency exponential sum. -/
private theorem wf_window_bound (s : Finset ℕ) (b : ℕ → ℂ) (freq : ℕ → ℝ) {T : ℝ}
    (hT : 0 < T) :
    ∫ t in (-T)..T, ‖∑ n ∈ s, b n *
      Complex.exp ((-2 * Real.pi * t * Complex.I) * (freq n))‖ ^ 2 ≤
      Real.pi ^ 2 * T ^ 2 * ∫ x : ℝ, ‖∑ n ∈ s,
        (Set.Ico (freq n - 1 / (2 * T)) (freq n)).indicator (fun _ => b n) x‖ ^ 2 := by
  let C : ℝ → ℂ := fun x => ∑ n ∈ s,
    (Set.Ico (freq n - 1 / (2 * T)) (freq n)).indicator (fun _ => b n) x
  let P : ℝ → ℂ := fun t => ∑ n ∈ s, b n *
    Complex.exp ((-2 * Real.pi * t * Complex.I) * (freq n))
  have hC₁ : Integrable C := wf_win_integrable s b freq _
  have hC₂ : MemLp C 2 := wf_win_memLp s b freq _ 2
  have hF := p_fourierIntegral_memLp C hC₁ hC₂
  have hFs : Integrable (fun t => ‖𝓕 C t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hPc : Continuous P := by dsimp [P]; fun_prop
  have hFc : Continuous (𝓕 C) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hC₁
  have hpoint : ∀ᵐ t : ℝ, t ∈ Set.Icc (-T) T →
      ‖P t‖ ^ 2 ≤ Real.pi ^ 2 * T ^ 2 * ‖𝓕 C t‖ ^ 2 := by
    filter_upwards [show ∀ᵐ t : ℝ, t ≠ 0 from by
      rw [ae_iff]
      simp] with t ht htI
    have hb : |t| ≤ T := abs_le.mpr ⟨htI.1, htI.2⟩
    have hk := wf_kernel_lower hT ht hb
    have hw := wf_fourier_window s b freq (by positivity : 0 ≤ 1 / (2 * T)) ht
    change 𝓕 C t = _ at hw
    have hnorm := congrArg norm hw
    rw [norm_mul] at hnorm
    have hq : ‖P t‖ ≤ (Real.pi * T) * ‖𝓕 C t‖ := by
      have hh := mul_le_mul_of_nonneg_right hk (norm_nonneg (P t))
      change 1 / (Real.pi * T) * ‖P t‖ ≤ _ at hh
      rw [← hnorm] at hh
      have hpT : 0 < Real.pi * T := mul_pos Real.pi_pos hT
      have hh' : ‖P t‖ / (Real.pi * T) ≤ ‖𝓕 C t‖ := by
        simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hh
      simpa only [mul_comm] using (div_le_iff₀ hpT).mp hh'
    nlinarith [norm_nonneg (P t), norm_nonneg (𝓕 C t), Real.pi_pos]
  have hint₂ : IntervalIntegrable (fun t : ℝ => ‖P t‖ ^ 2) volume (-T) T :=
    (hPc.norm.pow 2).intervalIntegrable _ _
  have hint₁ : IntervalIntegrable (fun t : ℝ => Real.pi ^ 2 * T ^ 2 * ‖𝓕 C t‖ ^ 2)
      volume (-T) T := ((hFc.norm.pow 2).const_mul _).intervalIntegrable _ _
  have hi := intervalIntegral.integral_mono_ae_restrict (by linarith : -T ≤ T)
    hint₂ hint₁ ((ae_restrict_iff' measurableSet_Icc).mpr hpoint)
  change (∫ t in (-T)..T, ‖P t‖ ^ 2) ≤ _
  calc
    _ ≤ ∫ t in (-T)..T, Real.pi ^ 2 * T ^ 2 * ‖𝓕 C t‖ ^ 2 := hi
    _ = Real.pi ^ 2 * T ^ 2 * ∫ t in (-T)..T, ‖𝓕 C t‖ ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ Real.pi ^ 2 * T ^ 2 * ∫ t : ℝ, ‖𝓕 C t‖ ^ 2 := by
      gcongr
      rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
      exact integral_mono_measure Measure.restrict_le_self
        (by filter_upwards with t; positivity) hFs
    _ = Real.pi ^ 2 * T ^ 2 * ∫ x : ℝ, ‖C x‖ ^ 2 := by
      rw [p_integral_norm_sq_fourier C hC₁ hC₂]

/-! ### Part 3: Gallagher's lemma for logarithmic frequencies -/

/-- Gallagher's smoothing lemma with the twist `n^{it}`: the `t`-integral is controlled by the
short-window energy of the coefficients at the frequencies `log n`. -/
private theorem gallagher_log (s : Finset ℕ) (b : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    ∫ t in (-T)..T, ‖∑ n ∈ s, b n * Complex.exp ((t * Real.log n : ℝ) * Complex.I)‖ ^ 2 ≤
      2 * Real.pi ^ 3 * T ^ 2 *
        ∫ x : ℝ, ‖∑ n ∈ s, (Set.Ico (Real.log n - 1 / (2 * T)) (Real.log n)).indicator
          (fun _ => b n) x‖ ^ 2 := by
  set C : ℝ → ℂ := fun x => ∑ n ∈ s,
    (Set.Ico (Real.log n - 1 / (2 * T)) (Real.log n)).indicator (fun _ => b n) x with hCdef
  set Q : ℝ → ℂ := fun u => ∑ n ∈ s,
    b n * Complex.exp ((-2 * Real.pi * u * Complex.I) * ((Real.log n : ℝ) : ℂ)) with hQdef
  have hQc : Continuous Q := by rw [hQdef]; fun_prop
  have hPfun : (fun t : ℝ => ∑ n ∈ s, b n * Complex.exp ((t * Real.log n : ℝ) * Complex.I))
      = fun t => Q (-(1 / (2 * Real.pi)) * t) := by
    funext t
    rw [hQdef]
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    push_cast
    field_simp
  have hPsum : ∀ t : ℝ,
      (∑ n ∈ s, b n * Complex.exp ((t * Real.log n : ℝ) * Complex.I))
        = Q (-(1 / (2 * Real.pi)) * t) := fun t => congrFun hPfun t
  rw [show (∫ t in (-T)..T,
        ‖∑ n ∈ s, b n * Complex.exp ((t * Real.log n : ℝ) * Complex.I)‖ ^ 2)
      = ∫ t in (-T)..T, ‖Q (-(1 / (2 * Real.pi)) * t)‖ ^ 2 from by
    apply intervalIntegral.integral_congr
    intro t ht
    show ‖∑ n ∈ s, b n * Complex.exp ((t * Real.log n : ℝ) * Complex.I)‖ ^ 2
      = ‖Q (-(1 / (2 * Real.pi)) * t)‖ ^ 2
    rw [hPsum t]]
  have hc0 : (-(1 / (2 * Real.pi)) : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (ne_of_gt (by positivity))
  have hkey : (∫ t in (-T)..T, ‖Q (-(1 / (2 * Real.pi)) * t)‖ ^ 2)
      = 2 * Real.pi * ∫ u in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)), ‖Q u‖ ^ 2 := by
    rw [intervalIntegral.integral_comp_mul_left (f := fun u => ‖Q u‖ ^ 2) hc0]
    have e1 : (-(1 / (2 * Real.pi))) * (-T) = T / (2 * Real.pi) := by field_simp
    have e2 : (-(1 / (2 * Real.pi))) * T = -(T / (2 * Real.pi)) := by field_simp
    have e3 : ((-(1 / (2 * Real.pi)))⁻¹ : ℝ) = -(2 * Real.pi) := by field_simp
    rw [e1, e2, e3, intervalIntegral.integral_symm]
    simp only [smul_neg, smul_eq_mul]
    ring
  rw [hkey]
  have hmono : (∫ u in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)), ‖Q u‖ ^ 2)
      ≤ ∫ u in (-T)..T, ‖Q u‖ ^ 2 := by
    set X : ℝ := T / (2 * Real.pi) with hX
    have hX0 : 0 ≤ X := by rw [hX]; positivity
    have hXT : X ≤ T := by
      rw [hX]
      exact div_le_self hT.le (by nlinarith [Real.pi_gt_three])
    have hX2 : X < T + 1 := by linarith
    apply intervalIntegral.integral_mono_interval
    · linarith
    · linarith
    · linarith
    · exact Filter.Eventually.of_forall (fun u => by positivity)
    · exact (hQc.norm.pow 2).intervalIntegrable _ _
  have hG := wf_window_bound s b (fun n => Real.log n) hT
  have h1 : (∫ u in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)), ‖Q u‖ ^ 2)
      ≤ Real.pi ^ 2 * T ^ 2 * ∫ x : ℝ, ‖C x‖ ^ 2 := hmono.trans hG
  calc 2 * Real.pi * ∫ u in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)), ‖Q u‖ ^ 2
      ≤ 2 * Real.pi * (Real.pi ^ 2 * T ^ 2 * ∫ x : ℝ, ‖C x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * Real.pi ^ 3 * T ^ 2 * ∫ x : ℝ, ‖C x‖ ^ 2 := by ring

/-! ### Part 4: the multiplicative large sieve for `ℕ`-indexed intervals -/

/-- Transport a sum over a `ℕ`-interval to the corresponding `ℤ`-interval. -/
private theorem sum_Ioc_int {α : Type*} [AddCommMonoid α] (f : ℕ → α) (M L : ℕ) :
    (∑ k ∈ Finset.Ioc (M : ℤ) ((M : ℤ) + L), f k.toNat)
      = ∑ n ∈ Finset.Ioc M (M + L), f n := by
  apply Finset.sum_nbij' (fun k : ℤ => k.toNat) (fun n : ℕ => (n : ℤ))
  · intro a ha
    simp only [Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Ioc] at ha
    omega
  · intro a ha
    simp
  · intro a ha
    simp

/-- `ℤ`-character values only see the natural representative. -/
private lemma char_int_eq {q : ℕ} (χ : DirichletCharacter ℂ q) {k : ℤ} (hk : 0 ≤ k) :
    χ k = χ ((k.toNat : ℕ) : ZMod q) := by
  have hkz : (k : ZMod q) = ((k.toNat : ℕ) : ZMod q) := by
    conv_lhs => rw [← Int.toNat_of_nonneg hk]
    push_cast
    rfl
  rw [hkz]

/-- The multiplicative large sieve, `ℕ`-indexed with the `(L + 2Q²)` weight. -/
private theorem mul_sieve_nat (Q : ℕ) (hQ : 1 ≤ Q) (c : ℕ → ℂ) (M L : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + L), c n * χ (n : ZMod q)‖ ^ 2
      ≤ ((L : ℝ) + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + L), ‖c n‖ ^ 2 := by
  classical
  have hmain := LeanLab.PNTPort.LargeSieve.multiplicative_large_sieve (Q := Q) hQ (fun k : ℤ => c k.toNat) (M : ℤ) L
  have hchi : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      (∑ k ∈ Finset.Ioc (M : ℤ) ((M : ℤ) + L), (fun k : ℤ => c k.toNat) k * χ k)
        = ∑ n ∈ Finset.Ioc M (M + L), c n * χ (n : ZMod q) := by
    intro q χ
    rw [show (∑ k ∈ Finset.Ioc (M : ℤ) ((M : ℤ) + L),
          (fun k : ℤ => c k.toNat) k * χ k)
        = ∑ k ∈ Finset.Ioc (M : ℤ) ((M : ℤ) + L), c k.toNat * χ ((k.toNat : ℕ) : ZMod q) from by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_Ioc] at hk
      have hk0 : (0 : ℤ) ≤ k := by omega
      rw [char_int_eq (q := q) χ (k := k) hk0]]
    exact sum_Ioc_int (fun n => c n * χ (n : ZMod q)) M L
  have hnorm : (∑ k ∈ Finset.Ioc (M : ℤ) ((M : ℤ) + L), ‖(fun k : ℤ => c k.toNat) k‖ ^ 2)
      = ∑ n ∈ Finset.Ioc M (M + L), ‖c n‖ ^ 2 := by
    simpa only using sum_Ioc_int (fun n => ‖c n‖ ^ 2) M L
  have heq1 : (∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / ((k + 1).totient : ℝ) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter
            (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc (M : ℤ) ((M : ℤ) + L), (fun k : ℤ => c k.toNat) n * χ n‖ ^ 2)
      = ∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / ((k + 1).totient : ℝ) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter
            (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + L), c n * χ (n : ZMod (k + 1))‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_congr rfl (fun χ hχ => by rw [hchi])]
  rw [heq1, hnorm] at hmain
  -- reindex `range Q` as `Icc 1 Q`
  have himg : (Finset.range Q).image (fun k => k + 1) = Finset.Icc 1 Q := by
    ext q
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨k, hk, rfl⟩
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨q - 1, by omega, by omega⟩
  have hreindex : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + L), c n * χ (n : ZMod q)‖ ^ 2)
      = ∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / ((k + 1).totient : ℝ) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter
            (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + L), c n * χ (n : ZMod (k + 1))‖ ^ 2 := by
    rw [← himg]
    exact Finset.sum_image (f := fun q : ℕ => ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + L), c n * χ (n : ZMod q)‖ ^ 2)
      (g := fun k => k + 1) (by
        intro x hx y hy hxy
        have h2 : x + 1 = y + 1 := hxy
        omega)
  rw [← hreindex] at hmain
  exact hmain

/-! ### Part 5: windows as filters and the per-point sieve -/

/-- The indicator window sum is the filter sum, for coefficients in any additive monoid. -/
private lemma ind_sum_eq_filter {α : Type*} [AddCommMonoid α] (s : Finset ℕ) (b : ℕ → α)
    (freq : ℕ → ℝ) (h x : ℝ) :
    (∑ n ∈ s, (Set.Ico (freq n - h) (freq n)).indicator (fun _ => b n) x)
      = ∑ n ∈ s.filter (fun n => x < freq n ∧ freq n ≤ x + h), b n := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hx : freq n - h ≤ x ∧ x < freq n
  · have hx' : x < freq n ∧ freq n ≤ x + h := ⟨hx.2, by linarith [hx.1]⟩
    simp only [Set.indicator, Set.mem_Ico, if_pos hx, if_pos hx']
  · have hx' : ¬ (x < freq n ∧ freq n ≤ x + h) := by
      intro hh
      exact hx ⟨by linarith [hh.2], hh.1⟩
    simp only [Set.indicator, Set.mem_Ico, if_neg hx, if_neg hx']

/-- A subset of an integer interval inherits the multiplicative large sieve. -/
private theorem mul_sieve_subset (Q : ℕ) (hQ : 1 ≤ Q) (c : ℕ → ℂ) (M L : ℕ)
    (s : Finset ℕ) (hs : s ⊆ Finset.Ioc M (M + L)) :
    ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) / (q.totient : ℝ) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ s, c n * χ (n : ZMod q)‖ ^ 2
      ≤ ((L : ℝ) + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ s, ‖c n‖ ^ 2 := by
  classical
  set b : ℕ → ℂ := fun n => if n ∈ s then c n else 0 with hb
  have hset : (Finset.Ioc M (M + L)).filter (fun n => n ∈ s) = s := by
    ext n
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hn => hs hn)
  have hsum : ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q,
      (∑ n ∈ Finset.Ioc M (M + L), b n * χ (n : ZMod q))
        = ∑ n ∈ s, c n * χ (n : ZMod q) := by
    intro q χ
    simp only [hb, ite_mul, zero_mul, ← Finset.sum_filter, hset]
  have henergy : (∑ n ∈ Finset.Ioc M (M + L), ‖b n‖ ^ 2) = ∑ n ∈ s, ‖c n‖ ^ 2 := by
    simp only [hb, apply_ite norm, norm_zero, ite_pow, zero_pow (by norm_num : 2 ≠ 0),
      ← Finset.sum_filter, hset]
  have h := mul_sieve_nat Q hQ b M L
  have heq : (∑ q ∈ Finset.Icc 1 Q, (q : ℝ) / (q.totient : ℝ) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + L), b n * χ (n : ZMod q)‖ ^ 2)
      = ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) / (q.totient : ℝ) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ s, c n * χ (n : ZMod q)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_congr rfl (fun χ hχ => by rw [hsum q χ])]
  rw [heq, henergy] at h
  exact h

/-- The per-point window sieve at one `x`. -/
private lemma per_x_bound (Q : ℕ) (hQ : 1 ≤ Q) (a : ℕ → ℂ) (M N : ℕ) {hh x : ℝ}
    (hhpos : 0 < hh) :
    ∑ q ∈ Finset.Icc 1 Q,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ (Finset.Ioc M (M + N)).filter
            (fun n : ℕ => x < Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ x + hh), a n * χ (n : ZMod q)‖ ^ 2
      ≤ (((⌊Real.exp (x + hh)⌋₊ - ⌊Real.exp x⌋₊ : ℕ) : ℝ) + 2 * (Q : ℝ) ^ 2) *
        ∑ n ∈ (Finset.Ioc M (M + N)).filter
            (fun n : ℕ => x < Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ x + hh), ‖a n‖ ^ 2 := by
  classical
  set W : Finset ℕ := (Finset.Ioc M (M + N)).filter
    (fun n : ℕ => x < Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ x + hh) with hW
  have hAB : ⌊Real.exp x⌋₊ ≤ ⌊Real.exp (x + hh)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))
  have hsub : W ⊆ Finset.Ioc ⌊Real.exp x⌋₊
      (⌊Real.exp x⌋₊ + (⌊Real.exp (x + hh)⌋₊ - ⌊Real.exp x⌋₊)) := by
    intro n hn
    simp only [hW, Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    obtain ⟨⟨hM, hN⟩, h1, h2⟩ := hn
    have hn1 : 1 ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlt : Real.exp x < (n : ℝ) := (Real.lt_log_iff_exp_lt hnpos).mp h1
    have hle : (n : ℝ) ≤ Real.exp (x + hh) := (Real.log_le_iff_le_exp hnpos).mp h2
    rw [Nat.add_sub_of_le hAB]
    exact ⟨(Nat.floor_lt (Real.exp_pos x).le).mpr hlt, Nat.le_floor hle⟩
  have hsl := mul_sieve_subset Q hQ a ⌊Real.exp x⌋₊
    (⌊Real.exp (x + hh)⌋₊ - ⌊Real.exp x⌋₊) W hsub
  refine (Finset.sum_le_sum (fun q hq => ?_)).trans hsl
  have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
  have hφ0 : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq0
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hw : (1 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) := (le_div_iff₀ hφ0).mpr (by simpa using hφq)
  exact le_mul_of_one_le_left
    (Finset.sum_nonneg (fun _ _ => by positivity)) hw

/-- The count of integers in one logarithmic window is at most `(M+N)/(2T) + 1`. -/
private lemma card_window_le (M N : ℕ) {hh x : ℝ}
    (hWn : (Finset.Ioc M (M + N)).filter
      (fun n : ℕ => x < Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ x + hh) ≠ ∅)
    (hhpos : 0 < hh) (hh1 : hh ≤ 1) :
    ((⌊Real.exp (x + hh)⌋₊ - ⌊Real.exp x⌋₊ : ℕ) : ℝ) ≤ (M + N : ℝ) * (2 * hh) + 1 := by
  obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.mpr hWn
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hlt : Real.exp x < (n : ℝ) := (Real.lt_log_iff_exp_lt hnpos).mp hn.2.1
  have hleN : (n : ℝ) ≤ (M + N : ℝ) := by
    have : n ≤ M + N := hn.1.2
    exact_mod_cast this
  have hexp : Real.exp x < (M + N : ℝ) := lt_of_lt_of_le hlt hleN
  have hAB : ⌊Real.exp x⌋₊ ≤ ⌊Real.exp (x + hh)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))
  have hfl : ((⌊Real.exp (x + hh)⌋₊ - ⌊Real.exp x⌋₊ : ℕ) : ℝ)
      ≤ Real.exp (x + hh) - Real.exp x + 1 := by
    rw [Nat.cast_sub hAB]
    have h1 : ((⌊Real.exp (x + hh)⌋₊ : ℕ) : ℝ) ≤ Real.exp (x + hh) :=
      Nat.floor_le (Real.exp_pos (x + hh)).le
    have h2 : Real.exp x < ((⌊Real.exp x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hfac : Real.exp (x + hh) - Real.exp x = Real.exp x * (Real.exp hh - 1) := by
    rw [Real.exp_add]
    ring
  have hexp1 : Real.exp hh - 1 ≤ 2 * hh := by
    have hb := Real.abs_exp_sub_one_sub_id_le (x := hh) (by rw [abs_of_pos hhpos]; linarith)
    have hb' : Real.exp hh - 1 - hh ≤ hh ^ 2 := (le_abs_self _).trans hb
    nlinarith [hhpos, sq_nonneg hh]
  have hNN : (0 : ℝ) ≤ (M + N : ℝ) := by positivity
  calc ((⌊Real.exp (x + hh)⌋₊ - ⌊Real.exp x⌋₊ : ℕ) : ℝ)
      ≤ Real.exp (x + hh) - Real.exp x + 1 := hfl
    _ = Real.exp x * (Real.exp hh - 1) + 1 := by rw [hfac]
    _ ≤ (M + N : ℝ) * (2 * hh) + 1 := by
        have h1 : Real.exp x * (Real.exp hh - 1) ≤ (M + N : ℝ) * (2 * hh) := by
          have h2 : (0 : ℝ) ≤ Real.exp hh - 1 := by linarith [Real.add_one_le_exp hh]
          nlinarith [hexp.le, hNN]
        linarith

/-! ### Part 6: the hybrid large sieve -/

/-- **Gallagher's hybrid large sieve** (Gallagher 1970, Theorem 2; Montgomery, Topics, Theorem 6.4),
with the coefficient `M + N + Q²T` of the shifted support. -/
theorem hybrid_large_sieve_proved : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ (M N : ℕ) (a : ℕ → ℂ),
      ∑ q ∈ Finset.Icc 1 Q, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        ∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          a n * χ (n : ZMod q) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
      C * ((M + N : ℕ) + (Q : ℝ) ^ 2 * T) *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2 := by
  refine ⟨4 * Real.pi ^ 3, by positivity, ?_⟩
  intro Q hQ T hT M N a
  classical
  have hTpos : 0 < T := by linarith
  set hh : ℝ := 1 / (2 * T) with hhh
  have hhpos : 0 < hh := by rw [hhh]; positivity
  have hh1 : hh ≤ 1 := by
    rw [hhh, div_le_one (by positivity)]
    linarith
  have hhalf : 2 * hh = 1 / T := by rw [hhh]; field_simp
  set K : ℝ := ((M + N : ℝ) / T + 1 + 2 * (Q : ℝ) ^ 2) with hKdef
  have hIcc : (Finset.Icc (M + 1) (M + N) : Finset ℕ) = Finset.Ioc M (M + N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  -- the exponential twist
  have hcpow : ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ,
      (n : ℂ) ^ ((t : ℂ) * Complex.I)
        = Complex.exp ((t * Real.log (n : ℝ) : ℝ) * Complex.I) := by
    intro n hn1 t
    have hn0 : (n : ℂ) ≠ 0 := by
      have : n ≠ 0 := by omega
      exact_mod_cast this
    rw [Complex.cpow_def_of_ne_zero hn0]
    have hlog : Complex.log (↑n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
      simpa using (Complex.ofReal_log (x := (n : ℝ)) (by positivity : (0 : ℝ) ≤ (n : ℝ))).symm
    rw [hlog]
    congr 1
    push_cast
    ring
  -- per character Gallagher
  have hgal : ∀ (q : ℕ), q ∈ Finset.Icc 1 Q → ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-T)..T, ‖∑ n ∈ Finset.Ioc M (M + N),
          a n * χ (n : ZMod q) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2)
        ≤ 2 * Real.pi ^ 3 * T ^ 2 *
          ∫ x : ℝ, ‖∑ n ∈ Finset.Ioc M (M + N),
            (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
              (fun _ => a n * χ (n : ZMod q)) x‖ ^ 2 := by
    intro q hq χ
    have hsum : ∀ t : ℝ, (∑ n ∈ Finset.Ioc M (M + N),
          a n * χ (n : ZMod q) * (n : ℂ) ^ ((t : ℂ) * Complex.I))
        = ∑ n ∈ Finset.Ioc M (M + N),
          (a n * χ (n : ZMod q)) * Complex.exp ((t * Real.log (n : ℝ) : ℝ) * Complex.I) := by
      intro t
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Finset.mem_Ioc] at hn
      rw [hcpow n (by omega) t, mul_assoc]
    calc (∫ t in (-T)..T, ‖∑ n ∈ Finset.Ioc M (M + N),
            a n * χ (n : ZMod q) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2)
        = ∫ t in (-T)..T, ‖∑ n ∈ Finset.Ioc M (M + N),
            (a n * χ (n : ZMod q)) *
              Complex.exp ((t * Real.log (n : ℝ) : ℝ) * Complex.I)‖ ^ 2 := by
          apply intervalIntegral.integral_congr
          intro t ht
          show ‖∑ n ∈ Finset.Ioc M (M + N),
              a n * χ (n : ZMod q) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 = _
          rw [hsum t]
      _ ≤ _ := gallagher_log (Finset.Ioc M (M + N))
          (fun n => a n * χ (n : ZMod q)) hTpos
  -- integrability of the window energy, one character at a time
  have hIntχ : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      Integrable (fun x : ℝ => ‖∑ n ∈ Finset.Ioc M (M + N),
        (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
          (fun _ => a n * χ (n : ZMod q)) x‖ ^ 2) := by
    intro q χ
    have hm := wf_win_memLp (Finset.Ioc M (M + N)) (fun n => a n * χ (n : ZMod q))
      (fun n => Real.log (n : ℝ)) hh 2
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  -- the pointwise comparison after integrating
  have hIntL : Integrable (fun x : ℝ => ∑ q ∈ Finset.Icc 1 Q,
      ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        ‖∑ n ∈ Finset.Ioc M (M + N),
          (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
            (fun _ => a n * χ (n : ZMod q)) x‖ ^ 2) := by
    apply integrable_finsetSum
    intro q hq
    apply integrable_finsetSum
    intro χ hχ
    exact hIntχ q χ
  have hIntR : Integrable (fun x : ℝ => K * ∑ n ∈ Finset.Ioc M (M + N),
      (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
        (fun _ => ‖a n‖ ^ 2) x) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro n hn
    exact ((continuous_const.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self)
      |>.integrable_indicator measurableSet_Ico
  have hxint : (∫ x : ℝ, ∑ q ∈ Finset.Icc 1 Q,
        ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
          ‖∑ n ∈ Finset.Ioc M (M + N),
            (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
              (fun _ => a n * χ (n : ZMod q)) x‖ ^ 2)
      ≤ ∫ x : ℝ, K * ∑ n ∈ Finset.Ioc M (M + N),
          (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
            (fun _ => ‖a n‖ ^ 2) x := by
    apply integral_mono_ae hIntL hIntR
    filter_upwards with x
    have hpt : (∑ q ∈ Finset.Icc 1 Q, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
          ‖∑ n ∈ Finset.Ioc M (M + N),
            (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
              (fun _ => a n * χ (n : ZMod q)) x‖ ^ 2)
        = ∑ q ∈ Finset.Icc 1 Q, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
            ‖∑ n ∈ (Finset.Ioc M (M + N)).filter
              (fun n : ℕ => x < Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ x + hh),
              a n * χ (n : ZMod q)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [ind_sum_eq_filter]
    rw [hpt]
    have hrhs : K * ∑ n ∈ Finset.Ioc M (M + N),
        (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
          (fun _ => ‖a n‖ ^ 2) x
        = K * ∑ n ∈ (Finset.Ioc M (M + N)).filter
            (fun n : ℕ => x < Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ x + hh),
            ‖a n‖ ^ 2 := by
      rw [ind_sum_eq_filter]
    rw [hrhs]
    by_cases hW : ((Finset.Ioc M (M + N)).filter
        (fun n : ℕ => x < Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ x + hh)) = ∅
    · rw [hW]
      simp
    · have hpx := per_x_bound Q hQ a M N (x := x) hhpos
      have hcard := card_window_le M N hW hhpos hh1
      have hcard' : ((⌊Real.exp (x + hh)⌋₊ - ⌊Real.exp x⌋₊ : ℕ) : ℝ) + 2 * (Q : ℝ) ^ 2
          ≤ K := by
        rw [hKdef]
        have h2 : ((M + N : ℝ) * (2 * hh) + 1) = (M + N : ℝ) / T + 1 := by
          rw [hhalf]
          ring
        linarith
      refine hpx.trans ?_
      exact mul_le_mul_of_nonneg_right hcard'
        (Finset.sum_nonneg (fun n hn => by positivity))
  -- the mass of one window
  have hmass : (∫ x : ℝ, ∑ n ∈ Finset.Ioc M (M + N),
      (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
        (fun _ => ‖a n‖ ^ 2) x) = hh * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
    rw [integral_finsetSum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [integral_indicator_const (‖a n‖ ^ 2) measurableSet_Ico, Real.volume_real_Ico,
        max_eq_left (by linarith : (0 : ℝ) ≤ Real.log (n : ℝ) - (Real.log (n : ℝ) - hh)),
        smul_eq_mul]
      ring
    · intro n hn
      exact ((continuous_const.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self)
        |>.integrable_indicator measurableSet_Ico
  -- assembling
  rw [hIcc]
  have hswap : (∑ q ∈ Finset.Icc 1 Q, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        ∫ x : ℝ, ‖∑ n ∈ Finset.Ioc M (M + N),
          (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
            (fun _ => a n * χ (n : ZMod q)) x‖ ^ 2)
      = ∫ x : ℝ, ∑ q ∈ Finset.Icc 1 Q, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
          ‖∑ n ∈ Finset.Ioc M (M + N),
            (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
              (fun _ => a n * χ (n : ZMod q)) x‖ ^ 2 := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q hq
      rw [integral_finsetSum]
      intro χ hχ
      exact hIntχ q χ
    · intro q hq
      apply integrable_finsetSum
      intro χ hχ
      exact hIntχ q χ
  have hmassK : (∫ x : ℝ, K * ∑ n ∈ Finset.Ioc M (M + N),
      (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
        (fun _ => ‖a n‖ ^ 2) x)
      = K * (hh * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2) := by
    rw [integral_const_mul, hmass]
  calc ∑ q ∈ Finset.Icc 1 Q, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        ∫ t in (-T)..T, ‖∑ n ∈ Finset.Ioc M (M + N),
          a n * χ (n : ZMod q) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2
      ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
          2 * Real.pi ^ 3 * T ^ 2 *
            ∫ x : ℝ, ‖∑ n ∈ Finset.Ioc M (M + N),
              (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
                (fun _ => a n * χ (n : ZMod q)) x‖ ^ 2 :=
        Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun χ hχ => hgal q hq χ))
    _ = 2 * Real.pi ^ 3 * T ^ 2 *
          ∑ q ∈ Finset.Icc 1 Q, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
            ∫ x : ℝ, ‖∑ n ∈ Finset.Ioc M (M + N),
              (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
                (fun _ => a n * χ (n : ZMod q)) x‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.mul_sum]
    _ = 2 * Real.pi ^ 3 * T ^ 2 * ∫ x : ℝ, ∑ q ∈ Finset.Icc 1 Q,
          ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
            ‖∑ n ∈ Finset.Ioc M (M + N),
              (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
                (fun _ => a n * χ (n : ZMod q)) x‖ ^ 2 := by
        rw [hswap]
    _ ≤ 2 * Real.pi ^ 3 * T ^ 2 * ∫ x : ℝ, K * ∑ n ∈ Finset.Ioc M (M + N),
          (Set.Ico (Real.log (n : ℝ) - hh) (Real.log (n : ℝ))).indicator
            (fun _ => ‖a n‖ ^ 2) x := by
        apply mul_le_mul_of_nonneg_left hxint (by positivity)
    _ = 2 * Real.pi ^ 3 * T ^ 2 * (K * (hh * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2)) := by
        rw [hmassK]
    _ ≤ 4 * Real.pi ^ 3 * ((M + N : ℕ) + (Q : ℝ) ^ 2 * T) *
          ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
        have hS : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 :=
          Finset.sum_nonneg (fun n hn => by positivity)
        have hA0 : (0 : ℝ) ≤ (M + N : ℝ) := by positivity
        have hQT : T ≤ (Q : ℝ) ^ 2 * T := by
          have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
          have hQ2 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
          calc T = 1 * T := by ring
            _ ≤ (Q : ℝ) ^ 2 * T := by gcongr
        have hchain : 2 * Real.pi ^ 3 * T ^ 2 * (K * (hh * ∑ n ∈ Finset.Ioc M (M + N),
            ‖a n‖ ^ 2))
            = (Real.pi ^ 3 * (M + N : ℝ) + Real.pi ^ 3 * T
                + 2 * Real.pi ^ 3 * (Q : ℝ) ^ 2 * T)
              * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
          rw [hKdef, hhh]
          field_simp
        rw [hchain]
        push_cast
        have hA0' : (0 : ℝ) ≤ (M : ℝ) + (N : ℝ) := by positivity
        have hfin : Real.pi ^ 3 * ((M : ℝ) + (N : ℝ)) + Real.pi ^ 3 * T
            + 2 * Real.pi ^ 3 * (Q : ℝ) ^ 2 * T
            ≤ 4 * Real.pi ^ 3 * (((M : ℝ) + (N : ℝ)) + (Q : ℝ) ^ 2 * T) := by
          have hp3 : (0 : ℝ) < Real.pi ^ 3 := by positivity
          have hQ2T : (0 : ℝ) ≤ (Q : ℝ) ^ 2 * T := by positivity
          nlinarith [hp3, hQT, hQ2T, hA0']
        exact mul_le_mul_of_nonneg_right hfin hS

/-- LEAF. Gallagher's hybrid large sieve: there is `C > 0` with, for `Q ≥ 1`, `T ≥ 1`,
`Σ_{q ≤ Q} Σ*_{χ mod q} ∫_{-T}^{T} |Σ_{n=M+1}^{M+N} a_n χ(n) n^{it}|² dt ≤ C (N + Q²T) Σ |a_n|²`,
the inner sum over primitive `χ`. From the multiplicative large sieve (Decomp1524a
`mult_large_sieve`) and Gallagher's lemma (Decomp1524b `gallagher_lemma`).
Gallagher 1970 Theorem 2; Montgomery, Topics, Theorem 6.4. Unit U-1524.
DECISION U-1614: the factor is `M + N + Q²T`, the length up to the top of the support, not
`N + Q²T`. Gallagher's bound carries the weight `Q²T + n` on `|a_n|²`, Iwaniec-Kowalski Theorem 9.12
has `n ≤ N`, Montgomery-Vaughan 1975 p. 366 (7.1) is the case `Q = 1`. The old form with `N` alone
is false for `M` large, `HybridShiftBarrier.hybrid_large_sieve_not_valid`. -/
theorem hybrid_large_sieve : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ (M N : ℕ) (a : ℕ → ℂ),
      ∑ q ∈ Finset.Icc 1 Q, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        ∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          a n * χ (n : ZMod q) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
      C * ((M + N : ℕ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2 := by
  exact hybrid_large_sieve_proved

/-- LEAF. Zero detection, the mollified coefficient at `n = 1`:
`Σ_{d | 1, d ≤ X} μ(d) = 1` for `X ≥ 1`. Montgomery, Topics, Ch. 12; Gallagher 1970 section 4.
Unit U-1524. -/
theorem mollifier_coeff_one {X : ℝ} (hX : 1 ≤ X) :
    ∑ d ∈ (Nat.divisors 1).filter (fun d : ℕ => (d : ℝ) ≤ X),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) = 1 := by
  norm_num [Finset.filter_singleton, hX]

/-- LEAF. Zero detection: the coefficients of `L(s,χ) M_X(s,χ)`, `M_X = Σ_{d ≤ X} μ(d)χ(d)d^{-s}`,
vanish for `1 < n ≤ X`: `Σ_{d | n, d ≤ X} μ(d) = Σ_{d | n} μ(d) = 0`. Montgomery, Topics,
Ch. 12; Iwaniec-Kowalski Section 10.2. Unit U-1524. -/
theorem mollifier_coeff_vanish {n : ℕ} {X : ℝ} (hn : 1 < n) (hnX : (n : ℝ) ≤ X) :
    ∑ d ∈ (Nat.divisors n).filter (fun d : ℕ => (d : ℝ) ≤ X),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) = 0 := by
  have hf : (Nat.divisors n).filter (fun d : ℕ => (d : ℝ) ≤ X) = n.divisors := by
    apply Finset.filter_true_of_mem
    intro d hd
    have hdn := Nat.le_of_dvd (by omega : 0 < n) (Nat.mem_divisors.mp hd).1
    exact (show (d : ℝ) ≤ n by exact_mod_cast hdn).trans hnX
  rw [hf]
  have hm := congrArg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at hm
  have hn1 : n ≠ 1 := by omega
  simpa [hn1, ← Int.cast_sum] using congrArg (fun z : ℤ => (z : ℝ)) hm

/-- LEAF. Zero detection: `|Σ_{d | n, d ≤ X} μ(d)| ≤ d(n)` for all `n` and `X`. Montgomery,
Topics, Ch. 12; Iwaniec-Kowalski Section 10.2. Unit U-1524. -/
theorem mollifier_coeff_le (n : ℕ) (X : ℝ) :
    |∑ d ∈ (Nat.divisors n).filter (fun d : ℕ => (d : ℝ) ≤ X),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ (Nat.divisors n).card := by
  calc |∑ d ∈ (Nat.divisors n).filter (fun d : ℕ => (d : ℝ) ≤ X),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)|
      ≤ ∑ d ∈ (Nat.divisors n).filter (fun d : ℕ => (d : ℝ) ≤ X),
        |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ (Nat.divisors n).filter (fun d : ℕ => (d : ℝ) ≤ X), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    _ ≤ _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast Finset.card_filter_le _ _

/-- LEAF. Extracting well-spaced zeros: if every interval `[u, u+1]` holds at most `K` points of
a finite `Z ⊆ ℝ`, then some `Z' ⊆ Z` has pairwise gaps `≥ 1` and `#Z ≤ 2K #Z'` (one point per
occupied `[k, k+1)`, then keep the even or the odd `k`). Montgomery, Topics, Ch. 12;
Gallagher 1970 section 4. Unit U-1524. -/
theorem spaced_subfamily (Z : Finset ℝ) (K : ℕ)
    (hK : ∀ u : ℝ, (Z.filter (fun γ => γ ∈ Set.Icc u (u + 1))).card ≤ K) :
    ∃ Z' ⊆ Z, (∀ γ ∈ Z', ∀ γ' ∈ Z', γ ≠ γ' → 1 ≤ |γ - γ'|) ∧ Z.card ≤ 2 * K * Z'.card := by
  classical
  let F := Z.powerset.filter (fun s => ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (1:ℝ) ≤ |a-b|)
  have hF : F.Nonempty := by
    refine ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), ?_⟩⟩
    simp
  obtain ⟨S, hS, hmax⟩ := exists_max_image F card hF
  have hSZ : S ⊆ Z := mem_powerset.mp (mem_filter.mp hS).1
  have hsep := (mem_filter.mp hS).2
  have hcover : ∀ z ∈ Z, ∃ s ∈ S, |z-s| < 1 := by
    intro z hz
    by_contra hh
    push_neg at hh
    have hzS : z ∉ S := by
      intro hzs
      have := hh z hzs
      norm_num at this
    have hSF : insert z S ∈ F := by
      apply mem_filter.mpr
      refine ⟨mem_powerset.mpr (insert_subset hz hSZ), ?_⟩
      intro a ha b hb hab
      rcases mem_insert.mp ha with hza | haS
      · subst a
        rcases mem_insert.mp hb with hzb | hbS
        · exact (hab hzb.symm).elim
        · exact hh b hbS
      · rcases mem_insert.mp hb with hzb | hbS
        · subst b
          simpa [abs_sub_comm] using hh a haS
        · exact hsep a haS b hbS hab
    have hc := hmax (insert z S) hSF
    rw [card_insert_of_notMem hzS] at hc
    omega
  have hcount : ∀ s ∈ S, (Z.filter (fun z => |z-s| < 1)).card ≤ 2*K := by
    intro s hs
    have hsub : Z.filter (fun z => |z-s| < 1) ⊆
        Z.filter (fun z => z ∈ Set.Icc (s-1) s) ∪ Z.filter (fun z => z ∈ Set.Icc s (s+1)) := by
      intro z hz
      obtain ⟨hz, hab⟩ := mem_filter.mp hz
      have hab' := abs_lt.mp hab
      apply mem_union.mpr
      rcases le_total z s with h | h
      · exact Or.inl (mem_filter.mpr ⟨hz, by constructor <;> linarith⟩)
      · exact Or.inr (mem_filter.mpr ⟨hz, by constructor <;> linarith⟩)
    have hleft : (Z.filter (fun z => z ∈ Set.Icc (s-1) s)).card ≤ K := by
      simpa using hK (s-1)
    have hright := hK s
    exact (card_le_card hsub).trans ((card_union_le _ _).trans (by omega))
  refine ⟨S, hSZ, hsep, ?_⟩
  have hsub : Z ⊆ S.biUnion (fun s => Z.filter (fun z => |z-s|<1)) := by
    intro z hz
    obtain ⟨s, hs, hzs⟩ := hcover z hz
    exact mem_biUnion.mpr ⟨s, hs, mem_filter.mpr ⟨hz, hzs⟩⟩
  calc Z.card ≤ (S.biUnion (fun s => Z.filter (fun z => |z-s|<1))).card := card_le_card hsub
    _ ≤ ∑ s ∈ S, (Z.filter (fun z => |z-s|<1)).card := card_biUnion_le
    _ ≤ ∑ _s ∈ S, 2*K := sum_le_sum hcount
    _ = _ := by simp; ring

/-! ### Vacuity instances -/

/-- The hypotheses of `zero_sum_le` hold for a one-zero family: `β = 1/2`, `x = 4`, `Y = 2`,
`η = 1/2`, `σ₀ = 1/2`, `A = 1`. -/
example : ∀ α ∈ Set.Icc (1 / 2 : ℝ) 1,
    ((({0} : Finset ℕ).filter (fun _ => α ≤ (1 / 2 : ℝ))).card : ℝ) ≤ 1 * (2 : ℝ) ^ (1 - α) := by
  intro α hα
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (1 - α) := Real.one_le_rpow (by norm_num) (by linarith [hα.2])
  have h2 : ((({0} : Finset ℕ).filter (fun _ => α ≤ (1 / 2 : ℝ))).card : ℝ) ≤ 1 := by
    have : (({0} : Finset ℕ).filter (fun _ => α ≤ (1 / 2 : ℝ))).card ≤ 1 :=
      (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  linarith

/-- `2 ≤ √4`, the `Y ≤ √x` hypothesis of the instance above. -/
example : (2 : ℝ) ≤ Real.sqrt 4 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `spaced_subfamily`'s hypothesis is met by `Z = {0, 2}` with `K = 1`. -/
example : ∀ u : ℝ, (({0, 2} : Finset ℝ).filter (fun γ => γ ∈ Set.Icc u (u + 1))).card ≤ 1 := by
  intro u
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Set.mem_Icc] at ha hb
  rcases ha with ⟨rfl | rfl, h1, h2⟩ <;> rcases hb with ⟨rfl | rfl, h3, h4⟩ <;> linarith

end LeanLab.ExceptionalSet.Decomp1524c
