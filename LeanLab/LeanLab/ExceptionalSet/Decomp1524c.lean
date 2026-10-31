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

namespace LeanLab.ExceptionalSet.Decomp1524c

open Real MeasureTheory Finset

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

/-- LEAF. Gallagher's hybrid large sieve: there is `C > 0` with, for `Q ≥ 1`, `T ≥ 1`,
`Σ_{q ≤ Q} Σ*_{χ mod q} ∫_{-T}^{T} |Σ_{n=M+1}^{M+N} a_n χ(n) n^{it}|² dt ≤ C (N + Q²T) Σ |a_n|²`,
the inner sum over primitive `χ`. From the multiplicative large sieve (Decomp1524a
`mult_large_sieve`) and Gallagher's lemma (Decomp1524b `gallagher_lemma`).
Gallagher 1970 Theorem 2; Montgomery, Topics, Theorem 6.4. Unit U-1524. -/
theorem hybrid_large_sieve : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ (M N : ℕ) (a : ℕ → ℂ),
      ∑ q ∈ Finset.Icc 1 Q, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        ∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          a n * χ (n : ZMod q) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
      C * (N + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2 := by
  sorry

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
