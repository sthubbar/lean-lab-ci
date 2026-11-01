/-
AI-written Lean code, Claude, 2026-10-25, run 20261025T2003Z-426, unit U-1528, DECOMPOSE.
P0020 P. J. Campbell 2026, arXiv 2608.09488 v1, Section 4: Lemmas 4.2 and 4.3 use
Rosser-Schoenfeld 1962, Theorem 5 (Σ_{p ≤ x} 1/p, eqs 3.17, 3.18) and the Mertens product,
Theorem 7 (eq 3.25), p. 70; the lab carries these as the cited defs `RS1962.RS318`,
`RSHypFrom318.RS317`, `CampbellLemma42.RS325`, not restated here.
This file splits the ELEMENTARY explicit Mertens second and third theorems, derived from
Mertens' first theorem (`Decomp1528a.mertens1_abs`) by partial summation, into leaves.

Constants: error 4/log y for prime reciprocal block sums, error 4/log y + 1/(2⌊y⌋) for the
log of the product block. These are far weaker than RS (3.18) and (3.25), whose 1/(2 log² x)
error needs the zeta zero data behind RS Theorems 1 to 4; so they cannot replace RS325 in
Lemma 4.2, whose margin is 0.6 percent. Their use: unconditional explicit forms for the lab's
weaker inputs, and they sharpen `PNTSieve.Mertens.sum_inv_primes_le` (constant 12) and
`PNTSieve.mertens_product_ge` (e^{-16}), which are not restated.

Leaves: 12. Assemblies: `mertens2_block`, `mertens2_exists_B`, `sum_recip_le_explicit`,
`mertens3_block`, `mertens_prod_upper`; each CONDITIONAL only on leaves of this file and of
Decomp1528a.
Known mathematics. Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.Decomp1528a

open Real Finset Filter Topology

noncomputable section
namespace LeanLab.AlmostPrimes.Decomp1528b

/-! ### Partial summation -/

/-- LEAF. Abel summation for Σ 1/p: for real 2 ≤ y ≤ x, with A(t) = Σ_{p ≤ t} log p / p,
Σ_{y < p ≤ x} 1/p = A(x)/log x - A(y)/log y + ∫_y^x A(t)/(t log² t) dt.
Mathlib `sum_mul_eq_sub_integral_mul` with f(t) = 1/log t. Rosser-Schoenfeld 1962, Section 4,
p. 74 style; Montgomery-Vaughan I, Thm 2.7(d) proof. Unit U-1528. -/
theorem abel_recip {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    ∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p =
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p) / log x -
        (∑ p ∈ Nat.primesLE ⌊y⌋₊, log p / p) / log y +
        ∫ t in y..x, (∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p) / (t * log t ^ 2) := by
  have hy0 : 0 ≤ y := by linarith
  set c : ℕ → ℝ := fun k => if k.Prime then log k / k else 0 with hc
  set f : ℝ → ℝ := fun t => 1 / log t with hf
  have hfeq : f = fun s : ℝ => (log s)⁻¹ := by
    funext s; simp [f, one_div]
  have hderiv : ∀ t : ℝ, 2 ≤ t → deriv f t = -(1 / (t * log t ^ 2)) := by
    intro t ht2
    have ht0 : (0 : ℝ) < t := by linarith
    have hlog : log t ≠ 0 := (Real.log_pos (by linarith : (1 : ℝ) < t)).ne'
    rw [hfeq]
    have hd : HasDerivAt (fun s : ℝ => (log s)⁻¹) (-(t : ℝ)⁻¹ / log t ^ 2) t :=
      (Real.hasDerivAt_log ht0.ne').inv hlog
    rw [hd.deriv]
    have : (t : ℝ) ≠ 0 := ht0.ne'
    field_simp
  have hdiff : ∀ t ∈ Set.Icc y x, DifferentiableAt ℝ f t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    have hlog : log t ≠ 0 := (Real.log_pos (by linarith [ht.1] : (1 : ℝ) < t)).ne'
    rw [hfeq]
    exact (Real.differentiableAt_log ht0.ne').inv hlog
  have hint : MeasureTheory.IntegrableOn (deriv f) (Set.Icc y x) := by
    have hcont : ContinuousOn (fun t : ℝ => -(1 / (t * log t ^ 2))) (Set.Icc y x) := by
      apply ContinuousOn.neg
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · refine ContinuousOn.mul continuousOn_id (ContinuousOn.pow ?_ 2)
        exact ContinuousOn.log continuousOn_id (fun t ht => by
          have h2 : 2 ≤ t := le_trans hy ht.1
          positivity)
      · intro t ht
        have h2 : 2 ≤ t := le_trans hy ht.1
        have hp : 0 < log t := Real.log_pos (by linarith)
        have : (0 : ℝ) < t := by linarith
        positivity
    refine (hcont.integrableOn_compact isCompact_Icc).congr_fun ?_ measurableSet_Icc
    intro t ht
    exact (hderiv t (le_trans hy ht.1)).symm
  have hA : ∀ t : ℝ, ∑ k ∈ Icc 0 ⌊t⌋₊, c k = ∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p := by
    intro t
    rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  have hL : ∑ k ∈ Ioc ⌊y⌋₊ ⌊x⌋₊, f k * c k =
      ∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
    rw [sum_filter]
    refine sum_congr rfl fun k hk => ?_
    by_cases hk' : k.Prime
    · have hk2 : (2 : ℝ) ≤ (k : ℝ) := by
        have : 2 ≤ k := hk'.two_le
        exact_mod_cast this
      have hlog : log (k : ℝ) ≠ 0 := (Real.log_pos (by linarith)).ne'
      have hk0 : (k : ℝ) ≠ 0 := by linarith
      simp only [f, c, hk', ite_true]
      field_simp
    · simp [f, c, hk']
  have hI : ∫ t in Set.Ioc y x, deriv f t * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) =
      -∫ t in y..x, (∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p) / (t * log t ^ 2) := by
    rw [intervalIntegral.integral_of_le hyx, ← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have h2 : 2 ≤ t := le_trans hy ht.1.le
    simp only
    rw [hderiv t h2, hA t]
    ring
  have habel := sum_mul_eq_sub_sub_integral_mul c (f := f) hy0 hyx hdiff hint
  rw [← hL, habel, hA x, hA y, hI]
  simp only [f, one_div]
  ring

/-- LEAF. For real 1 < y ≤ x, ∫_y^x 1/(t log t) dt = log log x - log log y.
Antiderivative log log t. Unit U-1528. -/
theorem integral_inv_mul_log {x y : ℝ} (hy : 1 < y) (hyx : y ≤ x) :
    ∫ t in y..x, 1 / (t * log t) = log (log x) - log (log y) := by
  have hd : ∀ t ∈ Set.uIcc y x, HasDerivAt (fun u => log (log u)) (1 / (t * log t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hyx] at ht
    have ht1 : 1 < t := by linarith [ht.1, hy]
    have h1 : HasDerivAt log t⁻¹ t := Real.hasDerivAt_log (by positivity)
    have h2 : HasDerivAt log (log t)⁻¹ (log t) := Real.hasDerivAt_log (Real.log_pos ht1).ne'
    have h3 := HasDerivAt.comp t h2 h1
    have eq : (log t)⁻¹ * t⁻¹ = 1 / (t * log t) := by
      rw [mul_comm, ← mul_inv, one_div]
    exact eq ▸ h3
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt hd
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.div continuousOn_const ?_ ?_
  · refine ContinuousOn.mul continuousOn_id ?_
    exact ContinuousOn.log continuousOn_id (fun t ht => by
      rw [Set.uIcc_of_le hyx] at ht
      have ht1 : 1 < t := by linarith [ht.1, hy]
      positivity)
  · intro t ht
    rw [Set.uIcc_of_le hyx] at ht
    have ht1 : 1 < t := by linarith [ht.1, hy]
    have hlog : 0 < log t := Real.log_pos ht1
    positivity

/-- LEAF. Integral error: for real 2 ≤ y ≤ x, with A(t) = Σ_{p ≤ t} log p/p,
|∫_y^x A(t)/(t log² t) dt - (log log x - log log y)| ≤ 2 (1/log y - 1/log x).
Proof: A(t) = log t + R(t) with |R(t)| ≤ 2 (`Decomp1528a.mertens1_abs`), the log t part is
`integral_inv_mul_log`, and ∫_y^x 2/(t log² t) = 2 (1/log y - 1/log x). A is a step function,
so it is interval integrable. Unit U-1528. -/
theorem integral_A_sub {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    |(∫ t in y..x, (∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p) / (t * log t ^ 2)) -
        (log (log x) - log (log y))| ≤ 2 * (1 / log y - 1 / log x) := by
  have hy1 : (1 : ℝ) < y := by linarith
  have hly : 0 < log y := Real.log_pos hy1
  have hlx : 0 < log x := Real.log_pos (by linarith : (1 : ℝ) < x)
  set A : ℝ → ℝ := fun t => ∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p with hA
  set c : ℕ → ℝ := fun k => if k.Prime then log k / k else 0 with hc
  have hAeq : ∀ t : ℝ, A t = ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
    intro t
    rw [hA, hc]
    simp only []
    rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  -- the weight 1/(t log²t) is continuous, hence integrable, on [y,x]
  have hgcont : ContinuousOn (fun t : ℝ => 1 / (t * log t ^ 2)) (Set.Icc y x) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · refine ContinuousOn.mul continuousOn_id (ContinuousOn.pow ?_ 2)
      exact ContinuousOn.log continuousOn_id (fun t ht => by
        have h2 : 2 ≤ t := le_trans hy ht.1
        positivity)
    · intro t ht
      have h2 : 2 ≤ t := le_trans hy ht.1
      have hp : 0 < log t := Real.log_pos (by linarith)
      have h0 : (0 : ℝ) < t := by linarith
      positivity
  have hgint : MeasureTheory.IntegrableOn (fun t : ℝ => 1 / (t * log t ^ 2)) (Set.Icc y x) :=
    hgcont.integrableOn_compact isCompact_Icc
  -- A/(t log² t) is interval integrable
  have hAii : IntervalIntegrable (fun t : ℝ => A t / (t * log t ^ 2)) MeasureTheory.volume y x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hyx]
    refine (integrableOn_mul_sum_Icc c (le_trans (by norm_num : (0 : ℝ) ≤ 2) hy)
      (m := 0) hgint).congr_fun ?_ measurableSet_Icc
    intro t ht
    simp only []
    rw [hAeq t]
    ring
  -- 1/(t log t) is interval integrable
  have hBcont : ContinuousOn (fun t : ℝ => 1 / (t * log t)) (Set.Icc y x) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · refine ContinuousOn.mul continuousOn_id ?_
      exact ContinuousOn.log continuousOn_id (fun t ht => by
        have h2 : 2 ≤ t := le_trans hy ht.1
        positivity)
    · intro t ht
      have h2 : 2 ≤ t := le_trans hy ht.1
      have hp : 0 < log t := Real.log_pos (by linarith)
      have h0 : (0 : ℝ) < t := by linarith
      positivity
  have hBii : IntervalIntegrable (fun t : ℝ => 1 / (t * log t)) MeasureTheory.volume y x :=
    hBcont.intervalIntegrable_of_Icc hyx
  -- split the comparison term off the integral
  have hkey : (∫ t in y..x, A t / (t * log t ^ 2)) - (log (log x) - log (log y)) =
      ∫ t in y..x, (A t - log t) / (t * log t ^ 2) := by
    rw [← integral_inv_mul_log hy1 hyx]
    rw [← intervalIntegral.integral_sub hAii hBii]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hyx] at ht
    have h2 : 2 ≤ t := le_trans hy ht.1
    have h0 : (0 : ℝ) < t := by linarith
    have hp : 0 < log t := Real.log_pos (by linarith)
    have ht0 : (t : ℝ) ≠ 0 := h0.ne'
    have hp0 : log t ≠ 0 := hp.ne'
    field_simp
  rw [hkey]
  -- bound the integrand pointwise by 2/(t log²t)
  have hmert : ∀ t : ℝ, 2 ≤ t → |A t - log t| ≤ 2 := by
    intro t ht
    have := Decomp1528a.mertens1_abs (x := t) (by linarith)
    simpa [A] using this
  have habs : |∫ t in y..x, (A t - log t) / (t * log t ^ 2)| ≤
      ∫ t in y..x, |(A t - log t) / (t * log t ^ 2)| :=
    intervalIntegral.abs_integral_le_integral_abs hyx
  have hpos : ∀ t ∈ Set.Icc y x, (0 : ℝ) < t * log t ^ 2 := by
    intro t ht
    have h2 : 2 ≤ t := le_trans hy ht.1
    have hp : 0 < log t := Real.log_pos (by linarith)
    have h0 : (0 : ℝ) < t := by linarith
    positivity
  have hmono : ∫ t in y..x, |(A t - log t) / (t * log t ^ 2)| ≤
      ∫ t in y..x, 2 / (t * log t ^ 2) := by
    refine intervalIntegral.integral_mono_on (f := fun t : ℝ => |(A t - log t) / (t * log t ^ 2)|)
      (g := fun t : ℝ => 2 / (t * log t ^ 2)) hyx ?_ ?_ ?_
    · have hsub : IntervalIntegrable (fun t : ℝ => (A t - log t) / (t * log t ^ 2))
          MeasureTheory.volume y x := by
        refine IntervalIntegrable.congr ?_ (hAii.sub hBii)
        intro t ht
        rw [Set.uIoc_of_le hyx] at ht
        have h0 : (0 : ℝ) < t := by linarith [ht.1]
        have hp : 0 < log t := Real.log_pos (by linarith [ht.1])
        have ht0 : (t : ℝ) ≠ 0 := h0.ne'
        have hp0 : log t ≠ 0 := hp.ne'
        field_simp
      exact hsub.abs
    · refine ContinuousOn.intervalIntegrable_of_Icc hyx ?_
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · refine ContinuousOn.mul continuousOn_id (ContinuousOn.pow ?_ 2)
        exact ContinuousOn.log continuousOn_id (fun t ht => by
          have h2 : 2 ≤ t := le_trans hy ht.1
          positivity)
      · exact fun t ht => (hpos t ht).ne'
    · intro t ht
      have h2 : 2 ≤ t := le_trans hy ht.1
      have hp2 := hpos t ht
      rw [abs_div, abs_of_pos hp2]
      gcongr
      exact hmert t h2
  -- value of the comparison integral
  have hderiv2 : ∀ t ∈ Set.uIcc y x, HasDerivAt (fun u : ℝ => -2 / log u) (2 / (t * log t ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hyx] at ht
    have h2 : 2 ≤ t := le_trans hy ht.1
    have h0 : (0 : ℝ) < t := by linarith
    have hp : 0 < log t := Real.log_pos (by linarith)
    have hd : HasDerivAt (fun u : ℝ => (log u)⁻¹) (-(t : ℝ)⁻¹ / log t ^ 2) t :=
      (Real.hasDerivAt_log h0.ne').inv hp.ne'
    have h2' := hd.const_mul (-2 : ℝ)
    have hfun : (fun u : ℝ => -2 / log u) = (fun u : ℝ => -2 * (log u)⁻¹) := by
      ext u
      simp [div_eq_mul_inv]
    have hval_eq : (-2 : ℝ) * (-(t : ℝ)⁻¹ / log t ^ 2) = 2 / (t * log t ^ 2) := by
      have ht0 : (t : ℝ) ≠ 0 := h0.ne'
      have hp0 : log t ≠ 0 := hp.ne'
      field_simp
    rw [hval_eq] at h2'
    rw [← hfun] at h2'
    exact h2'
  have h2int : IntervalIntegrable (fun t : ℝ => 2 / (t * log t ^ 2)) MeasureTheory.volume y x := by
    refine ContinuousOn.intervalIntegrable_of_Icc hyx ?_
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · refine ContinuousOn.mul continuousOn_id (ContinuousOn.pow ?_ 2)
      exact ContinuousOn.log continuousOn_id (fun t ht => by
        have h2 : 2 ≤ t := le_trans hy ht.1
        positivity)
    · exact fun t ht => (hpos t ht).ne'
  have hval : ∫ t in y..x, 2 / (t * log t ^ 2) = 2 * (1 / log y - 1 / log x) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv2 h2int]
    field_simp
    ring
  linarith [habs, hmono, hval]

/-- **Explicit Mertens second theorem, block form**: for real 2 ≤ y ≤ x,
|Σ_{y < p ≤ x} 1/p - (log log x - log log y)| ≤ 4/log y.
Python: worst ratio 0.13 of the bound on a sample grid to 2·10^6.
Assembly from `abel_recip`, `integral_A_sub` and `Decomp1528a.mertens1_abs`. -/
theorem mertens2_block {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    |∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p - (log (log x) - log (log y))| ≤
      4 / log y := by
  have hx : 2 ≤ x := le_trans hy hyx
  have hly : 0 < log y := Real.log_pos (by linarith)
  have hlx : 0 < log x := Real.log_pos (by linarith)
  have hlyx : log y ≤ log x := Real.log_le_log (by linarith) hyx
  have hab := abel_recip hy hyx
  have hI := integral_A_sub hy hyx
  have hRx := Decomp1528a.mertens1_abs (x := x) (by linarith)
  have hRy := Decomp1528a.mertens1_abs (x := y) (by linarith)
  set Ax := ∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p
  set Ay := ∑ p ∈ Nat.primesLE ⌊y⌋₊, log p / p
  set I := ∫ t in y..x, (∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p) / (t * log t ^ 2)
  have ex : Ax / log x = 1 + (Ax - log x) / log x := by field_simp; ring
  have ey : Ay / log y = 1 + (Ay - log y) / log y := by field_simp; ring
  have bx : |(Ax - log x) / log x| ≤ 2 / log x := by
    rw [abs_div, abs_of_pos hlx]; exact div_le_div_of_nonneg_right hRx hlx.le
  have bY : |(Ay - log y) / log y| ≤ 2 / log y := by
    rw [abs_div, abs_of_pos hly]; exact div_le_div_of_nonneg_right hRy hly.le
  rw [hab, ex, ey]
  have key : 1 + (Ax - log x) / log x - (1 + (Ay - log y) / log y) + I -
      (log (log x) - log (log y)) =
      (Ax - log x) / log x - (Ay - log y) / log y + (I - (log (log x) - log (log y))) := by ring
  rw [key]
  calc |(Ax - log x) / log x - (Ay - log y) / log y + (I - (log (log x) - log (log y)))|
      ≤ |(Ax - log x) / log x| + |(Ay - log y) / log y| +
          |I - (log (log x) - log (log y))| := by
        have := abs_add_le ((Ax - log x) / log x - (Ay - log y) / log y)
          (I - (log (log x) - log (log y)))
        have := abs_sub ((Ax - log x) / log x) ((Ay - log y) / log y)
        linarith
    _ ≤ 2 / log x + 2 / log y + 2 * (1 / log y - 1 / log x) := by linarith
    _ = 4 / log y := by ring

/-! ### The constant B -/

set_option linter.unusedVariables false in
/-- LEAF. Block split: for real 0 ≤ y ≤ x,
Σ_{p ≤ x} 1/p = Σ_{p ≤ y} 1/p + Σ_{y < p ≤ x} 1/p. Unit U-1528. -/
theorem sum_recip_split {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p =
      ∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p + ∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
  have _ : 0 ≤ y := hy
  have e : Nat.primesLE ⌊x⌋₊ = Nat.primesLE ⌊y⌋₊ ∪ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE, mem_union, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hp, h2⟩
      by_cases h : p ≤ ⌊y⌋₊
      · left; exact ⟨h, h2⟩
      · right; exact ⟨⟨not_le.mp h, hp⟩, h2⟩
    · rintro (⟨hp, h2⟩ | ⟨⟨-, hp⟩, h2⟩)
      · exact ⟨le_trans hp (Nat.floor_mono hyx), h2⟩
      · exact ⟨hp, h2⟩
  rw [e, sum_union]
  have hd : Disjoint (Nat.primesLE ⌊y⌋₊) ((Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime) := by
    rw [disjoint_iff_ne]
    intro a ha b hb eq
    rw [Nat.mem_primesLE] at ha
    rw [mem_filter, mem_Ioc] at hb
    subst eq
    exact not_le.mpr hb.1.1 ha.1
  exact hd

/-- LEAF. Limits from a Cauchy modulus: if F, g : ℝ → ℝ, g → 0 at infinity and
|F x - F y| ≤ g y whenever a ≤ y ≤ x, then F has a limit B with |F x - B| ≤ g x for x ≥ a.
Standard; Mathlib `cauchySeq_tendsto_of_complete` style. Unit U-1528. -/
theorem exists_limit_of_modulus (F g : ℝ → ℝ) (a : ℝ) (hg : Tendsto g atTop (𝓝 0))
    (hF : ∀ x y, a ≤ y → y ≤ x → |F x - F y| ≤ g y) :
    ∃ B : ℝ, ∀ x, a ≤ x → |F x - B| ≤ g x := by
  have hc : CauchySeq F := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hg ε hε
    use max N a
    intro n hn
    have h1 : a ≤ max N a := le_max_right N a
    have h2 : max N a ≤ n := hn
    have h3 := hF n (max N a) h1 h2
    have hN_max : N ≤ max N a := le_max_left N a
    have h4 : |g (max N a)| < ε := by
      have hdist := hN (max N a) hN_max
      rw [dist_zero_right] at hdist
      exact hdist
    have hg_pos : 0 ≤ g (max N a) := by
      have : |F n - F (max N a)| ≤ g (max N a) := h3
      exact le_trans (abs_nonneg _) this
    rw [abs_of_nonneg hg_pos] at h4
    exact lt_of_le_of_lt h3 h4
  obtain ⟨B, hB⟩ := cauchySeq_tendsto_of_complete hc
  use B
  intro x hx
  have htendsto : Tendsto (fun y => F y - F x) atTop (𝓝 (B - F x)) :=
    Tendsto.sub_const hB (F x)
  have heventual : ∀ᶠ y in atTop, F y - F x ∈ Set.Icc (-g x) (g x) := by
    rw [eventually_atTop]
    use x
    intro y hy_
    have hle := hF y x hx hy_
    rw [abs_le] at hle
    exact hle
  have hmem := isClosed_Icc.mem_of_tendsto htendsto heventual
  rw [Set.mem_Icc] at hmem
  rw [abs_sub_comm, abs_le]
  exact ⟨hmem.1, hmem.2⟩

/-- **Explicit Mertens second theorem with its constant**: there is B (Meissel-Mertens, 0.26149...)
with |Σ_{p ≤ x} 1/p - log log x - B| ≤ 4/log x for every real x ≥ 2.
Assembly from `mertens2_block`, `sum_recip_split`, `exists_limit_of_modulus`. -/
theorem mertens2_exists_B :
    ∃ B : ℝ, ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - log (log x) - B| ≤ 4 / log x := by
  have hg : Tendsto (fun x : ℝ => 4 / log x) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop
  obtain ⟨B, hB⟩ := exists_limit_of_modulus
    (fun x => ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - log (log x)) (fun x => 4 / log x) 2 hg
    (by
      intro x y hy hyx
      have h1 := mertens2_block hy hyx
      have h2 := sum_recip_split (by linarith : (0 : ℝ) ≤ y) hyx
      rw [h2]
      have e : ∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p +
            ∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p - log (log x) -
          (∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p - log (log y)) =
          ∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p - (log (log x) - log (log y)) := by
        ring
      rw [e]; exact h1)
  exact ⟨B, fun x hx => by have := hB x hx; simpa [sub_sub] using this⟩

/-- LEAF. Σ_{p ≤ 2} 1/p = 1/2. Unit U-1528. -/
theorem sum_recip_two : ∑ p ∈ Nat.primesLE 2, (1 : ℝ) / p = 1 / 2 := by
  have e : Nat.primesLE 2 = {2} := by
    ext p
    simp only [Nat.mem_primesLE, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      have : p ≥ 2 := Nat.Prime.two_le h2
      linarith
    · rintro rfl
      exact ⟨by linarith, Nat.prime_two⟩
  rw [e, sum_singleton]
  norm_num

/-- LEAF. Numeric: -0.3666 ≤ log log 2 and 4/log 2 ≤ 5.771; log 2 = 0.693147...,
log log 2 = -0.366513, 4/log 2 = 5.770780. Unit U-1528. -/
theorem loglog2_bounds : -0.3666 ≤ log (log 2) ∧ 4 / log 2 ≤ 5.771 := by
  have h1 : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have h2 : log 2 < 0.6931471808 := Real.log_two_lt_d9
  constructor
  · have h3 : log 0.6931471803 ≤ log (log 2) := Real.log_le_log (by norm_num) h1.le
    have h4 : (-0.3666 : ℝ) ≤ log 0.6931471803 := by
      rw [← Real.exp_le_exp, Real.exp_log (by norm_num)]
      have h_bound := Real.exp_bound (x := -0.3666) (by norm_num) (n := 6) (by norm_num)
      have h_approx : ∑ m ∈ range 6, (-0.3666 : ℝ) ^ m / ↑m.factorial =
          1 - 0.3666 + 0.3666^2 / 2 - 0.3666^3 / 6 + 0.3666^4 / 24 - 0.3666^5 / 120 := by
        simp [sum_range_succ]; norm_num
      have h_val2 : (|-0.3666| : ℝ) ^ 6 * (↑(Nat.succ 6) / (↑(Nat.factorial 6) * (6 : ℝ))) ≤ 0.00001 := by norm_num
      rw [h_approx] at h_bound
      have h1_bound : rexp (-0.3666) - (1 - 0.3666 + 0.3666^2 / 2 - 0.3666^3 / 6 + 0.3666^4 / 24 - 0.3666^5 / 120) ≤ 0.00001 :=
        le_trans (le_abs_self _) (le_trans h_bound h_val2)
      calc
        rexp (-0.3666) ≤ 1 - 0.3666 + 0.3666^2 / 2 - 0.3666^3 / 6 + 0.3666^4 / 24 - 0.3666^5 / 120 + 0.00001 := by linarith
        _ ≤ 0.6931471803 := by norm_num
    exact le_trans h4 h3
  · have h_pos : 0 < log 2 := by linarith
    have h1a : 4 / log 2 ≤ 4 / 0.6931471803 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith) h1.le
    have h2a : 4 / 0.6931471803 ≤ (5.771 : ℝ) := by
      rw [div_le_iff₀ (by norm_num)]
      norm_num
    linarith

/-- **Explicit Σ 1/p bound**: Σ_{p ≤ x} 1/p ≤ log log x + 6.638 for every real x ≥ 2,
sharpening the lab's `PNTSieve.Mertens.sum_inv_primes_le` constant 12. True constant B = 0.2615.
Assembly from `mertens2_block` at y = 2, `sum_recip_split`, `sum_recip_two`, `loglog2_bounds`. -/
theorem sum_recip_le_explicit {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p ≤ log (log x) + 6.638 := by
  have h1 := mertens2_block (le_refl (2 : ℝ)) hx
  have h2 := sum_recip_split (by norm_num : (0 : ℝ) ≤ 2) hx
  have h3 := sum_recip_two
  have h4 := loglog2_bounds
  have hf : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  rw [hf] at h1 h2
  rw [h2, h3]
  have := (abs_le.mp h1).2
  linarith [h4.1, h4.2]

/-! ### The Mertens product -/

/-- LEAF. For real p ≥ 2: 0 ≤ -log(1 - 1/p) - 1/p ≤ 1/(2 p (p - 1)), from
-log(1 - t) - t = Σ_{k ≥ 2} t^k/k ≤ t²/(2(1 - t)). Rosser-Schoenfeld 1962, proof of Theorem 7,
p. 75 style. Unit U-1528. -/
private theorem neg_log_one_sub_aux {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1 / 2) :
    0 ≤ -log (1 - t) - t ∧ -log (1 - t) - t ≤ t ^ 2 / (2 * (1 - t)) := by
  have hlt : t < 1 := by linarith
  have h1t : 0 < 1 - t := by linarith
  constructor
  · have hexp : 1 - t ≤ exp (-t) := by
      have := Real.add_one_le_exp (-t)
      linarith
    have hlog : log (1 - t) ≤ -t := by
      rw [← Real.log_exp (-t)]
      exact Real.log_le_log h1t hexp
    linarith
  · have htabs : |t| < 1 := by rw [abs_of_pos h0]; exact hlt
    have hlog := Real.hasSum_pow_div_log_of_abs_lt_one (x := t) htabs
    -- shift the logarithmic series by one term: `-log (1 - t) = t + Σ_{n} t^(n+2)/(n+2)`
    have hshift :
        HasSum (fun n : ℕ => t ^ (n + 2) / ((n : ℝ) + 2)) (-log (1 - t) - t) := by
      have h := (hasSum_nat_add_iff (f := fun n : ℕ => t ^ (n + 1) / ((n : ℝ) + 1))
        (g := -log (1 - t) - t) 1).mpr (by
          have e : -log (1 - t) - t + (∑ i ∈ range 1, t ^ (i + 1) / ((i : ℝ) + 1)) =
              -log (1 - t) := by
            simp
          rw [e]
          exact hlog)
      have key : (fun n : ℕ => t ^ (n + 1 + 1) / ((↑(n + 1) : ℝ) + 1)) =
          (fun n : ℕ => t ^ (n + 2) / ((n : ℝ) + 2)) := by
        ext n
        have h1 : (n + 1 + 1 : ℕ) = n + 2 := by omega
        have h2 : ((↑(n + 1) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
        rw [h1, h2]
      rw [key] at h
      exact h
    -- shift the geometric series by two terms
    have hgeo := hasSum_geometric_of_lt_one h0.le hlt
    have hgeo2 : HasSum (fun n : ℕ => t ^ (n + 2)) ((1 - t)⁻¹ - 1 - t) := by
      have h := (hasSum_nat_add_iff (f := fun n : ℕ => t ^ n)
        (g := (1 - t)⁻¹ - 1 - t) 2).mpr (by
          have e : (1 - t)⁻¹ - 1 - t + (∑ i ∈ range 2, t ^ i) = (1 - t)⁻¹ := by
            simp [sum_range_succ]
          rw [e]
          exact hgeo)
      simpa using h
    have hcomp : HasSum (fun n : ℕ => (1 / 2) * t ^ (n + 2)) ((1 / 2) * ((1 - t)⁻¹ - 1 - t)) :=
      hgeo2.mul_left (1 / 2)
    have hterm : ∀ n : ℕ, t ^ (n + 2) / ((n : ℝ) + 2) ≤ (1 / 2) * t ^ (n + 2) := by
      intro n
      have hpow : (0 : ℝ) ≤ t ^ (n + 2) := pow_nonneg h0.le _
      have hk2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hmul : t ^ (n + 2) / 2 * 2 ≤ t ^ (n + 2) / 2 * ((n : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hk2 (by positivity)
      have h2eq : t ^ (n + 2) / 2 * 2 = t ^ (n + 2) := by ring
      rw [div_le_iff₀ (by positivity)]
      rw [h2eq] at hmul
      linarith [hmul]
    have hle := Summable.tsum_le_tsum (f := fun n : ℕ => t ^ (n + 2) / ((n : ℝ) + 2))
      (g := fun n : ℕ => (1 / 2) * t ^ (n + 2)) hterm hshift.summable hcomp.summable
    rw [hshift.tsum_eq, hcomp.tsum_eq] at hle
    have hval : (1 / 2) * ((1 - t)⁻¹ - 1 - t) = t ^ 2 / (2 * (1 - t)) := by
      field_simp
      ring
    linarith [hle, hval]

theorem neg_log_one_sub_inv_bounds {p : ℝ} (hp : 2 ≤ p) :
    0 ≤ -log (1 - 1 / p) - 1 / p ∧ -log (1 - 1 / p) - 1 / p ≤ 1 / (2 * p * (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have ht0 : 0 < 1 / p := by positivity
  have ht1 : 1 / p ≤ 1 / 2 := by
    rw [div_le_iff₀ hp0]
    linarith
  obtain ⟨h1, h2⟩ := neg_log_one_sub_aux ht0 ht1
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have e : (1 / p) ^ 2 / (2 * (1 - 1 / p)) = 1 / (2 * p * (p - 1)) := by
    field_simp
  exact ⟨h1, e ▸ h2⟩

/-- LEAF. Telescoping tail: for naturals 1 ≤ m, Σ_{m < p ≤ n, p prime} 1/(p (p - 1)) ≤ 1/m, since
1/(k(k - 1)) = 1/(k - 1) - 1/k. Unit U-1528. -/
theorem sum_inv_pp1_tail (m n : ℕ) (hm : 1 ≤ m) :
    ∑ p ∈ (Ioc m n).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 / m := by
  have hd : ∀ p : ℕ, 2 ≤ p → (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) = 1 / ((p : ℝ) - 1) - 1 / p := by
    intro p hp
    have hp_real : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have h1 : (p : ℝ) ≠ 0 := by linarith
    have h2 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp; ring
  have h_eq : ∑ p ∈ (Ioc m n).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) =
      ∑ p ∈ (Ioc m n).filter Nat.Prime, (1 / ((p : ℝ) - 1) - 1 / p) := by
    apply sum_congr rfl
    intro p hp
    rw [mem_filter, mem_Ioc] at hp
    have : 2 ≤ p := hp.2.two_le
    exact hd p this
  rw [h_eq]
  have h_le : ∑ p ∈ (Ioc m n).filter Nat.Prime, (1 / ((p : ℝ) - 1) - 1 / p) ≤ ∑ p ∈ Ioc m n, (1 / ((p : ℝ) - 1) - 1 / p) := by
    apply sum_le_sum_of_subset_of_nonneg
    · exact filter_subset _ _
    · intro p hp _
      rw [mem_Ioc] at hp
      have hp2 : 2 ≤ p := by linarith
      have hp_real : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      have : (1 : ℝ) / ((p : ℝ) - 1) - 1 / p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        rw [hd p hp2]
      rw [this]
      have h1 : 0 < (p : ℝ) := by linarith
      have h2 : 0 < (p : ℝ) - 1 := by linarith
      positivity
  by_cases hmn : m < n
  · have h_tele : ∑ p ∈ Ioc m n, (1 / ((p : ℝ) - 1) - 1 / p) = 1 / (m : ℝ) - 1 / (n : ℝ) := by
      have e1 : Ioc m n = Ico (m + 1) (n + 1) := by
        ext x; simp only [mem_Ioc, mem_Ico]; omega
      rw [e1]
      have e2 : ∑ k ∈ Ico (m + 1) (n + 1), (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) =
          ∑ k ∈ range (n - m), (1 / (((m + 1 + k : ℕ) : ℝ) - 1) - 1 / ((m + 1 + k : ℕ) : ℝ)) := by
        rw [sum_Ico_eq_sum_range]
        have h_sub : n + 1 - (m + 1) = n - m := by omega
        rw [h_sub]
      rw [e2]
      have := sum_range_sub' (fun k => 1 / ((m + k : ℕ) : ℝ)) (n - m)
      have h_eq2 : (fun (k : ℕ) => 1 / (((m + 1 + k : ℕ) : ℝ) - 1) - 1 / ((m + 1 + k : ℕ) : ℝ)) =
          (fun k => 1 / ((m + k : ℕ) : ℝ) - 1 / ((m + (k + 1) : ℕ) : ℝ)) := by
        ext k; congr 2; push_cast; ring; push_cast; ring
      rw [h_eq2, this]
      have hz : (m + 0 : ℕ) = m := by omega
      have hn : (m + (n - m) : ℕ) = n := Nat.add_sub_of_le hmn.le
      rw [hz, hn]
    have h_final : 1 / (m : ℝ) - 1 / (n : ℝ) ≤ 1 / (m : ℝ) := by
      have : 0 ≤ 1 / (n : ℝ) := by
        have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans (by omega) hmn)
        positivity
      linarith
    linarith
  · have h_tele : Ioc m n = ∅ := by
      rw [Ioc_eq_empty_iff.mpr]
      omega
    have h_empty_sum : ∑ p ∈ Ioc m n, (1 / ((p : ℝ) - 1) - 1 / p) = 0 := by
      rw [h_tele, sum_empty]
    rw [h_empty_sum] at h_le
    have : (0 : ℝ) ≤ 1 / m := by
      have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      positivity
    linarith

/-- LEAF. Log of the product block: for any naturals m, n,
log ∏_{m < p ≤ n} (1 - 1/p) = Σ_{m < p ≤ n} log(1 - 1/p); every factor is positive. Unit U-1528. -/
theorem log_prod_block (m n : ℕ) :
    log (∏ p ∈ (Ioc m n).filter Nat.Prime, (1 - (1 : ℝ) / p)) =
      ∑ p ∈ (Ioc m n).filter Nat.Prime, log (1 - (1 : ℝ) / p) := by
  apply log_prod
  intro p hp
  rw [mem_filter] at hp
  have hp2 : 2 ≤ p := hp.2.two_le
  have hp_real : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have : (1 : ℝ) / p < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  linarith

/-- **Explicit Mertens third theorem, block form**: for real 2 ≤ y ≤ x,
|log ∏_{y < p ≤ x} (1 - 1/p) + (log log x - log log y)| ≤ 4/log y + 1/(2⌊y⌋).
Assembly from `mertens2_block`, `log_prod_block`, `neg_log_one_sub_inv_bounds`,
`sum_inv_pp1_tail`. -/
theorem mertens3_block {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    |log (∏ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p)) +
        (log (log x) - log (log y))| ≤ 4 / log y + 1 / (2 * (⌊y⌋₊ : ℝ)) := by
  set S := (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime
  have hm : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith)
  have h1 := mertens2_block hy hyx
  rw [log_prod_block]
  have hE : ∀ p ∈ S, 0 ≤ -log (1 - (1 : ℝ) / p) - 1 / p ∧
      -log (1 - (1 : ℝ) / p) - 1 / p ≤ (1 / 2) * ((1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
    have := neg_log_one_sub_inv_bounds hp2
    refine ⟨this.1, le_trans this.2 (le_of_eq ?_)⟩
    field_simp
  have hT := sum_inv_pp1_tail ⌊y⌋₊ ⌊x⌋₊ hm
  have hs0 : 0 ≤ ∑ p ∈ S, (-log (1 - (1 : ℝ) / p) - 1 / p) := sum_nonneg fun p hp => (hE p hp).1
  have hs1 : ∑ p ∈ S, (-log (1 - (1 : ℝ) / p) - 1 / p) ≤
      (1 / 2) * ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [mul_sum]; exact sum_le_sum fun p hp => (hE p hp).2
  have hsplit : ∑ p ∈ S, log (1 - (1 : ℝ) / p) =
      -(∑ p ∈ S, (1 : ℝ) / p) - ∑ p ∈ S, (-log (1 - (1 : ℝ) / p) - 1 / p) := by
    rw [sum_sub_distrib, sum_neg_distrib]; ring
  rw [hsplit]
  have hmR : (0 : ℝ) < ⌊y⌋₊ := by exact_mod_cast hm
  have e2 : (1 : ℝ) / (2 * (⌊y⌋₊ : ℝ)) = (1 / 2) * (1 / (⌊y⌋₊ : ℝ)) := by field_simp
  rw [e2]
  have := abs_le.mp h1
  rw [abs_le]; constructor <;> nlinarith [this.1, this.2]

/-- LEAF. Euler product against the harmonic sum: for every natural N,
H_N · ∏_{p ≤ N} (1 - 1/p) ≤ 1, H_N = Σ_{n ≤ N} 1/n (Mathlib `harmonic`), because
∏_{p ≤ N} (1 - 1/p)⁻¹ = ∏_{p ≤ N} Σ_k p^{-k} ≥ Σ_{n ≤ N} 1/n. Hardy-Wright, Thm 427 proof;
Rosser-Schoenfeld 1962, p. 70 style. Unit U-1528. -/
theorem harmonic_mul_prod_le (N : ℕ) :
    (harmonic N : ℝ) * ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) ≤ 1 := by
  set s : Finset ℕ := Nat.primesLE N with hs
  -- the completely multiplicative weight n ↦ 1/n
  set F : ℕ →*₀ ℝ :=
    { toFun := fun n => (n : ℝ)⁻¹
      map_zero' := by simp
      map_one' := by simp
      map_mul' := by intro a b; push_cast; rw [mul_inv] } with hF
  have hFn : ∀ n : ℕ, (F n : ℝ) = (n : ℝ)⁻¹ := fun n => rfl
  -- the geometric series at each prime is summable
  have hsumg : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖((fun n : ℕ => (F n : ℝ)) ((p : ℕ) ^ n))‖) := by
    intro p hp
    have hp2 : 2 ≤ p := hp.two_le
    have hx : ‖((p : ℝ)⁻¹)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity), inv_lt_one_iff₀]
      right
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      linarith
    have heq : (fun n : ℕ => ‖((fun n : ℕ => (F n : ℝ)) ((p : ℕ) ^ n))‖) =
        (fun n : ℕ => ‖((p : ℝ)⁻¹)‖ ^ n) := by
      funext n
      simp only []
      rw [hFn, ← norm_pow]
      congr 1
      push_cast
      rw [inv_pow]
    rw [heq]
    exact summable_geometric_of_lt_one (norm_nonneg _) hx
  -- the Euler product over the primes ≤ N, as a sum over `s`-factored numbers
  obtain ⟨hsumm, hhas⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := (fun n : ℕ => (F n : ℝ))) (by simp [hFn]) (by
      intro m n _
      simp only [hFn]
      push_cast
      rw [mul_inv]) hsumg s
  have hfilter : s.filter Nat.Prime = s := by
    rw [hs]
    exact Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primesLE hp
  -- each geometric factor is `(1 - 1/p)⁻¹`
  have hfac : ∀ p ∈ s, (∑' n : ℕ, (fun n : ℕ => (F n : ℝ)) (p ^ n)) = (1 - (1 : ℝ) / p)⁻¹ := by
    intro p hp
    have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesLE (hs ▸ hp)
    have hx : ‖((p : ℝ)⁻¹)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity), inv_lt_one_iff₀]
      right
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      linarith
    have ht : (∑' n : ℕ, (fun n : ℕ => (F n : ℝ)) (p ^ n)) = ∑' n : ℕ, ((p : ℝ)⁻¹) ^ n := by
      apply tsum_congr
      intro n
      simp only []
      rw [hFn]
      push_cast
      rw [inv_pow]
    rw [ht, tsum_geometric_of_norm_lt_one hx]
    simp
  -- every `n ≤ N` is `s`-factored
  have hmem : ∀ n ∈ Finset.Icc 1 N, n ∈ Nat.factoredNumbers s := by
    intro n hn
    rw [mem_Icc] at hn
    rw [Nat.mem_factoredNumbers_iff_forall_le]
    refine ⟨by omega, ?_⟩
    intro p hp _ hpd
    rw [hs, Nat.mem_primesLE]
    exact ⟨le_trans (Nat.le_of_dvd (by omega) hpd) hn.2, ‹Nat.Prime p›⟩
  have hsub : Summable (fun m : Nat.factoredNumbers s => (F m : ℝ)) := hhas.summable
  let e : {n // n ∈ Finset.Icc 1 N} ↪ Nat.factoredNumbers s :=
    ⟨fun n => ⟨n.1, hmem n.1 n.2⟩, by
      intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext hab⟩
  have hsumT : ∑ m ∈ Finset.map e (Finset.Icc 1 N).attach, (F m : ℝ) = (harmonic N : ℝ) := by
    rw [Finset.sum_map]
    have hcongr : (fun x : {n // n ∈ Finset.Icc 1 N} => (F (e x) : ℝ)) =
        (fun x : {n // n ∈ Finset.Icc 1 N} => (F (x : ℕ) : ℝ)) := by
      funext x
      rfl
    rw [hcongr, Finset.sum_attach, harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_congr rfl fun n _ => hFn n
  have hHle : (harmonic N : ℝ) ≤ ∑' m : Nat.factoredNumbers s, (F m : ℝ) := by
    rw [← hsumT]
    exact hsub.sum_le_tsum _ fun m _ => by rw [hFn]; positivity
  have htsum_eq : (∑' m : Nat.factoredNumbers s, (F m : ℝ)) = ∏ p ∈ s, (1 - (1 : ℝ) / p)⁻¹ := by
    rw [hhas.tsum_eq, hfilter]
    exact Finset.prod_congr rfl hfac
  have hPpos : 0 < ∏ p ∈ s, (1 - (1 : ℝ) / p) := by
    refine prod_pos fun p hp => ?_
    have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesLE (hs ▸ hp)
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have h1 : (1 : ℝ) / p < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    linarith
  have h1 : (harmonic N : ℝ) * ∏ p ∈ s, (1 - (1 : ℝ) / p) ≤
      (∏ p ∈ s, (1 - (1 : ℝ) / p)⁻¹) * ∏ p ∈ s, (1 - (1 : ℝ) / p) := by
    rw [← htsum_eq]
    exact mul_le_mul_of_nonneg_right hHle hPpos.le
  have h2 : (∏ p ∈ s, (1 - (1 : ℝ) / p)⁻¹) * ∏ p ∈ s, (1 - (1 : ℝ) / p) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun p hp => ?_
    have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesLE (hs ▸ hp)
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hne : (1 - (1 : ℝ) / p) ≠ 0 := by
      have h1 : (1 : ℝ) / p < 1 := by
        rw [div_lt_one (by linarith)]
        linarith
      linarith
    exact inv_mul_cancel₀ hne
  rw [hs] at h1
  rw [h2] at h1
  simpa using h1

/-- **Elementary Mertens product upper bound**: ∏_{p ≤ x} (1 - 1/p) ≤ 1/log x for real x ≥ 2.
Rosser-Schoenfeld (3.26), p. 70, has e^{-γ}(1 + 1/(2 log² x))/log x, sharper by 0.56.
Assembly from `harmonic_mul_prod_le` and Mathlib `log_add_one_le_harmonic`. -/
theorem mertens_prod_upper {x : ℝ} (hx : 2 ≤ x) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (1 : ℝ) / p) ≤ 1 / log x := by
  set N := ⌊x⌋₊
  have hlx : 0 < log x := Real.log_pos (by linarith)
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hl1 : log x ≤ log ((N + 1 : ℕ) : ℝ) := by
    push_cast; exact Real.log_le_log (by linarith) hxN.le
  have hH := log_add_one_le_harmonic N
  have hP := harmonic_mul_prod_le N
  have hP0 : 0 ≤ ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) := by
    refine prod_nonneg fun p hp => ?_
    have : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le
    rw [sub_nonneg, div_le_one (by linarith)]; exact this
  rw [le_div_iff₀ hlx]
  have : log x * ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) ≤
      (harmonic N : ℝ) * ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) :=
    mul_le_mul_of_nonneg_right (le_trans hl1 hH) hP0
  linarith

/-- LEAF. **Elementary Mertens product lower bound**: 1/(1500 log x) ≤ ∏_{p ≤ x} (1 - 1/p) for
real x ≥ 2. From `mertens3_block` at y = 2 and the factor 1/2 at p = 2:
the product is ≥ (log 2/2) e^{-5.771 - 1/4}/log x = 8.4·10^{-4}/log x. Sharpens the lab's
`PNTSieve.mertens_product_ge` (e^{-16}). Rosser-Schoenfeld (3.25), p. 70, has
e^{-γ}(1 - 1/(2 log² x))/log x for x ≥ 285. Unit U-1528. -/
theorem mertens_prod_lower {x : ℝ} (hx : 2 ≤ x) :
    1 / (1500 * log x) ≤ ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (1 : ℝ) / p) := by
  have hlx : 0 < log x := Real.log_pos (by linarith)
  have hN : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  -- the numeric input: 7.0808 ≤ log 1500
  have h1500 : (7.0808 : ℝ) ≤ log 1500 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 1500)]
    have h1 : exp (7.0808 : ℝ) = exp 7 * exp 0.0808 := by
      rw [← Real.exp_add]
      norm_num
    have h2 : exp 7 = (exp 1) ^ 7 := by
      have := Real.exp_nat_mul (x := (1 : ℝ)) 7
      simpa only [Nat.cast_ofNat, mul_one] using this
    have hb := Real.exp_bound (x := 0.0808) (by norm_num) (n := 3) (by norm_num)
    have hsum : (∑ m ∈ range 3, (0.0808 : ℝ) ^ m / ↑(Nat.factorial m)) =
        1 + 0.0808 + 0.0808 ^ 2 / 2 := by
      simp [sum_range_succ]
    rw [hsum, abs_le] at hb
    have herr : |(0.0808 : ℝ)| ^ 3 * ((Nat.succ 3 : ℝ) / ((Nat.factorial 3 : ℝ) * 3)) ≤ 0.0002 := by
      norm_num
    have h4 : exp 0.0808 ≤ 1.085 := by linarith [hb.2, herr]
    have h3 : (exp 1) ^ 7 ≤ 2.7182818286 ^ 7 :=
      pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_d9) 7
    have h5 : (2.7182818286 : ℝ) ^ 7 ≤ 1097 := by norm_num
    rw [h1, h2]
    have hp1 : (0 : ℝ) < (exp 1) ^ 7 := by positivity
    nlinarith [h3, h4, h5, hp1]
  have hlog2b := loglog2_bounds
  have hlog2lt : log 2 ≤ 0.6931471808 := le_of_lt Real.log_two_lt_d9
  have hlog2pos : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
  -- split off the prime 2
  have hsplit : Nat.primesLE ⌊x⌋₊ = {2} ∪ (Ioc 2 ⌊x⌋₊).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE, mem_union, mem_singleton, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h2.two_le with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨⟨h, h1⟩, h2⟩
    · rintro (rfl | ⟨⟨-, h1⟩, h2⟩)
      · exact ⟨hN, Nat.prime_two⟩
      · exact ⟨h1, h2⟩
  have hdisj : Disjoint ({2} : Finset ℕ) ((Ioc 2 ⌊x⌋₊).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [mem_singleton] at ha
    simp only [mem_filter, mem_Ioc] at hb
    subst ha
    omega
  have hPpos : 0 < ∏ p ∈ (Ioc 2 ⌊x⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p) := by
    refine prod_pos fun p hp => ?_
    rw [mem_filter, mem_Ioc] at hp
    have hp2 : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp.1.1
    have : (1 : ℝ) / p < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    linarith
  have h3 := mertens3_block (x := x) (y := 2) (le_refl (2 : ℝ)) hx
  have hf2 : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  rw [hf2] at h3
  have hlb : -(log (log x) - log (log 2)) - (4 / log 2 + 1 / (2 * 2)) ≤
      log (∏ p ∈ (Ioc 2 ⌊x⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p)) := by
    have := (abs_le.mp h3).1
    linarith
  have hlogle : log (1 / (1500 * log x)) ≤
      log ((1 - 1 / 2) * ∏ p ∈ (Ioc 2 ⌊x⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p)) := by
    rw [Real.log_mul (by norm_num) hPpos.ne']
    have e1 : log (1 / (1500 * log x)) = -log 1500 - log (log x) := by
      rw [one_div, Real.log_inv, Real.log_mul (by norm_num) hlx.ne']
      ring
    have e2 : log (1 - 1 / 2 : ℝ) = -log 2 := by
      have h : (1 - 1 / 2 : ℝ) = 2⁻¹ := by norm_num
      rw [h, Real.log_inv]
    rw [e1, e2]
    have h4 := hlog2b.2
    have h5 := hlog2b.1
    linarith [hlb, h1500, hlog2lt, h4, h5]
  have hposT : 0 < 1 / (1500 * log x) := by positivity
  have hposP : 0 < (1 - 1 / 2) * ∏ p ∈ (Ioc 2 ⌊x⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p) := by
    have : (0 : ℝ) < 1 - 1 / 2 := by norm_num
    positivity
  rw [hsplit, prod_union hdisj, prod_singleton]
  exact (Real.log_le_log_iff hposT hposP).mp hlogle

/-! ### Vacuity instances -/

/-- The hypotheses of `mertens2_block` and `mertens3_block` hold at y = 2, x = 10. -/
example : (2 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 10 := by norm_num

/-- The hypotheses of `exists_limit_of_modulus` hold for F = 0, g = 1/x, a = 1. -/
example : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) ∧
    ∀ x y : ℝ, 1 ≤ y → y ≤ x → |(0 : ℝ) - 0| ≤ 1 / y := by
  refine ⟨?_, fun x y hy _ => by simp; positivity⟩
  simpa using tendsto_inv_atTop_zero

end LeanLab.AlmostPrimes.Decomp1528b
