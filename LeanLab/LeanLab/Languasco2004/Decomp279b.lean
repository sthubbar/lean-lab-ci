/-
Perelli and Pintz 1993, https://doi.org/10.1112/jlms/s2-47.1.41.
Pages 43 to 48 give the written proof. AI wrote the Lean code.
Goldbach is open. Analytic leaves stay OPEN.
-/
import LeanLab.Languasco2004.Decomp279a

namespace LeanLab.Languasco2004.Decomp279b
open Finset Real MeasureTheory LeanLab.Languasco2004.EncA
open scoped ArithmeticFunction.vonMangoldt
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 44: the composed exponent after choosing Y and H. -/
def lengthExponent (η : ℝ) : ℝ := (7 / 12 + η) * (1 / 3 + η)
/-- Page 44: the localization parameter Y. -/
def localization (N η : ℝ) : ℝ := N ^ (7 / 12 + η)
/-- Page 44: H equals Y to the power 1/3 plus eta when N is positive. -/
def windowLength (N η : ℝ) : ℝ := N ^ lengthExponent η
/-- Page 44: even integers in the open left local window. -/
def window (N η : ℝ) : Finset ℕ :=
  (Ioc ⌊N⌋₊ ⌊N + windowLength N η⌋₊).filter Even
/-- Page 43: summation indices for R star and M star at m. -/
def pairs (N Y : ℝ) (m : ℕ) : Finset ℕ :=
  (Ioo 0 m).filter (fun h : ℕ => N - Y < (h : ℝ) ∧ (h : ℝ) ≤ N ∧ ((m - h : ℕ) : ℝ) ≤ Y)
/-- Page 43: the weighted representation sum R star. -/
def weightedCount (N Y : ℝ) (m : ℕ) : ℝ :=
  ∑ h ∈ pairs N Y m, Λ h * Λ (m - h)
/-- Page 43: the unweighted representation sum M star. -/
def unweightedCount (N Y : ℝ) (m : ℕ) : ℝ := (pairs N Y m).card
/-- Page 43: e of alpha. -/
def phase (α : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * α)
/-- Page 43: the first prime exponential sum S1. -/
def firstSum (N Y α : ℝ) : ℂ :=
  ∑ h ∈ Ioc ⌊N - Y⌋₊ ⌊N⌋₊, (Λ h : ℂ) * phase (h * α)
/-- Page 43: the second prime exponential sum S2. -/
def secondSum (Y α : ℝ) : ℂ :=
  ∑ k ∈ Icc 1 ⌊Y⌋₊, (Λ k : ℂ) * phase (k * α)
/-- Page 43: the prescribed logarithmic arc exponent B. -/
def arcExponent (η A : ℝ) : ℝ := 3 / η * (2 * A + 25)
/-- Page 43: the union of the small major arcs I prime of q and a. -/
def majorSet (N Y B : ℝ) : Set ℝ :=
  {α | ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ B ∧
    1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |α - (a : ℝ) / q| < Real.log N ^ (2 * B) / ((q : ℝ) * Y)}
/-- Page 43: the period of integration from 1/Q to 1 plus 1/Q. -/
def period (H : ℝ) : Set ℝ := Set.Icc (2 / Real.sqrt H) (1 + 2 / Real.sqrt H)
/-- Page 44 display 1: the major arc Fourier coefficient. -/
def majorCoefficient (N Y H B : ℝ) (m : ℕ) : ℂ :=
  ∫ α in period H ∩ majorSet N Y B,
    firstSum N Y α * secondSum Y α * phase (-(m : ℝ) * α)
/-- Page 44 display 3: the minor arc Fourier coefficient. -/
def minorCoefficient (N Y H B : ℝ) (m : ℕ) : ℂ :=
  ∫ α in period H \ majorSet N Y B,
    firstSum N Y α * secondSum Y α * phase (-(m : ℝ) * α)
/-- Page 44 display 1: the major arc error after subtracting the singular main term. -/
def majorError (N η A : ℝ) (m : ℕ) : ℂ :=
  majorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m -
    ((Decomp279a.singular m * unweightedCount N (localization N η) m : ℝ) : ℂ)
/-- Page 44 display 1: the full representation error. -/
def fullError (N η : ℝ) (m : ℕ) : ℝ :=
  weightedCount N (localization N η) m -
    Decomp279a.singular m * unweightedCount N (localization N η) m

/-- LEAF. Pages 44 and 45 display 4, completed on page 46.
This controls only the major arc error, not the exceptional count. -/
theorem major_bound :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∑ m ∈ window N η, ‖majorError N η A m‖ ^ 2 ≤
        C * windowLength N η * localization N η ^ 2 / Real.log N ^ A := by sorry

/-- LEAF. Page 44 display 3 and page 46 display 5, proved through display 26
on page 48. This is the minor arc mean square obtained from the local S2 bound. -/
theorem minor_bound :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∑ m ∈ window N η,
        ‖minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2 ≤
        C * windowLength N η * localization N η ^ 2 / Real.log N ^ A := by sorry

private lemma phase_add (x y : ℝ) : phase x * phase y = phase (x + y) := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma integral_exp_int_period (n : ℤ) (a : ℝ) :
    (∫ x in a..(1 + a), Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)))
      = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [ite_eq_right hn]
    have hc : (2 * Real.pi * Complex.I * (n : ℂ)) ≠ 0 := by
      have hreal : (2 * Real.pi * (n : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (by exact_mod_cast hn)
      rw [show (2 * Real.pi * Complex.I * (n : ℂ)) = ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hreal) Complex.I_ne_zero
    rw [show (∫ x in a..(1 + a),
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)))
        = ∫ x in a..(1 + a),
          Complex.exp ((2 * Real.pi * Complex.I * (n : ℂ)) * (x : ℂ)) from by
      simp only [mul_assoc]]
    rw [integral_exp_mul_complex hc]
    rw [div_eq_zero_iff]
    left
    rw [sub_eq_zero]
    have h1 : Complex.exp ((2 * Real.pi * Complex.I * (n : ℂ)) * ((1 + a : ℝ) : ℂ))
        = Complex.exp ((2 * Real.pi * Complex.I * (n : ℂ)) * (a : ℂ)
            + (n : ℂ) * (2 * Real.pi * Complex.I)) := by
      congr 1
      push_cast
      ring
    rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The phase of a sum of two integer multiples of the period, with the coefficient of `-m`. -/
private lemma phase_mul_three (h k m : ℕ) (α : ℝ) :
    phase ((h : ℝ) * α) * phase ((k : ℝ) * α) * phase (-(m : ℝ) * α) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((((h : ℤ) + (k : ℤ) - (m : ℤ) : ℤ)) : ℂ) * (α : ℂ)) := by
  rw [phase_add, phase_add]
  unfold phase
  congr 1
  push_cast
  ring

private lemma integrand_eq_sum (N Y : ℝ) (m : ℕ) (α : ℝ) :
    firstSum N Y α * secondSum Y α * phase (-(m : ℝ) * α) =
      ∑ h ∈ Ioc ⌊N - Y⌋₊ ⌊N⌋₊, ∑ k ∈ Icc 1 ⌊Y⌋₊,
        ((Λ h : ℂ) * (Λ k : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I *
            ((((h : ℤ) + (k : ℤ) - (m : ℤ) : ℤ)) : ℂ) * (α : ℂ)) := by
  unfold firstSum secondSum
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro h _
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro k _
  rw [show ((Λ h : ℂ) * phase ((h : ℝ) * α)) * ((Λ k : ℂ) * phase ((k : ℝ) * α))
        * phase (-(m : ℝ) * α) =
      ((Λ h : ℂ) * (Λ k : ℂ)) *
        (phase ((h : ℝ) * α) * phase ((k : ℝ) * α) * phase (-(m : ℝ) * α)) by ring,
    phase_mul_three]

private lemma pairs_eq (N Y : ℝ) (m : ℕ) :
    pairs N Y m =
      (Ioc ⌊N - Y⌋₊ ⌊N⌋₊).filter (fun h => 1 ≤ m - h ∧ m - h ≤ ⌊Y⌋₊) := by
  unfold pairs
  ext h
  simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h0, hm⟩, hNY, hN, hY⟩
    exact ⟨⟨(Nat.floor_lt' (by omega)).mpr hNY, (Nat.le_floor_iff' (by omega)).mpr hN⟩,
      by omega, (Nat.le_floor_iff' (by omega)).mpr hY⟩
  · rintro ⟨⟨hfloor, hNfloor⟩, h1, hYfloor⟩
    exact ⟨⟨by omega, by omega⟩, (Nat.floor_lt' (by omega)).mp hfloor,
      (Nat.le_floor_iff' (by omega)).mp hNfloor, (Nat.le_floor_iff' (by omega)).mp hYfloor⟩

private lemma inner_sum_C (Y : ℝ) (m h : ℕ) :
    ∑ k ∈ Icc 1 ⌊Y⌋₊, ((Λ h : ℂ) * (Λ k : ℂ)) * (if h + k = m then (1 : ℂ) else 0)
      = if 1 ≤ m - h ∧ m - h ≤ ⌊Y⌋₊ then (Λ h : ℂ) * (Λ (m - h) : ℂ) else 0 := by
  have key : ∀ k : ℕ, 1 ≤ k → ((Λ h : ℂ) * (Λ k : ℂ)) * (if h + k = m then (1 : ℂ) else 0)
      = if k = m - h then (Λ h : ℂ) * (Λ (m - h) : ℂ) else 0 := by
    intro k hk1
    by_cases hk : h + k = m
    · have hkh : k = m - h := by omega
      rw [if_pos hk, if_pos hkh, mul_one, hkh]
    · have hkh : k ≠ m - h := by
        intro hh
        rw [hh] at hk1
        omega
      rw [if_neg hk, if_neg hkh, mul_zero]
  rw [Finset.sum_congr rfl (fun k hk => key k (Finset.mem_Icc.mp hk).1), Finset.sum_ite_eq']
  simp only [Finset.mem_Icc]

private lemma double_sum_eq_weighted_C (N Y : ℝ) (m : ℕ) :
    ∑ h ∈ Ioc ⌊N - Y⌋₊ ⌊N⌋₊, ∑ k ∈ Icc 1 ⌊Y⌋₊,
        ((Λ h : ℂ) * (Λ k : ℂ)) * (if h + k = m then (1 : ℂ) else 0)
      = (weightedCount N Y m : ℂ) := by
  rw [Finset.sum_congr rfl (fun h _ => inner_sum_C Y m h)]
  rw [← Finset.sum_filter]
  rw [← pairs_eq]
  rw [weightedCount]
  push_cast
  rfl

private lemma period_integral_eq_weighted (N Y H : ℝ) (m : ℕ) :
    ∫ α in period H, firstSum N Y α * secondSum Y α * phase (-(m : ℝ) * α)
      = (weightedCount N Y m : ℂ) := by
  have hle : 2 / Real.sqrt H ≤ 1 + 2 / Real.sqrt H := by
    have : (0 : ℝ) ≤ 2 / Real.sqrt H := by positivity
    linarith
  rw [show period H = Set.Icc (2 / Real.sqrt H) (1 + 2 / Real.sqrt H) from rfl,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  rw [intervalIntegral.integral_congr (fun α _ => integrand_eq_sum N Y m α)]
  have hG : ∀ h k : ℕ, IntervalIntegrable (fun α : ℝ => ((Λ h : ℂ) * (Λ k : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I *
        ((((h : ℤ) + (k : ℤ) - (m : ℤ) : ℤ)) : ℂ) * (α : ℂ))) volume
      (2 / Real.sqrt H) (1 + 2 / Real.sqrt H) := by
    intro h k
    exact (by fun_prop : Continuous fun α : ℝ => ((Λ h : ℂ) * (Λ k : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I *
        ((((h : ℤ) + (k : ℤ) - (m : ℤ) : ℤ)) : ℂ) * (α : ℂ))).intervalIntegrable _ _
  have hGs : ∀ h : ℕ, IntervalIntegrable (fun α : ℝ => ∑ k ∈ Icc 1 ⌊Y⌋₊, ((Λ h : ℂ) * (Λ k : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I *
        ((((h : ℤ) + (k : ℤ) - (m : ℤ) : ℤ)) : ℂ) * (α : ℂ))) volume
      (2 / Real.sqrt H) (1 + 2 / Real.sqrt H) := by
    intro h
    exact (by fun_prop : Continuous fun α : ℝ => ∑ k ∈ Icc 1 ⌊Y⌋₊, ((Λ h : ℂ) * (Λ k : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I *
        ((((h : ℤ) + (k : ℤ) - (m : ℤ) : ℤ)) : ℂ) * (α : ℂ))).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (fun h _ => hGs h)]
  rw [Finset.sum_congr rfl
    (fun h _ => intervalIntegral.integral_finsetSum (fun k _ => hG h k))]
  have hterm : ∀ h k : ℕ, (∫ x in (2 / Real.sqrt H)..(1 + 2 / Real.sqrt H),
      ((Λ h : ℂ) * (Λ k : ℂ)) * Complex.exp (2 * Real.pi * Complex.I *
        ((((h : ℤ) + (k : ℤ) - (m : ℤ) : ℤ)) : ℂ) * (x : ℂ)))
      = ((Λ h : ℂ) * (Λ k : ℂ)) * (if h + k = m then (1 : ℂ) else 0) := by
    intro h k
    rw [intervalIntegral.integral_const_mul, integral_exp_int_period]
    congr 1
    by_cases hk : h + k = m
    · have hn : ((h : ℤ) + (k : ℤ) - (m : ℤ)) = 0 := by omega
      rw [if_pos hk, if_pos hn]
    · have hn : ¬(((h : ℤ) + (k : ℤ) - (m : ℤ)) = 0) := by omega
      rw [if_neg hk, if_neg hn]
  rw [Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun k _ => hterm h k))]
  rw [double_sum_eq_weighted_C]

private lemma measurableSet_majorSet (N Y B : ℝ) : MeasurableSet (majorSet N Y B) := by
  have h : majorSet N Y B = ⋃ (q : ℕ) (a : ℕ), {α : ℝ |
      1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ B ∧ 1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |α - (a : ℝ) / q| < Real.log N ^ (2 * B) / ((q : ℝ) * Y)} := by
    ext α
    simp only [majorSet, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [h]
  apply MeasurableSet.iUnion; intro q
  apply MeasurableSet.iUnion; intro a
  by_cases hq : 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ B ∧ 1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hq
    convert measurableSet_Ioo (a := (a : ℝ) / q - Real.log N ^ (2 * B) / ((q : ℝ) * Y))
      (b := (a : ℝ) / q + Real.log N ^ (2 * B) / ((q : ℝ) * Y)) using 1
    ext α
    simp only [Set.mem_setOf_eq, Set.mem_Ioo]
    constructor
    · rintro ⟨-, -, -, -, -, hlt⟩
      rw [abs_lt] at hlt
      exact ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
    · rintro ⟨ha, hb⟩
      exact ⟨h1, h2, h3, h4, h5, by rw [abs_lt]; exact ⟨by linarith, by linarith⟩⟩
  · have hne : {α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ B ∧ 1 ≤ a ∧ a ≤ q ∧
        Nat.Coprime a q ∧ |α - (a : ℝ) / q| < Real.log N ^ (2 * B) / ((q : ℝ) * Y)} = ∅ := by
      ext α
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, -⟩
        exact hq ⟨h1, h2, h3, h4, h5⟩
      · intro hh
        exact hh.elim
    rw [hne]
    exact MeasurableSet.empty

private lemma coeff_split (N Y H B : ℝ) (m : ℕ) :
    majorCoefficient N Y H B m + minorCoefficient N Y H B m =
      ∫ α in period H, firstSum N Y α * secondSum Y α * phase (-(m : ℝ) * α) := by
  have hM : MeasurableSet (majorSet N Y B) := measurableSet_majorSet N Y B
  have hcont : Continuous fun α : ℝ => firstSum N Y α * secondSum Y α * phase (-(m : ℝ) * α) := by
    unfold firstSum secondSum phase
    fun_prop
  have hint : IntegrableOn
      (fun α : ℝ => firstSum N Y α * secondSum Y α * phase (-(m : ℝ) * α))
      (Set.Icc (2 / Real.sqrt H) (1 + 2 / Real.sqrt H)) volume :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  unfold majorCoefficient minorCoefficient
  rw [show period H = Set.Icc (2 / Real.sqrt H) (1 + 2 / Real.sqrt H) from rfl]
  rw [← setIntegral_union
    (s := Set.Icc (2 / Real.sqrt H) (1 + 2 / Real.sqrt H) ∩ majorSet N Y B)
    (t := Set.Icc (2 / Real.sqrt H) (1 + 2 / Real.sqrt H) \ majorSet N Y B)
    (by rw [Set.disjoint_left]; rintro x ⟨-, hxM⟩ ⟨-, hxnM⟩; exact hxnM hxM)
    (measurableSet_Icc.diff hM)
    (hint.mono_set Set.inter_subset_left) (hint.mono_set Set.sdiff_subset),
    Set.inter_union_sdiff]

/-- LEAF. Page 44 display 1, before applying Cauchy Schwarz.
Fourier orthogonality and the partition of the period give the coefficient identity. -/
theorem fourier_split (N η A : ℝ) (hN : 3 ≤ N) (hη : 0 < η) (m : ℕ) :
    (fullError N η m : ℂ) = majorError N η A m +
      minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m := by
  have hkey : (weightedCount N (localization N η) m : ℂ) =
      majorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m +
      minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m :=
    ((coeff_split N (localization N η) (windowLength N η) (arcExponent η A) m).trans
      (period_integral_eq_weighted N (localization N η) (windowLength N η) m)).symm
  unfold fullError majorError
  push_cast
  rw [hkey]
  ring

private theorem prod_le_prod_real {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h0a : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
    have hga : 0 ≤ g a := h0a.trans (h a (Finset.mem_insert_self a s))
    have ih0 : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
    have ihle : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
      ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact mul_le_mul (h a (Finset.mem_insert_self a s)) ihle ih0 hga

/-! ## Step 1: the telescoping product and its finite lower bound -/

private theorem tel_prod (N : ℕ) :
    (∏ n ∈ Icc 2 (N + 2), (1 - 1 / (n : ℝ) ^ 2)) =
      (N + 3 : ℕ) / (2 * ((N + 2 : ℕ) : ℝ)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [show N.succ + 2 = (N + 2) + 1 by omega, prod_Icc_succ_top (by omega), ih]
    push_cast
    have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
    have h3 : (N : ℝ) + 3 ≠ 0 := by positivity
    field_simp
    ring

/-- Any finite subproduct with indices at least two is at least one half. -/
private theorem prod_lower (s : Finset ℕ) (hs : ∀ n ∈ s, 2 ≤ n) :
    (1 / 2 : ℝ) ≤ ∏ n ∈ s, (1 - 1 / (n : ℝ) ^ 2) := by
  let N := s.sup id
  have hsub : s ⊆ Icc 2 (N + 2) := by
    intro n hn
    exact mem_Icc.mpr ⟨hs n hn, (Finset.le_sup (f := id) hn).trans (by omega)⟩
  have hprod := Finset.prod_le_prod_of_subset_of_le_one₀ hsub
    (f := fun n : ℕ => (1 - 1 / (n : ℝ) ^ 2))
    (fun n hn => by
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [sub_nonneg, div_le_one (by positivity)]
      nlinarith)
    (fun n hn _ => sub_le_self _ (by positivity))
  rw [tel_prod N] at hprod
  apply le_trans ?_ hprod
  rw [le_div_iff₀ (by positivity)]
  push_cast
  linarith

/-! ## Step 2: the local factor for even `n` -/

/-- For even `n`, every finite product of local factors is at least one half:
the primes dividing `n` contribute 1, and the remaining ones are odd with
`p - 1 >= 2`. -/
private theorem finite_lower (n : ℕ) (he : Even n) (s : Finset Nat.Primes) :
    (1 / 2 : ℝ) ≤
      ∏ p ∈ s, (if (p : ℕ) ∣ n then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  classical
  set t := s.filter (fun p : Nat.Primes => ¬ (p : ℕ) ∣ n) with ht
  have hodd : ∀ p ∈ t, 3 ≤ (p : ℕ) := by
    intro p hp
    have hnot := (Finset.mem_filter.mp hp).2
    have he2 : 2 ∣ n := even_iff_two_dvd.mp he
    have h2 := p.property.two_le
    by_contra hlt
    push_neg at hlt
    have hpp : (p : ℕ) = 2 := by omega
    exact hnot (hpp ▸ he2)
  have hsplit :
      (∏ p ∈ s, (if (p : ℕ) ∣ n then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2)) =
        ∏ p ∈ t, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    have hmul := Finset.prod_filter_mul_prod_filter_not (s := s)
      (f := fun p : Nat.Primes =>
        (if (p : ℕ) ∣ n then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2))
      (p := fun p : Nat.Primes => (p : ℕ) ∣ n)
    simp only [← ht] at hmul
    have hone : (∏ p ∈ s.filter (fun p : Nat.Primes => (p : ℕ) ∣ n),
        (if (p : ℕ) ∣ n then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2)) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      rw [ite_eq_left (Finset.mem_filter.mp hp).2]
    rw [hone, one_mul] at hmul
    rw [← hmul]
    apply Finset.prod_congr rfl
    intro p hp
    have hnp : ¬ (p : Nat.Primes).1 ∣ n := (Finset.mem_filter.mp hp).2
    exact ite_eq_right hnp
  rw [hsplit]
  have hcast : ∀ p ∈ t, (1 - 1 / ((p : ℝ) - 1) ^ 2) =
      (1 - 1 / (((p : ℕ) - 1 : ℕ) : ℝ) ^ 2) := by
    intro p hp
    have h1 : 1 ≤ (p : ℕ) := p.property.one_le
    rw [Nat.cast_sub h1, Nat.cast_one]
  rw [Finset.prod_congr rfl hcast]
  have hbij : (∏ p ∈ t, (1 - 1 / (((p : ℕ) - 1 : ℕ) : ℝ) ^ 2)) =
      ∏ m ∈ t.image (fun p : Nat.Primes => (p : ℕ) - 1), (1 - 1 / (m : ℝ) ^ 2) := by
    refine Finset.prod_bij (fun p _ => (p : ℕ) - 1) ?_ ?_ ?_ ?_
    · intro p hp
      exact Finset.mem_image_of_mem _ hp
    · intro p hp q hq h
      apply Subtype.ext
      change (p : ℕ) - 1 = (q : ℕ) - 1 at h
      have hp3 := hodd p hp
      have hq3 := hodd q hq
      omega
    · intro m hm
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
      exact ⟨p, hp, rfl⟩
    · intro p hp
      rfl
  rw [hbij]
  exact prod_lower (t.image (fun p : Nat.Primes => (p : ℕ) - 1)) (by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    have := hodd p hp
    omega)

/-- The infinite product of local factors for even `n` is at least one half.
Either the product does not converge, in which case `tprod` is the junk value
one, or it is the limit of its finite partial products. -/
private theorem tprod_lower (n : ℕ) (he : Even n) :
    (1 / 2 : ℝ) ≤
      ∏' p : Nat.Primes, (if (p : ℕ) ∣ n then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  set f : Nat.Primes → ℝ :=
    fun p => if (p : ℕ) ∣ n then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2 with hf
  by_cases hm : Multipliable f
  · obtain ⟨a, ha⟩ := hm
    rw [ha.tprod_eq]
    exact le_hasProd_of_le_prod ha (fun s => finite_lower n he s)
  · rw [tprod_eq_one_of_not_multipliable hm]
    norm_num

/-- The second factor of the singular series, over the prime divisors of `n`,
is at least one. -/
private theorem primeFactors_prod_ge_one (n : ℕ) :
    (1 : ℝ) ≤ ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
  classical
  have hstep : (∏ p ∈ n.primeFactors, (1 : ℝ)) ≤
      ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
    apply prod_le_prod_real
    · intro p hp
      norm_num
    · intro p hp
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by
        have := Nat.prime_of_mem_primeFactors hp
        exact_mod_cast this.two_le
      have hpos : 0 ≤ 1 / ((p : ℝ) - 1) := by
        apply div_nonneg zero_le_one
        linarith
      linarith
  simpa using hstep

/-- The singular series is at least one half for every even integer. -/
private theorem singular_lower (n : ℕ) (he : Even n) :
    (1 / 2 : ℝ) ≤ LeanLab.Languasco2004.Decomp279a.singular n := by
  unfold LeanLab.Languasco2004.Decomp279a.singular
  set f : Nat.Primes → ℝ :=
    fun p => if (p : ℕ) ∣ n then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2 with hf
  have h1 : (1 / 2 : ℝ) ≤ ∏' p : Nat.Primes, f p := tprod_lower n he
  have h2 : (1 : ℝ) ≤ ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 1)) :=
    primeFactors_prod_ge_one n
  have h1' : (0 : ℝ) ≤ ∏' p : Nat.Primes, f p := by
    by_cases hm : Multipliable f
    · obtain ⟨a, ha⟩ := hm
      rw [ha.tprod_eq]
      exact le_hasProd_of_le_prod ha (fun s =>
        (by
          have := finite_lower n he s
          linarith))
    · rw [tprod_eq_one_of_not_multipliable hm]; norm_num
  have h2' : (0 : ℝ) ≤ ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by linarith
  nlinarith [mul_le_mul h1 h2 zero_le_one h1']


/-! ## Step 3: counting the h whose two von Mangoldt factors are both nonzero -/

/-- A prime power below `K` that is not itself prime is a perfect power `a ^ b`
with `2 ≤ a ≤ sqrt K` and `2 ≤ b ≤ log 2 K`. -/
private lemma primePow_bounded {K h : ℕ} (hh : h ≤ K) (hp : IsPrimePow h)
    (hnp : ¬ h.Prime) :
    ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ b ≤ Nat.log 2 K ∧ a ≤ Nat.sqrt K ∧ h = a ^ b := by
  obtain ⟨k, hklog, hkpos, p, hple, heq, hpprime⟩ := (isPrimePow_nat_iff_bounded_log h).mp hp
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hnp (by rw [heq]; simpa using hpprime)
  have hk2 : 2 ≤ k := by omega
  have hp2 : 2 ≤ p := hpprime.two_le
  have hpsq : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right (by omega : 1 ≤ p) hk2
  have h2 : p ^ 2 ≤ K := le_trans hpsq (heq ▸ hh)
  exact ⟨p, k, hp2, hk2, hklog.trans (Nat.log_mono_right hh),
    Nat.le_sqrt'.mpr h2, heq⟩

/-- The number of perfect powers `a ^ b` with `2 ≤ a ≤ sqrt K` and `2 ≤ b ≤ log 2 K`
is at most `(sqrt K + 1) * (log 2 K + 1)`. -/
private lemma card_perfect_powers_le (K : ℕ) :
    (((Finset.range (K + 1)).filter (fun h => ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧
        b ≤ Nat.log 2 K ∧ a ≤ Nat.sqrt K ∧ h = a ^ b)).card)
      ≤ (Nat.sqrt K + 1) * (Nat.log 2 K + 1) := by
  classical
  set S := (Finset.range (K + 1)).filter (fun h => ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧
      b ≤ Nat.log 2 K ∧ a ≤ Nat.sqrt K ∧ h = a ^ b) with hS
  have hsub : S ⊆ (Finset.range (Nat.sqrt K + 1) ×ˢ Finset.range (Nat.log 2 K + 1)).image
      (fun q : ℕ × ℕ => q.1 ^ q.2) := by
    intro h hh
    obtain ⟨-, a, b, ha2, hb2, hble, hale, rfl⟩ := Finset.mem_filter.mp hh
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hale),
       Finset.mem_range.mpr (Nat.lt_succ_of_le hble)⟩, rfl⟩
  calc S.card ≤ ((Finset.range (Nat.sqrt K + 1) ×ˢ Finset.range (Nat.log 2 K + 1)).image
        (fun q : ℕ × ℕ => q.1 ^ q.2)).card := Finset.card_le_card hsub
    _ ≤ (Finset.range (Nat.sqrt K + 1) ×ˢ Finset.range (Nat.log 2 K + 1)).card :=
        Finset.card_image_le
    _ = (Nat.sqrt K + 1) * (Nat.log 2 K + 1) := by
        rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-- Every member of a `pairs` set is at most its first parameter, as a real. -/
private lemma pairs_le_N {Nr Y : ℝ} {m h : ℕ} (hh : h ∈ pairs Nr Y m) : (h : ℝ) ≤ Nr := by
  unfold pairs at hh
  exact (Finset.mem_filter.mp hh).2.2.1

/-- Every member of a `pairs` set is positive and below `m`. -/
private lemma pairs_lt {Nr Y : ℝ} {m h : ℕ} (hh : h ∈ pairs Nr Y m) : 0 < h ∧ h < m :=
  Finset.mem_Ioo.mp (Finset.mem_filter.mp hh).1

/-- Every member of a `pairs` set has `m - h ≤ Y`. -/
private lemma pairs_sub_le {Nr Y : ℝ} {m h : ℕ} (hh : h ∈ pairs Nr Y m) :
    ((m - h : ℕ) : ℝ) ≤ Y :=
  (Finset.mem_filter.mp hh).2.2.2

/-- The `h` for which `h` itself is a proper prime power are few. -/
private lemma card_first_family {K : ℕ} {Nr Y : ℝ} {m : ℕ} (hNK : Nr ≤ (K : ℝ)) :
    (((pairs Nr Y m).filter (fun h => Λ h ≠ 0 ∧ ¬ h.Prime)).card)
      ≤ (Nat.sqrt K + 1) * (Nat.log 2 K + 1) := by
  classical
  apply le_trans (b := (((Finset.range (K + 1)).filter (fun h => ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧
      b ≤ Nat.log 2 K ∧ a ≤ Nat.sqrt K ∧ h = a ^ b)).card))
  · apply Finset.card_le_card
    intro h hh
    obtain ⟨hp, hne, hnp⟩ := Finset.mem_filter.mp hh
    have hle : h ≤ K := by
      have : (h : ℝ) ≤ (K : ℝ) := le_trans (pairs_le_N hp) hNK
      exact_mod_cast this
    have hpow : IsPrimePow h := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne
    obtain ⟨a, b, ha, hb, hbl, hal, hab⟩ := primePow_bounded hle hpow hnp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hle),
      ⟨a, b, ha, hb, hbl, hal, hab⟩⟩
  · exact card_perfect_powers_le K

/-- The `h` for which `m - h` is a proper prime power are few. -/
private lemma card_second_family {K : ℕ} {Nr Y : ℝ} {m : ℕ} (hNK : Nr ≤ (K : ℝ))
    (hY : Y ≤ Nr) :
    (((pairs Nr Y m).filter (fun h => Λ (m - h) ≠ 0 ∧ ¬ (m - h).Prime)).card)
      ≤ (Nat.sqrt K + 1) * (Nat.log 2 K + 1) := by
  classical
  set T := (Finset.range (K + 1)).filter (fun h => ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧
      b ≤ Nat.log 2 K ∧ a ≤ Nat.sqrt K ∧ h = a ^ b) with hT
  have hcard : T.card ≤ (Nat.sqrt K + 1) * (Nat.log 2 K + 1) := card_perfect_powers_le K
  have hinj : ∀ h₁ ∈ (pairs Nr Y m).filter (fun h => Λ (m - h) ≠ 0 ∧ ¬ (m - h).Prime),
      ∀ h₂ ∈ (pairs Nr Y m).filter (fun h => Λ (m - h) ≠ 0 ∧ ¬ (m - h).Prime),
      m - h₁ = m - h₂ → h₁ = h₂ := by
    intro h₁ h₁m h₂ h₂m heq
    have h1lt : h₁ < m := (pairs_lt (Finset.mem_filter.mp h₁m).1).2
    have h2lt : h₂ < m := (pairs_lt (Finset.mem_filter.mp h₂m).1).2
    omega
  have himg : ((pairs Nr Y m).filter (fun h => Λ (m - h) ≠ 0 ∧ ¬ (m - h).Prime)).image
      (fun h => m - h) ⊆ T := by
    intro q hq
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hp, hne, hnp⟩ := Finset.mem_filter.mp hh
    have hqK : m - h ≤ K := by
      have hsub : ((m - h : ℕ) : ℝ) ≤ Nr := le_trans (pairs_sub_le hp) hY
      have : ((m - h : ℕ) : ℝ) ≤ (K : ℝ) := le_trans hsub hNK
      exact_mod_cast this
    have hpow : IsPrimePow (m - h) := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne
    obtain ⟨a, b, ha, hb, hbl, hal, hab⟩ := primePow_bounded hqK hpow hnp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hqK),
      ⟨a, b, ha, hb, hbl, hal, hab⟩⟩
  calc ((pairs Nr Y m).filter (fun h => Λ (m - h) ≠ 0 ∧ ¬ (m - h).Prime)).card
      = (((pairs Nr Y m).filter (fun h => Λ (m - h) ≠ 0 ∧ ¬ (m - h).Prime)).image
          (fun h => m - h)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ T.card := Finset.card_le_card himg
    _ ≤ _ := hcard

/-! ## Step 4: the weighted count is small for a non Goldbach integer -/

/-- For `h` in the pairs set, both von Mangoldt factors are at most `log K`. -/
private lemma mangoldt_term_le {K : ℕ} {Nr Y : ℝ} {m h : ℕ} (hK : 1 ≤ K)
    (hNK : Nr ≤ (K : ℝ)) (hYN : Y ≤ Nr) (hh : h ∈ pairs Nr Y m) :
    Λ h * Λ (m - h) ≤ (Real.log K) ^ 2 := by
  obtain ⟨hpos, hlt⟩ := pairs_lt hh
  have hle : (h : ℝ) ≤ (K : ℝ) := le_trans (pairs_le_N hh) hNK
  have hsub : ((m - h : ℕ) : ℝ) ≤ K := le_trans (le_trans (pairs_sub_le hh) hYN) hNK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have h1 : Λ h ≤ Real.log K :=
    ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hpos) hle)
  have htrace : Λ (m - h) ≤ Real.log K := by
    rcases Nat.eq_zero_or_pos (m - h) with hz | hzp
    · rw [hz]
      have h0 : Λ (0 : ℕ) ≤ Real.log ((0 : ℕ) : ℝ) := ArithmeticFunction.vonMangoldt_le_log
      simp only [Nat.cast_zero, Real.log_zero] at h0
      linarith
    · exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hzp) hsub)
  rw [pow_two]
  exact mul_le_mul h1 htrace ArithmeticFunction.vonMangoldt_nonneg hlogK

/-- For a non Goldbach `m`, the support of the weighted count is contained in the
union of the two families of proper prime powers. -/
private lemma support_subset {Nr Y : ℝ} {m : ℕ} (hm : ¬ IsGoldbachSum m) :
    (pairs Nr Y m).filter (fun h => Λ h ≠ 0 ∧ Λ (m - h) ≠ 0) ⊆
      (pairs Nr Y m).filter (fun h => Λ h ≠ 0 ∧ ¬ h.Prime) ∪
      (pairs Nr Y m).filter (fun h => Λ (m - h) ≠ 0 ∧ ¬ (m - h).Prime) := by
  intro h hh
  obtain ⟨hp, hne1, hne2⟩ := Finset.mem_filter.mp hh
  have hlt : h < m := (pairs_lt hp).2
  by_cases h1 : h.Prime
  · refine Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp, hne2, ?_⟩))
    intro h2
    exact hm ⟨h, m - h, h1, h2, by omega⟩
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp, hne1, h1⟩))

/-- The weighted count of a non Goldbach integer is at most twice the number of
proper prime powers below `K`, times `(log K)^2`. -/
private lemma weighted_le {K : ℕ} {Nr Y : ℝ} {m : ℕ} (hK : 1 ≤ K)
    (hNK : Nr ≤ (K : ℝ)) (hY : Y ≤ Nr) (hm : ¬ IsGoldbachSum m) :
    weightedCount Nr Y m ≤
      2 * ((Nat.sqrt K + 1) * (Nat.log 2 K + 1) : ℕ) * (Real.log K) ^ 2 := by
  classical
  set supp := (pairs Nr Y m).filter (fun h => Λ h ≠ 0 ∧ Λ (m - h) ≠ 0) with hsupp
  set A := (pairs Nr Y m).filter (fun h => Λ h ≠ 0 ∧ ¬ h.Prime) with hA
  set B := (pairs Nr Y m).filter (fun h => Λ (m - h) ≠ 0 ∧ ¬ (m - h).Prime) with hB
  have hsupp_eq : weightedCount Nr Y m = ∑ h ∈ supp, Λ h * Λ (m - h) := by
    unfold weightedCount
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro h hpair hnotin
    have hp : ¬ (Λ h ≠ 0 ∧ Λ (m - h) ≠ 0) :=
      fun hc => hnotin (Finset.mem_filter.mpr ⟨hpair, hc⟩)
    rcases not_and_or.mp hp with h0 | h0
    · rw [not_not.mp h0, zero_mul]
    · rw [not_not.mp h0, mul_zero]
  have hterm : ∀ h ∈ supp, Λ h * Λ (m - h) ≤ (Real.log K) ^ 2 :=
    fun h hh => mangoldt_term_le hK hNK hY (Finset.mem_filter.mp hh).1
  have hsum : ∑ h ∈ supp, Λ h * Λ (m - h) ≤ (supp.card : ℝ) * (Real.log K) ^ 2 := by
    have hconst : ∑ _h ∈ supp, (Real.log K) ^ 2 = (supp.card : ℝ) * (Real.log K) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← hconst]
    exact Finset.sum_le_sum hterm
  have hcard : (supp.card : ℝ) ≤ 2 * ((Nat.sqrt K + 1) * (Nat.log 2 K + 1) : ℕ) := by
    have hsub := support_subset (Y := Y) (Nr := Nr) hm
    rw [← hsupp, ← hA, ← hB] at hsub
    have h1 : supp.card ≤ (A ∪ B).card := Finset.card_le_card hsub
    have h2 : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le _ _
    have h3 : A.card ≤ (Nat.sqrt K + 1) * (Nat.log 2 K + 1) := card_first_family hNK
    have h4 : B.card ≤ (Nat.sqrt K + 1) * (Nat.log 2 K + 1) := card_second_family hNK hY
    have h5 : supp.card ≤ 2 * ((Nat.sqrt K + 1) * (Nat.log 2 K + 1)) := by omega
    exact_mod_cast h5
  have hstep : (supp.card : ℝ) * (Real.log K) ^ 2 ≤
      (2 * ((Nat.sqrt K + 1) * (Nat.log 2 K + 1) : ℕ) : ℝ) * (Real.log K) ^ 2 :=
    mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
  rw [hsupp_eq]
  exact le_trans hsum hstep

/-! ## Step 5: the pairs set is large -/

/-- The pairs set of a window element has at least `Y - H - 2` members. -/
private lemma card_pairs_ge {Nr H Y : ℝ} {m : ℕ} (hN : 1 ≤ Nr) (hH : 0 < H)
    (hYH : H + 1 ≤ Y) (hYN : Y ≤ Nr)
    (hmgt : Nat.floor Nr < m) (hmle : (m : ℝ) ≤ Nr + H) :
    Y - H - 2 ≤ ((pairs Nr Y m).card : ℝ) := by
  classical
  set L := Nat.floor Nr with hL
  set A := max 1 (Nat.ceil (Nr + H - Y)) with hA
  have hsub : Finset.Icc A L ⊆ pairs Nr Y m := by
    intro h hh
    obtain ⟨hAh, hhL⟩ := Finset.mem_Icc.mp hh
    have hA1 : 1 ≤ h := le_trans (le_max_left _ _) hAh
    have hceil : (Nr + H - Y) ≤ (Nat.ceil (Nr + H - Y) : ℝ) := Nat.le_ceil _
    have hAle : (Nat.ceil (Nr + H - Y) : ℝ) ≤ (h : ℝ) := by
      exact_mod_cast (le_trans (le_max_right _ _) hAh)
    have h1 : Nr + H - Y ≤ (h : ℝ) := le_trans hceil hAle
    have hLle : (h : ℝ) ≤ (L : ℝ) := by exact_mod_cast hhL
    have hLleN : (L : ℝ) ≤ Nr := Nat.floor_le (by positivity)
    have hmax : max 1 (Nr + H - Y) ≤ (h : ℝ) := by
      apply max_le
      · exact_mod_cast hA1
      · exact h1
    have hgt : Nr - Y < max 1 (Nr + H - Y) := by
      by_cases hc : (Nr + H - Y) ≤ 1
      · rw [max_eq_left hc]; linarith
      · push_neg at hc
        rw [max_eq_right hc.le]; linarith
    have hlt : h < m := by
      have hlt' : (h : ℝ) < (m : ℝ) := lt_of_le_of_lt hLle (by exact_mod_cast hmgt)
      exact_mod_cast hlt'
    have hmh : ((m - h : ℕ) : ℝ) ≤ Y := by
      rw [Nat.cast_sub (le_of_lt hlt)]
      linarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hA1, hlt⟩,
      by linarith, le_trans hLle hLleN, hmh⟩
  have hAL : A ≤ L := by
    have h1 : 1 ≤ L := by
      apply Nat.le_floor
      exact_mod_cast hN
    have h2 : Nat.ceil (Nr + H - Y) ≤ L := by
      apply Nat.ceil_le.mpr
      have hNl : Nr - 1 ≤ (L : ℝ) := by
        have := Nat.lt_floor_add_one Nr
        linarith
      linarith
    exact max_le h1 h2
  have hcard : L + 1 - A ≤ (pairs Nr Y m).card := by
    simpa only [Nat.card_Icc] using Finset.card_le_card hsub
  have hAub : (A : ℝ) ≤ max 1 (Nr + H - Y + 1) := by
    rw [hA]
    push_cast
    apply max_le
    · exact le_max_left _ _
    · by_cases hc : (0 : ℝ) ≤ Nr + H - Y
      · have := Nat.ceil_lt_add_one hc
        push_cast at this
        linarith [le_max_right (1 : ℝ) (Nr + H - Y + 1)]
      · push_neg at hc
        have hz : Nat.ceil (Nr + H - Y) = 0 :=
          Nat.eq_zero_of_le_zero (Nat.ceil_le.mpr (by push_cast; linarith))
        rw [hz]
        push_cast
        linarith [le_max_left (1 : ℝ) (Nr + H - Y + 1)]
  have hLlb : Nr - 1 ≤ (L : ℝ) := by
    have := Nat.lt_floor_add_one Nr
    linarith
  have hreal : ((L + 1 - A : ℕ) : ℝ) = (L : ℝ) + 1 - (A : ℝ) := by
    rw [Nat.cast_sub (by omega : A ≤ L + 1)]
    push_cast
    ring
  have hfin : Y - H - 2 ≤ ((L + 1 - A : ℕ) : ℝ) := by
    rw [hreal]
    by_cases hc : 1 ≤ Nr + H - Y + 1
    · rw [max_eq_right hc] at hAub
      linarith
    · push_neg at hc
      rw [max_eq_left hc.le] at hAub
      linarith
  exact le_trans hfin (by exact_mod_cast hcard)

/-! ## Step 6: the elementary size comparison -/

/-- `log x ≤ 100 x ^ (1/100)` for `x ≥ 1`. -/
private lemma log_le_rpow_100 {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 100 * x ^ (1 / 100 : ℝ) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hu1 : (1 : ℝ) ≤ x ^ (1 / 100 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hu0 : (0 : ℝ) < x ^ (1 / 100 : ℝ) := lt_of_lt_of_le one_pos hu1
  have hlog : Real.log x = 100 * Real.log (x ^ (1 / 100 : ℝ)) := by
    rw [Real.log_rpow hx0]
    ring
  have hsub := Real.log_le_sub_one_of_pos hu0
  have hu : Real.log (x ^ (1 / 100 : ℝ)) ≤ x ^ (1 / 100 : ℝ) := by linarith
  rw [hlog]
  nlinarith

/-- The size comparison: beyond an explicit threshold, twice the prime power
count times `(log N)^2` is at most `N ^ (7/12)` over one thousand and twenty four. -/
private lemma bound_eventually :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 * (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) * (Real.log N) ^ 2 ≤
        (N : ℝ) ^ (7 / 12 : ℝ) / 1024 := by
  refine ⟨10 ^ 250, fun N hN => ?_⟩
  set x : ℝ := (N : ℝ) with hxdef
  have hxN : (10 : ℝ) ^ 250 ≤ x := by
    rw [hxdef]
    have h1 : ((10 ^ 250 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : ((10 ^ 250 : ℕ) : ℝ) = (10 : ℝ) ^ 250 := by push_cast; ring
    linarith
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hxN
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hH1 : Real.log x ≤ 100 * x ^ (1 / 100 : ℝ) := log_le_rpow_100 hx1
  have hsqrt : ((Nat.sqrt N : ℝ) + 1) ≤ 2 * x ^ (1 / 2 : ℝ) := by
    have hsq : ((Nat.sqrt N : ℝ)) ^ 2 ≤ x := by
      rw [hxdef]
      have := Nat.sqrt_le' N
      exact_mod_cast this
    have hle : (Nat.sqrt N : ℝ) ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hsq
    have hrw : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
    have hone : (1 : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
      rw [← hrw]; exact Real.one_le_sqrt.mpr hx1
    have : (Nat.sqrt N : ℝ) ≤ x ^ (1 / 2 : ℝ) := by rw [← hrw]; exact hle
    linarith
  have hlog2N : ((Nat.log 2 N : ℝ) + 1) ≤ 4 * Real.log x := by
    have hpow : (2 : ℝ) ^ (Nat.log 2 N) ≤ x := by
      rw [hxdef]
      have h1 : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
      have h2 : ((2 ^ Nat.log 2 N : ℕ) : ℝ) = (2 : ℝ) ^ (Nat.log 2 N) := by push_cast; ring
      rw [← h2]
      exact_mod_cast h1
    have hlog2pos : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hlog : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log x := by
      have hpos2 : (0:ℝ) < (2:ℝ) ^ (Nat.log 2 N) := by positivity
      have h1 := Real.log_le_log hpos2 hpow
      rw [Real.log_pow] at h1
      exact h1
    have hL1 : (0.6931471803 : ℝ) ≤ Real.log x := by
      have h3 : (2:ℝ) ≤ x := by nlinarith
      have := Real.log_le_log (by norm_num : (0:ℝ) < 2) h3
      linarith
    have hstep : (Nat.log 2 N : ℝ) ≤ Real.log x / 0.6931471803 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    nlinarith
  have hS : (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) ≤
      8 * x ^ (1 / 2 : ℝ) * Real.log x := by
    push_cast
    nlinarith [hsqrt, hlog2N, hL0]
  have hL3 : (Real.log x) ^ 3 ≤ 10 ^ 6 * x ^ (3 / 100 : ℝ) := by
    have h1 : (Real.log x) ^ 3 ≤ (100 * x ^ (1 / 100 : ℝ)) ^ 3 := by
      apply pow_le_pow_left₀ hL0 hH1
    have h2 : (100 * x ^ (1 / 100 : ℝ)) ^ 3 = 10 ^ 6 * x ^ (3 / 100 : ℝ) := by
      have h3 : (x ^ (1 / 100 : ℝ)) ^ 3 = x ^ (3 / 100 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hx0)]
        norm_num
      calc (100 * x ^ (1 / 100 : ℝ)) ^ 3
          = 100 ^ 3 * (x ^ (1 / 100 : ℝ)) ^ 3 := by ring
        _ = 10 ^ 6 * x ^ (3 / 100 : ℝ) := by rw [h3]; norm_num
    linarith
  have hmid : 2 * (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) * (Real.log x) ^ 2 ≤
      16 * x ^ (1 / 2 : ℝ) * (Real.log x) ^ 3 := by
    nlinarith [hS, hL0, sq_nonneg (Real.log x)]
  have hfin : 16 * x ^ (1 / 2 : ℝ) * (Real.log x) ^ 3 ≤
      16 * x ^ (1 / 2 : ℝ) * (10 ^ 6 * x ^ (3 / 100 : ℝ)) := by
    have h2 : (0:ℝ) ≤ 16 * x ^ (1 / 2 : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hL3 h2
  have hcomb : 16 * x ^ (1 / 2 : ℝ) * (10 ^ 6 * x ^ (3 / 100 : ℝ)) =
      16 * 10 ^ 6 * x ^ (53 / 100 : ℝ) := by
    have hsum : x ^ (1 / 2 : ℝ) * x ^ (3 / 100 : ℝ) = x ^ (53 / 100 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    calc 16 * x ^ (1 / 2 : ℝ) * (10 ^ 6 * x ^ (3 / 100 : ℝ))
        = 16 * 10 ^ 6 * (x ^ (1 / 2 : ℝ) * x ^ (3 / 100 : ℝ)) := by ring
      _ = 16 * 10 ^ 6 * x ^ (53 / 100 : ℝ) := by rw [hsum]
  have hkey : (16 * 10 ^ 6 : ℝ) * x ^ (53 / 100 : ℝ) ≤ x ^ (7 / 12 : ℝ) / 1024 := by
    have hpos : (0:ℝ) < x ^ (53 / 100 : ℝ) := Real.rpow_pos_of_pos hx0 (53 / 100)
    have hsplit : x ^ (7 / 12 : ℝ) = x ^ (53 / 100 : ℝ) * x ^ (4 / 75 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    have hbig : (1.6384 * 10 ^ 10 : ℝ) ≤ x ^ (4 / 75 : ℝ) := by
      have hmono : ((10 : ℝ) ^ 250) ^ (4 / 75 : ℝ) ≤ x ^ (4 / 75 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hxN (by norm_num)
      have hval : ((10 : ℝ) ^ 250) ^ (4 / 75 : ℝ) = (10 : ℝ) ^ (40 / 3 : ℝ) := by
        rw [← Real.rpow_natCast (10 : ℝ) 250]
        rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10)]
        norm_num
      have hlow : (10 : ℝ) ^ (13 : ℝ) ≤ (10 : ℝ) ^ (40 / 3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have hnum : (1.6384 * 10 ^ 10 : ℝ) ≤ (10 : ℝ) ^ (13 : ℝ) := by norm_num
      rw [hval] at hmono
      linarith
    have hmul : (1.6384 * 10 ^ 10 : ℝ) * x ^ (53 / 100 : ℝ) ≤
        x ^ (4 / 75 : ℝ) * x ^ (53 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_right hbig hpos.le
    rw [hsplit]
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1024)]
    nlinarith [hmul]
  calc 2 * (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) * (Real.log N) ^ 2
      = 2 * (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) : ℕ) : ℝ) * (Real.log x) ^ 2 := by
        rw [hxdef]
    _ ≤ 16 * x ^ (1 / 2 : ℝ) * (Real.log x) ^ 3 := hmid
    _ ≤ 16 * x ^ (1 / 2 : ℝ) * (10 ^ 6 * x ^ (3 / 100 : ℝ)) := hfin
    _ = 16 * 10 ^ 6 * x ^ (53 / 100 : ℝ) := hcomb
    _ ≤ x ^ (7 / 12 : ℝ) / 1024 := hkey
    _ = (N : ℝ) ^ (7 / 12 : ℝ) / 1024 := by rw [hxdef]

/-- LEAF. Page 42 after Theorem 2 and page 44 after display 3.
For an even non Goldbach integer, the singular main term dominates the
contribution of proper prime powers. This is a pointwise lower bound for the
squared representation error, with no average estimate. -/
theorem exception_error_lower :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ → ∃ c N₀ : ℝ, 0 < c ∧ ∀ N : ℝ, N₀ ≤ N → ∀ m ∈ window N η,
      ¬ IsGoldbachSum m → c * localization N η ^ 2 ≤ fullError N η m ^ 2 := by
  obtain ⟨K₀, hK₀⟩ := bound_eventually
  refine ⟨1 / 100, by norm_num, fun η hη0 hηsmall => ?_⟩
  have hη100 : η ≤ 1 / 100 := le_of_lt hηsmall
  refine ⟨1 / 1024, max (K₀ : ℝ) 100, by norm_num, fun N hN m hmwin hgold => ?_⟩
  have hN100 : (100 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hNK₀ : (K₀ : ℝ) ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hY0 : 0 < localization N η := Real.rpow_pos_of_pos hN0 _
  have hH0 : 0 < windowLength N η := Real.rpow_pos_of_pos hN0 _
  obtain ⟨hmIoc, hmEven⟩ := Finset.mem_filter.mp hmwin
  have hmgt : ⌊N⌋₊ < m := (Finset.mem_Ioc.mp hmIoc).1
  have hmup : m ≤ ⌊N + windowLength N η⌋₊ := (Finset.mem_Ioc.mp hmIoc).2
  have hmle : (m : ℝ) ≤ N + windowLength N η := by
    have h1 : (m : ℝ) ≤ (⌊N + windowLength N η⌋₊ : ℝ) := by exact_mod_cast hmup
    have h2 : (⌊N + windowLength N η⌋₊ : ℝ) ≤ N + windowLength N η :=
      Nat.floor_le (by have := hH0; linarith)
    linarith
  -- the localization parameter is at most `N`, so the assumptions of the counts hold
  have hYleN : localization N η ≤ N := by
    have h : localization N η ≤ N ^ (1 : ℝ) := by
      rw [localization]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    rwa [Real.rpow_one] at h
  have hN712leY : N ^ (7 / 12 : ℝ) ≤ localization N η := by
    rw [localization]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  -- the window is much shorter than the localization
  have hgap : lengthExponent η + 1 / 3 ≤ 7 / 12 + η := by
    unfold lengthExponent
    nlinarith
  have hcube : (2 : ℝ) ≤ N ^ (1 / 3 : ℝ) := by
    have h3 : (1 : ℝ) / 3 = (3 : ℝ)⁻¹ := by norm_num
    rw [h3, Real.le_rpow_inv_iff_of_pos (by norm_num) (le_of_lt hN0) (by norm_num : (0:ℝ) < 3)]
    norm_num
    linarith
  have hHhalf : windowLength N η ≤ localization N η / 2 := by
    have hprod : windowLength N η * N ^ (1 / 3 : ℝ) ≤ localization N η := by
      rw [windowLength, localization, lengthExponent, ← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1 hgap
    have h2 : windowLength N η * 2 ≤ windowLength N η * N ^ (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hcube (le_of_lt hH0)
    linarith
  have hY8 : (8 : ℝ) ≤ localization N η := by
    have h1 : (100 : ℝ) ^ (7 / 12 : ℝ) ≤ localization N η := by
      rw [localization]
      calc (100 : ℝ) ^ (7 / 12 : ℝ) ≤ N ^ (7 / 12 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) hN100 (by norm_num)
        _ ≤ N ^ (7 / 12 + η) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h2 : (8 : ℝ) ≤ (100 : ℝ) ^ (7 / 12 : ℝ) := by
      have h10 : (100 : ℝ) ^ (1 / 2 : ℝ) = 10 := by
        rw [← Real.sqrt_eq_rpow]
        norm_num
      calc (8 : ℝ) ≤ 10 := by norm_num
        _ = (100 : ℝ) ^ (1 / 2 : ℝ) := h10.symm
        _ ≤ (100 : ℝ) ^ (7 / 12 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    linarith
  have hYH : windowLength N η + 1 ≤ localization N η := by linarith
  -- the pairs set is large
  have hcp := card_pairs_ge (Nr := N) (H := windowLength N η) (Y := localization N η) (m := m)
    hN1 hH0 hYH hYleN hmgt hmle
  have hpair4 : localization N η / 4 ≤ ((pairs N (localization N η) m).card : ℝ) := by linarith
  -- the singular series is bounded below
  have hsing : (1 : ℝ) / 2 ≤ LeanLab.Languasco2004.Decomp279a.singular m := singular_lower m hmEven
  -- the weighted count is small
  have hK1 : 1 ≤ Nat.ceil N := by
    have h : (1 : ℝ) ≤ (Nat.ceil N : ℝ) := le_trans hN1 (Nat.le_ceil N)
    exact_mod_cast h
  have hNK : N ≤ ((Nat.ceil N : ℕ) : ℝ) := Nat.le_ceil N
  have hK0le : K₀ ≤ Nat.ceil N := by
    have h : (K₀ : ℝ) ≤ ((Nat.ceil N : ℕ) : ℝ) := le_trans hNK₀ hNK
    exact_mod_cast h
  have hw := weighted_le (K := Nat.ceil N) (Nr := N) (Y := localization N η) (m := m)
    hK1 hNK hYleN hgold
  have hKb := hK₀ (Nat.ceil N) hK0le
  have hwu : weightedCount N (localization N η) m ≤
      ((Nat.ceil N : ℕ) : ℝ) ^ (7 / 12 : ℝ) / 1024 := le_trans hw hKb
  have hceilb : ((Nat.ceil N : ℕ) : ℝ) ≤ N + 1 :=
    (Nat.ceil_lt_add_one (le_of_lt hN0)).le
  have hceil712 : ((Nat.ceil N : ℕ) : ℝ) ^ (7 / 12 : ℝ) ≤ 2 * N ^ (7 / 12 : ℝ) := by
    have h1 : ((Nat.ceil N : ℕ) : ℝ) ^ (7 / 12 : ℝ) ≤ (N + 1) ^ (7 / 12 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hceilb (by norm_num)
    have h2 : (N + 1) ^ (7 / 12 : ℝ) ≤ (2 * N) ^ (7 / 12 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have h3 : (2 * N) ^ (7 / 12 : ℝ) = 2 ^ (7 / 12 : ℝ) * N ^ (7 / 12 : ℝ) :=
      Real.mul_rpow (by norm_num) (le_of_lt hN0)
    have h4 : (2 : ℝ) ^ (7 / 12 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (7 / 12 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    calc ((Nat.ceil N : ℕ) : ℝ) ^ (7 / 12 : ℝ) ≤ (N + 1) ^ (7 / 12 : ℝ) := h1
      _ ≤ (2 * N) ^ (7 / 12 : ℝ) := h2
      _ = 2 ^ (7 / 12 : ℝ) * N ^ (7 / 12 : ℝ) := h3
      _ ≤ 2 * N ^ (7 / 12 : ℝ) := mul_le_mul_of_nonneg_right h4 (by positivity)
  have hwY : weightedCount N (localization N η) m ≤ localization N η / 512 := by
    have : ((Nat.ceil N : ℕ) : ℝ) ^ (7 / 12 : ℝ) / 1024 ≤ 2 * N ^ (7 / 12 : ℝ) / 1024 := by
      linarith [hceil712]
    have h : 2 * N ^ (7 / 12 : ℝ) / 1024 ≤ localization N η / 512 := by
      linarith [hN712leY]
    linarith
  -- the pointwise lower bound
  have hprod2 : localization N η / 8 ≤
      LeanLab.Languasco2004.Decomp279a.singular m * ((pairs N (localization N η) m).card : ℝ) := by
    have h1 : (1 : ℝ) / 2 * (localization N η / 4) ≤
        LeanLab.Languasco2004.Decomp279a.singular m * ((pairs N (localization N η) m).card : ℝ) :=
      mul_le_mul hsing hpair4 (by linarith) (by linarith [hsing])
    linarith
  have hfull : fullError N η m ≤ -(localization N η) / 16 := by
    unfold fullError unweightedCount
    nlinarith [hwY, hprod2, hY0]
  have hsq : (localization N η / 16) ^ 2 ≤ fullError N η m ^ 2 := by
    nlinarith [hfull, hY0]
  calc (1 / 1024 : ℝ) * localization N η ^ 2 ≤ (localization N η / 16) ^ 2 := by nlinarith [hY0]
    _ ≤ fullError N η m ^ 2 := hsq

/-- Page 44 display 1: the square of the norm of a sum is at most twice
 the sum of the squared norms. -/
theorem norm_add_sq (z w : ℂ) : ‖z + w‖ ^ 2 ≤ 2 * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
  have h := norm_add_le z w
  have h0 := norm_nonneg (z + w)
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

/-- Page 44 displays 1, 3, 4 and 5: combine the major and minor estimates.
CONDITIONAL ON major_bound, minor_bound and fourier_split. -/
theorem mean_square :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∑ m ∈ window N η, fullError N η m ^ 2 ≤
        C * windowLength N η * localization N η ^ 2 / Real.log N ^ A := by
  obtain ⟨η₁, he₁, hmaj⟩ := major_bound
  obtain ⟨η₂, he₂, hmin⟩ := minor_bound
  refine ⟨min η₁ η₂, lt_min he₁ he₂, ?_⟩
  intro η A hη hηsmall hA
  obtain ⟨C₁, N₁, h₁⟩ := hmaj η A hη (hηsmall.trans_le (min_le_left _ _)) hA
  obtain ⟨C₂, N₂, h₂⟩ := hmin η A hη (hηsmall.trans_le (min_le_right _ _)) hA
  refine ⟨2 * (C₁ + C₂), max 3 (max N₁ N₂), ?_⟩
  intro N hN
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hpoint : ∀ m ∈ window N η, fullError N η m ^ 2 ≤
      2 * (‖majorError N η A m‖ ^ 2 +
      ‖minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2) := by
    intro m _
    have h := norm_add_sq (majorError N η A m)
      (minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m)
    rw [← fourier_split N η A hN3 hη m, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    exact h
  calc ∑ m ∈ window N η, fullError N η m ^ 2
      ≤ ∑ m ∈ window N η, 2 * (‖majorError N η A m‖ ^ 2 +
          ‖minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2) :=
        Finset.sum_le_sum hpoint
    _ = 2 * ((∑ m ∈ window N η, ‖majorError N η A m‖ ^ 2) +
          ∑ m ∈ window N η,
            ‖minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 * (C₁ * windowLength N η * localization N η ^ 2 / Real.log N ^ A +
          C₂ * windowLength N η * localization N η ^ 2 / Real.log N ^ A) := by
        gcongr
        · exact h₁ N hN1
        · exact h₂ N hN2
    _ = _ := by ring

/-- Page 42 Theorem 2 from the mean square and the pointwise exception bound.
CONDITIONAL ON the four OPEN leaves of this file. -/
theorem local_exception_bound :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((Ioc ⌊N⌋₊ ⌊N + windowLength N η⌋₊).filter
        (fun m => Even m ∧ ¬ IsGoldbachSum m)).card : ℝ) ≤
      C * windowLength N η / Real.log N ^ A := by
  obtain ⟨η₁, he₁, hmeanAll⟩ := mean_square
  obtain ⟨η₂, he₂, hlowerAll⟩ := exception_error_lower
  refine ⟨min η₁ η₂, lt_min he₁ he₂, ?_⟩
  intro η A hη hηsmall hA
  obtain ⟨C, N₁, hmean⟩ := hmeanAll η A hη (hηsmall.trans_le (min_le_left _ _)) hA
  obtain ⟨c, N₂, hc, hlower⟩ := hlowerAll η hη (hηsmall.trans_le (min_le_right _ _))
  refine ⟨C / c, max 3 (max N₁ N₂), ?_⟩
  intro N hN
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let bad := (window N η).filter (fun m => ¬ IsGoldbachSum m)
  have hpoint : ∀ m ∈ window N η,
      (if ¬ IsGoldbachSum m then c * localization N η ^ 2 else 0) ≤ fullError N η m ^ 2 := by
    intro m hm
    split_ifs with h
    · positivity
    · exact hlower N hN2 m hm h
  have hsum := (Finset.sum_le_sum hpoint).trans (hmean N hN1)
  have hsum' : (bad.card : ℝ) * (c * localization N η ^ 2) ≤
      C * windowLength N η * localization N η ^ 2 / Real.log N ^ A := by
    simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, bad] using hsum
  have hY : 0 < localization N η ^ 2 := by
    apply sq_pos_of_pos
    exact Real.rpow_pos_of_pos (by linarith) _
  have hL : 0 < Real.log N ^ A := Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
  have hcancel : (bad.card : ℝ) * c ≤ C * windowLength N η / Real.log N ^ A := by
    apply (mul_le_mul_iff_left₀ hY).mp
    calc (bad.card : ℝ) * c * localization N η ^ 2
        = (bad.card : ℝ) * (c * localization N η ^ 2) := by ring
      _ ≤ C * windowLength N η * localization N η ^ 2 / Real.log N ^ A := hsum'
      _ = (C * windowLength N η / Real.log N ^ A) * localization N η ^ 2 := by ring
  have hresult : (bad.card : ℝ) ≤ C / c * windowLength N η / Real.log N ^ A := by
    have hdiv := (le_div_iff₀ hc).mpr hcancel
    convert hdiv using 1 <;> ring
  convert hresult using 1
  congr 2
  ext m
  simp [bad, window, and_assoc]

/-- The exact sealed statement of EncA.perelliPintz1993.
CONDITIONAL ON the four OPEN leaves here and Decomp279a.extend_windows. -/
theorem perelliPintz1993_from_leaves : Theorem1_6 := by
  intro ε hε _
  let b : ℝ := min (7 / 36 + ε) (1 / 2)
  obtain ⟨η₀, he₀, hlocal⟩ := local_exception_bound
  let η : ℝ := min (min (ε / 4) (1 / 2000)) (η₀ / 2)
  have hη : 0 < η := lt_min (lt_min (by positivity) (by norm_num)) (by positivity)
  have hηsmall : η < η₀ := (min_le_right _ _).trans_lt (by linarith)
  have hηε : η ≤ ε / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hηcap : η ≤ 1 / 2000 := (min_le_left _ _).trans (min_le_right _ _)
  have ha : 0 < lengthExponent η := by unfold lengthExponent; positivity
  have hab : lengthExponent η < b := by
    apply lt_min <;> unfold lengthExponent <;> nlinarith
  have hb : b < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hext := Decomp279a.extend_windows (fun n => Even n ∧ ¬ IsGoldbachSum n)
    (lengthExponent η) b ha hab hb (fun A hA => by
      obtain ⟨C, N₀, hC⟩ := hlocal η A hη hηsmall hA
      refine ⟨C, N₀, ?_⟩
      intro N hN
      convert hC N hN using 1 <;> unfold windowLength <;> congr 2 <;> ext n <;> simp)
  apply LogFrom_mono (r := b) (min_le_left _ _)
  intro A hA
  obtain ⟨C, X₀, hC⟩ := hext A hA
  refine ⟨C, X₀, ?_⟩
  intro X H hX hH hHu
  convert hC X H hX hH hHu using 1
  unfold LeanLab.LanguascoPerelli1996.EH
  congr 2
  ext n
  simp

#print axioms major_bound
#print axioms minor_bound
#print axioms fourier_split
#print axioms exception_error_lower
#print axioms norm_add_sq
#print axioms mean_square
#print axioms local_exception_bound
#print axioms perelliPintz1993_from_leaves
end
end LeanLab.Languasco2004.Decomp279b
