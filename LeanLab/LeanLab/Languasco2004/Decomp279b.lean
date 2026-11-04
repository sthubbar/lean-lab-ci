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

/-- LEAF. Page 42 after Theorem 2 and page 44 after display 3.
For an even non Goldbach integer, the singular main term dominates the
contribution of proper prime powers. This is a pointwise lower bound for the
squared representation error, with no average estimate. -/
theorem exception_error_lower :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ → ∃ c N₀ : ℝ, 0 < c ∧ ∀ N : ℝ, N₀ ≤ N → ∀ m ∈ window N η,
      ¬ IsGoldbachSum m → c * localization N η ^ 2 ≤ fullError N η m ^ 2 := by sorry

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
