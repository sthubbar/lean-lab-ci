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

/-- LEAF. Page 44 display 1, before applying Cauchy Schwarz.
Fourier orthogonality and the partition of the period give the coefficient identity. -/
theorem fourier_split (N η A : ℝ) (hN : 3 ≤ N) (hη : 0 < η) (m : ℕ) :
    (fullError N η m : ℂ) = majorError N η A m +
      minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m := by sorry

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
