/-
Perelli and Pintz 1993, pages 42 to 48.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
Reassemble the exact cited statement using the new smaller leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp413a
import LeanLab.Languasco2004.Decomp413b

namespace LeanLab.Languasco2004.PPAssembly413
open Finset Real Decomp279b LeanLab.Languasco2004.EncA
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 44 displays 1, 3, 4 and 5: combine the major and minor estimates.
CONDITIONAL ON the five OPEN leaves in Decomp413a and Decomp413b.
The Fourier split is already proved on main. -/
theorem mean_square_from_parts :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∑ m ∈ window N η, fullError N η m ^ 2 ≤
        C * windowLength N η * localization N η ^ 2 / Real.log N ^ A := by
  obtain ⟨η₁, he₁, hmaj⟩ := Decomp413b.major_bound_from_parts
  obtain ⟨η₂, he₂, hmin⟩ := Decomp413a.minor_bound_from_parts
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
CONDITIONAL ON the five OPEN leaves in Decomp413a and Decomp413b.
The pointwise exception lower bound is already proved on main. -/
theorem local_exception_bound_from_parts :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((Ioc ⌊N⌋₊ ⌊N + windowLength N η⌋₊).filter
        (fun m => Even m ∧ ¬ IsGoldbachSum m)).card : ℝ) ≤
      C * windowLength N η / Real.log N ^ A := by
  obtain ⟨η₁, he₁, hmeanAll⟩ := mean_square_from_parts
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
CONDITIONAL ON the five OPEN leaves in Decomp413a and Decomp413b.
Decomp279a.extend_windows is already proved on main. -/
theorem perelliPintz1993_from_parts : Theorem1_6 := by
  intro ε hε _
  let b : ℝ := min (7 / 36 + ε) (1 / 2)
  obtain ⟨η₀, he₀, hlocal⟩ := local_exception_bound_from_parts
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

#print axioms mean_square_from_parts
#print axioms local_exception_bound_from_parts
#print axioms perelliPintz1993_from_parts
end
end LeanLab.Languasco2004.PPAssembly413
