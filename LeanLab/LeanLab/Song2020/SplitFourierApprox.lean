/-
SPLIT of `LeanLab.Song2020.Decomp139.fourier_approximation`, PREP 2026-11-21.
Source: Y. Song, arXiv 2012.06322 v1, papers/P0078.pdf. Lemma 1 on printed page 3;
the S2 estimate on printed pages 4 and 5, from the display after "By Lemma 3.1, we have"
through "Concluding the above estimate, we have S2 << H^(1/2) n^(1-γ/2) + H^(-1) y n^(1-γ)".
Lemma 1 is already PROVED on main as
`Repair591FourierMajorant.song_lemma1_majorant591` and is used here, not restated.
The remaining cited input is Graham and Kolesnik, display 3.3.4, the exponent pair 1/2, 1/2.
The original statement is not restated: the assembly proves its exact type.
AI wrote the Lean code. Not compiled in this design unit. Binary Goldbach is open.
-/
import LeanLab.Song2020.Decomp139
import LeanLab.Song2020.Repair591FourierMajorant

namespace LeanLab.Song2020.SplitFourierApprox

open LeanLab.Song2020 LeanLab.Song2020.State1562 LeanLab.Song2020.Decomp139
open scoped Classical

noncomputable section

/-- The real trigonometric majorant of Lemma 1 at truncation level H. -/
def majorant (b : ℕ → ℤ → ℂ) (H : ℕ) (x : ℝ) : ℝ :=
  (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b H h * eC (x * h)).re

/-- The Lemma 1 coefficients cut to the frequencies the truncated sum uses. -/
def truncCoeff (a : ℕ → ℤ → ℂ) (H : ℕ) (h : ℤ) : ℂ :=
  if |h| ≤ (H : ℤ) then a H h else 0

/-- Page 4, Graham and Kolesnik display 3.3.4 with the exponent pair 1/2, 1/2, in the form
Song uses: the sum of e of h x to the gamma over an initial segment of the window is at most
a constant times h to the 1/2 n to the gamma over 2 plus h inverse n to the 1 minus gamma. -/
def ExponentPairHalf (γ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ, 0 < y → y ≤ (n : ℝ) / 3 →
    ∀ h : ℕ, 1 ≤ h → ∀ t : ℝ,
      ‖∑ m ∈ subWindow n y t, eC ((h : ℝ) * (m : ℝ) ^ γ)‖ ≤
        C * ((h : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) + (h : ℝ)⁻¹ * (n : ℝ) ^ (1 - γ))

/-- LEAF. Page 4, the display splitting the sawtooth sum into S1 plus S2: at each prime the
sawtooth difference minus its truncated Fourier difference is at most the Lemma 1 majorant
at both points, and the weight times the additive character has modulus the weight.
Elementary: triangle inequality and the modulus of e. -/
theorem leaf_saw_window_triangle (γ : ℝ) (hγ : 0 < γ) (a b : ℕ → ℤ → ℂ) (H : ℕ)
    (hmaj : ∀ x : ℝ, ‖(saw x : ℂ) - fourier a H x‖ ≤ majorant b H x)
    (n : ℕ) (y α : ℝ) :
    ‖sawSum γ n y α - truncatedSum a H γ n y α‖ ≤
      ∑ p ∈ windowPrimes n y, psWeight γ p *
        (majorant b H (-((p : ℝ) + 1) ^ γ) + majorant b H (-(p : ℝ) ^ γ)) := by
  sorry

/-- LEAF. CITED: S. W. Graham and G. Kolesnik, van der Corput's Method of Exponential Sums,
LMS Lecture Note Series 126, Cambridge 1991, display 3.3.4 with the exponent pair 1/2, 1/2,
as used by Song on printed page 4, last display. Applied on dyadic pieces of the window. -/
theorem leaf_exponent_pair_half :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ExponentPairHalf γ := by
  sorry

/-- LEAF. Pages 4 and 5, from "By Lemma 3.1, we have" to "Concluding the above estimate".
The majorant is nonnegative, so the prime sum is at most the sum over all integers of the
window and its shift by one. The zero frequency gives H inverse y n to the 1 minus gamma.
For 1 at most the absolute value of h at most H, partial summation in the weight
x to the 1 minus gamma over initial segments and the exponent pair bound give
H to the 1/2 n to the 1 minus gamma over 2, and the term n to the 2 minus 2 gamma times
log H over H is absorbed into it since gamma exceeds 2/3. -/
theorem leaf_s2_window_of_exponent_pair :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ExponentPairHalf γ →
    ∀ Cb : ℝ, 0 ≤ Cb → ∀ b : ℕ → ℤ → ℂ,
      (∀ H : ℕ, 1 ≤ H → ∀ h : ℤ, |h| ≤ (H : ℤ) → ‖b H h‖ ≤ Cb / (H : ℝ)) →
      (∀ H : ℕ, 1 ≤ H → ∀ x : ℝ, 0 ≤ majorant b H x) →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
        ∀ H : ℕ, 1 ≤ H →
          ∑ p ∈ windowPrimes n y, psWeight γ p *
            (majorant b H (-((p : ℝ) + 1) ^ γ) + majorant b H (-(p : ℝ) ^ γ)) ≤
              C * tailBudget γ n y H := by
  sorry

/-- The cut coefficients give the same truncated Fourier polynomial as Lemma 1. -/
theorem fourier_truncCoeff (a : ℕ → ℤ → ℂ) (H : ℕ) (x : ℝ) :
    fourier (truncCoeff a) H x =
      ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0), a H h * eC (x * h) := by
  unfold Decomp139.fourier
  refine Finset.sum_congr rfl (fun h hh => ?_)
  have habs : |h| ≤ (H : ℤ) := abs_le.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1)
  show (if |h| ≤ (H : ℤ) then a H h else 0) * eC ((h : ℝ) * x) = a H h * eC (x * (h : ℝ))
  rw [if_pos habs, mul_comm (h : ℝ) x]

/-- Assembly. The exact type of `Decomp139.fourier_approximation`, from the three leaves
and the proved Lemma 1 majorant `song_lemma1_majorant591`. No sorry in this body. -/
theorem fourier_approximation_of_leaves :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ a : ℕ → ℤ → ℂ, ∃ K : ℝ, 1 ≤ K ∧
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
          ∀ H : ℕ, 1 ≤ H → ∀ α : ℝ,
            ‖sawSum γ n y α - truncatedSum a H γ n y α‖ ≤
              C * tailBudget γ n y H := by
  intro γ hγ hγ1
  have hγ0 : 0 < γ := by linarith
  obtain ⟨C₁, hC₁, a, b, hL1⟩ :=
    LeanLab.Song2020.Repair591FourierMajorant.song_lemma1_majorant591
  have hcoef : ∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖truncCoeff a H h‖ ≤ max C₁ 1 / |(h : ℝ)| := by
    intro H h hh
    have hpos : 0 < |(h : ℝ)| := abs_pos.mpr (by exact_mod_cast hh)
    by_cases habs : |h| ≤ (H : ℤ)
    · have hH : 1 ≤ H := by
        obtain ⟨h2, h3⟩ := abs_le.mp habs
        omega
      rw [show truncCoeff a H h = a H h from if_pos habs]
      calc ‖a H h‖ ≤ C₁ / |(h : ℝ)| := (hL1 H hH).1 h hh habs
        _ ≤ max C₁ 1 / |(h : ℝ)| := div_le_div_of_nonneg_right (le_max_left _ _) hpos.le
    · rw [show truncCoeff a H h = 0 from if_neg habs, norm_zero]
      exact div_nonneg (le_trans zero_le_one (le_max_right _ _)) (abs_nonneg _)
  obtain ⟨C₂, hC₂, N₀, hS2⟩ := leaf_s2_window_of_exponent_pair γ hγ hγ1
    (leaf_exponent_pair_half γ hγ hγ1) C₁ hC₁ b
    (fun H hH h hh => (hL1 H hH).2.1 h hh)
    (fun H hH x => le_trans (norm_nonneg _) ((hL1 H hH).2.2 x).2)
  refine ⟨truncCoeff a, max C₁ 1, le_max_right _ _, hcoef, C₂, hC₂, N₀, ?_⟩
  intro n hn y hy1 hy2 H hH α
  refine le_trans (leaf_saw_window_triangle γ hγ0 (truncCoeff a) b H ?_ n y α)
    (hS2 n hn y hy1 hy2 H hH)
  intro x
  rw [fourier_truncCoeff a H x]
  exact ((hL1 H hH).2.2 x).2

/-- Match: the assembly has exactly the type of the sealed step. -/
example : (∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ a : ℕ → ℤ → ℂ, ∃ K : ℝ, 1 ≤ K ∧
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
          ∀ H : ℕ, 1 ≤ H → ∀ α : ℝ,
            ‖sawSum γ n y α - truncatedSum a H γ n y α‖ ≤
              C * tailBudget γ n y H) :=
  fourier_approximation_of_leaves

end

/-- Twin check against the sealed declaration itself. -/
example : type_of% @LeanLab.Song2020.Decomp139.fourier_approximation :=
  fourier_approximation_of_leaves

end LeanLab.Song2020.SplitFourierApprox

#print axioms LeanLab.Song2020.SplitFourierApprox.fourier_approximation_of_leaves
#print axioms LeanLab.Song2020.SplitFourierApprox.fourier_truncCoeff
