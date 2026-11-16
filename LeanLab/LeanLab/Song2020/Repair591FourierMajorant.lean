/-
AI wrote the Lean code. CODEX task591.
Source: Song 2020, https://arxiv.org/pdf/2012.06322v1, page 3, Lemma 1.
This is the cited trigonometric majorant, with its coefficient families quantified together.
Binary Goldbach is open.
-/
import LeanLab.Song2020.Characteristic139

namespace LeanLab.Song2020.Repair591FourierMajorant

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

/-- LEAF: Song 2012.06322, page 3, Lemma 1, citing Graham and Kolesnik, Appendix.
One coefficient pair works for all real x at each positive truncation level.
The majorant is real. Its real part is used for the ordered inequality.
The coefficient estimates are uniform in the truncation level and frequency. -/
theorem song_lemma1_majorant591 :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ a b : ℕ → ℤ → ℂ, ∀ H : ℕ, 1 ≤ H →
      (∀ h : ℤ, h ≠ 0 → |h| ≤ (H : ℤ) → ‖a H h‖ ≤ C / |(h : ℝ)|) ∧
      (∀ h : ℤ, |h| ≤ (H : ℤ) → ‖b H h‖ ≤ C / (H : ℝ)) ∧
      ∀ x : ℝ,
        (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b H h * eC (x * h)).im = 0 ∧
        ‖(Decomp139.saw x : ℂ) -
          ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0),
            a H h * eC (x * h)‖ ≤
          (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b H h * eC (x * h)).re := by
  sorry

end LeanLab.Song2020.Repair591FourierMajorant

#print axioms LeanLab.Song2020.Repair591FourierMajorant.song_lemma1_majorant591
