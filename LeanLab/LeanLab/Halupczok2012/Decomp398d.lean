import LeanLab.Halupczok2012.Variable398
import LeanLab.Halupczok2012.UniformMain398
import LeanLab.Halupczok2012.Decomp398c

/-!
Supply decomposition for the maximum supplement of Halupczok Theorem 2.
Source: journal pages 344 to 345, the main term computation and its last paragraph.
The binary part is proved uniformly by Variable398.
Only the uniform main term step remains open here.
https://doi.org/10.5802/jtnb.839
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp398d

open Finset
open scoped Classical

/-- LEAF. Halupczok page 344, the main term display after 4.2 and the Euler product step.
Theorem 2.1 is an explicit hypothesis. The residues vary with q.
This estimate concerns one weighted prime sum, with no binary prime sum.
Its error is Y1 times the logarithmic saving, before multiplication by Y2. -/
theorem uniform_main_term (h3 : Theorem3) :
    ∀ A ε ε1 ε2 : ℝ, 0 < A → 0 < ε → 0 < ε1 → 0 < ε2 → ∃ B : ℝ, 0 < B ∧
      ∀ c : Fin 7 → ℝ, (∀ i, 0 < c i) → ∀ c7 : ℝ, 0 < c7 → ∃ C Y0 : ℝ,
      ∀ (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ), Y0 ≤ Y1 → Y0 ≤ Y2 →
        Thm2Hyp ε ε1 ε2 B c n X1 Y1 X2 Y2 Q → Q ≤ c7 * Y1 ^ (1 / 2 : ℝ) →
        ∀ a : ℕ → ℤ, (∀ q, Int.gcd (a q) q = 1) →
        ∑ q ∈ Icc 1 ⌊Q⌋₊, |mainSum n X1 Y1 q (a q) - T n q (a q) * Y1| ≤
          C * Y1 * Real.log Y2 ^ (-A) := by
  intro A ε ε1 ε2 hA hε hε1 hε2
  obtain ⟨B, hB, hM⟩ := UniformMain398.mainTerm h3 A ε ε1 ε2 hA hε hε1 hε2
  refine ⟨B, hB, fun c hc c7 hc7 => ?_⟩
  obtain ⟨C, Y0, hC⟩ := hM c hc
  refine ⟨C, Y0, ?_⟩
  intro n X1 Y1 X2 Y2 Q hY1 hY2 hH hQ a ha
  have hm := hC n X1 Y1 X2 Y2 Q hY1 hY2 hH a
  simpa [ha] using hm

/-- Exact sealed Theorem2Max statement, from the uniform main term leaf and the PP1993 leaves. -/
theorem theorem2_max : Theorem2Max := by
  intro A ε ε1 ε2 hA hε hε1 hε2
  obtain ⟨B, hB, hM⟩ := uniform_main_term (theorem3_of_uniform Decomp398c.pps_uniform)
    A ε ε1 ε2 hA hε hε1 hε2
  refine ⟨B, hB, ?_⟩
  intro c hc c7 hc7
  obtain ⟨C1, Y01, hb⟩ := Variable398.binaryPart_uniform (theorem5_of_PP Decomp398a.pp1993_goldbach)
    A ε ε1 ε2 hA hε hε1 hε2 B hB c hc
  obtain ⟨C2, Y02, hm⟩ := hM c hc c7 hc7
  refine ⟨C1 + C2, max Y01 (max Y02 0), ?_⟩
  intro n X1 Y1 X2 Y2 Q hY1 hY2 hH hQ a ha
  have hY2nn : 0 ≤ Y2 := (le_max_right _ _).trans ((le_max_right _ _).trans hY2)
  have hbin := hb n X1 Y1 X2 Y2 Q ((le_max_left _ _).trans hY1)
    ((le_max_left _ _).trans hY2) hH a
  have hmain := hm n X1 Y1 X2 Y2 Q
    ((le_max_left _ _).trans ((le_max_right _ _).trans hY1))
    ((le_max_left _ _).trans ((le_max_right _ _).trans hY2)) hH hQ a ha
  have hmain' := mul_le_mul_of_nonneg_left hmain hY2nn
  have hle : (∑ q ∈ Icc 1 ⌊Q⌋₊, |ternSum n X1 Y1 X2 Y2 q (a q) - T n q (a q) * Y1 * Y2|) ≤
      (∑ q ∈ Icc 1 ⌊Q⌋₊, |binPart n X1 Y1 X2 Y2 q (a q)|) +
      Y2 * ∑ q ∈ Icc 1 ⌊Q⌋₊, |mainSum n X1 Y1 q (a q) - T n q (a q) * Y1| := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun q _ => ?_
    rw [Variable398.error_split]
    calc
      _ ≤ |binPart n X1 Y1 X2 Y2 q (a q)| +
          |Y2 * (mainSum n X1 Y1 q (a q) - T n q (a q) * Y1)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg hY2nn]
  nlinarith

end LeanLab.Halupczok2012.Decomp398d
