/-
The remaining continuous multiplier is exactly a sum with its selected pair erased.
Source: P0029 page 26 displays 7.4 to 7.7 and their Farey separation proof.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp432a
import LeanLab.BhowmikGrimmelt2026.MajorArcPair

namespace LeanLab.BhowmikGrimmelt2026

/-- Integer shifts do not change the centered zero Poisson translate. -/
theorem centeredFourier_add_int432 (G : ℝ → ℝ) (T β : ℝ) (k : ℤ) :
    centeredFourier405 G T (β + k) = centeredFourier405 G T β := by
  unfold centeredFourier405
  rw [round_add_intCast, Int.cast_add]
  congr 1
  ring

/-- The selected continuous term occurs at a canonical pair of the full rational sum. -/
theorem nearContinuous_canonical432 {G : ℝ → ℝ} {X : ℕ} {R η α : ℝ}
    (hX : 0 < (X : ℝ)) (hR : 0 ≤ R) (hRX : R ≤ X) (hsep : 2 * R ^ 2 < X)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hm : MajorArc X R α) :
    ∃ p ∈ reducedPairs ⌊R⌋₊, nearContinuous432 G X R η α =
      centeredFourier405 G (η * X * p.1 / R) (α - p.2 / p.1) := by
  obtain ⟨q, hq, a, ha, hclose⟩ := majorArc_center_in_sum328 hX hRX hα hm
  have hqn := Finset.mem_Icc.mp hq
  have han := (Finset.mem_filter.mp ha).2
  obtain ⟨b, hb, hcop, k, heq⟩ := reduced_residue_of_int (by omega : 0 < q) han
  refine ⟨⟨q, b⟩, (mem_reducedPairs _ _).mpr ⟨hqn.1, hqn.2, hb, hcop⟩, ?_⟩
  rw [nearContinuous_eq432 hX hR hsep hq ha hclose]
  have hd : α - (a : ℝ) / q = (α - (b : ℝ) / q) + ((-k : ℤ) : ℝ) := by
    rw [heq, Int.cast_neg]
    ring
  rw [hd, centeredFourier_add_int432]

/-- On a major arc the pure continuous multiplier is the negative sum of all other pairs.
The selected pair is literally erased from the finite canonical rational set. -/
theorem continuous_off_sum432 {G : ℝ → ℝ} {X : ℕ} {R η α : ℝ}
    (hX : 0 < (X : ℝ)) (hR : 0 ≤ R) (hRX : R ≤ X) (hsep : 2 * R ^ 2 < X)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hm : MajorArc X R α) :
    ∃ p₀ ∈ reducedPairs ⌊R⌋₊,
      nearContinuous432 G X R η α -
        continuousModel405 G R (fun q => η * X * q / R) α =
      -∑ p ∈ (reducedPairs ⌊R⌋₊).erase p₀,
        centeredFourier405 G (η * X * p.1 / R) (α - p.2 / p.1) := by
  classical
  obtain ⟨p₀, hp₀, hnear⟩ := nearContinuous_canonical432 hX hR hRX hsep hα hm
  refine ⟨p₀, hp₀, ?_⟩
  rw [hnear, continuousModel405, ← sum_reducedPairs]
  rw [← Finset.sum_erase_add _ _ hp₀]
  ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.centeredFourier_add_int432
#print axioms LeanLab.BhowmikGrimmelt2026.nearContinuous_canonical432
#print axioms LeanLab.BhowmikGrimmelt2026.continuous_off_sum432
