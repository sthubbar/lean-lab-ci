/-
Lemma 7.2 of Bhowmik and Grimmelt 2026, page 26.
The proof uses exact Poisson summation, rapid Fourier decay, evenness and Farey separation.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.SumEstimates
import LeanLab.BhowmikGrimmelt2026.MajorArcPair

namespace LeanLab.BhowmikGrimmelt2026

/-- Lemma 7.2 with the exact statement already recorded in Statements.lean. -/
theorem lemma72_proved : Lemma72 := by
  intro G hG A hA
  obtain ⟨H, hH, hestimate⟩ := scaledPairSum_estimates hG hA
  refine ⟨H, fun N R η hR hη _hη1 hcondition α => ?_⟩
  have hR0 : 0 < R := by linarith
  have hR2 : 0 < R ^ 2 := by positivity
  have hηN : 0 < η * (N : ℝ) := by nlinarith only [hcondition, hR2]
  have hN : (0 : ℝ) < N := by
    by_contra hn
    have h := mul_nonpos_of_nonneg_of_nonpos hη.le (le_of_not_gt hn)
    linarith
  let K : ℝ := η * N / R ^ 2
  have hK10 : 10 ≤ K := by
    dsimp [K]
    exact (le_div_iff₀ hR2).mpr hcondition
  have hK : 1 ≤ K := by linarith
  have hK0 : 0 < K := by linarith
  have hscale (q : ℕ) : η * N * q / R = K * R * q := by
    dsimp [K]
    field_simp
    <;> ring
  have hT : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < η * N * q / R := by
    intro q hq
    have hq0 : 0 < q := by have h := (Finset.mem_Icc.mp hq).1; omega
    positivity
  have hb : bRhat G R (fun q => η * N * q / R) α = scaledPairSum G R K α := by
    rw [bRhat_eq hG.supp hG.even R (fun q => η * N * q / R) hT α]
    rw [scaledPairSum, sum_reducedPairs ⌊R⌋₊
      (fun q a => GThat G (K * R * q) (α - a / q))]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro a ha
    rw [hscale]
  have hest := hestimate R K η hR hK hη.le α
  constructor
  · intro hmajor
    rw [hb]
    apply hest.1
    obtain ⟨p, hp, hclose⟩ := majorArc_pair hN hR hmajor
    refine ⟨p, hp, ?_⟩
    have h := mul_le_mul_of_nonneg_left hclose (show 0 ≤ K * R by positivity)
    have heq : K * R * (R / N) = η := by
      dsimp [K]
      field_simp
      <;> ring
    calc
      K * R * (p.1 : ℝ) * intDist (α - p.2 / p.1) =
          K * R * ((p.1 : ℝ) * intDist (α - p.2 / p.1)) := by ring
      _ ≤ K * R * (R / N) := h
      _ = η := heq
  · intro _hminor
    rw [hb]
    exact hest.2

/-- The paper's Lemma 7.2, replacing the cited placeholder in Statements.lean. -/
theorem lemma72 : Lemma72 := lemma72_proved

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.lemma72_proved
#print axioms LeanLab.BhowmikGrimmelt2026.lemma72
