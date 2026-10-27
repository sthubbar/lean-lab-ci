import LeanLab.Zhao2025.BZero
import LeanLab.Zhao2025.ExpPairIntegral

/-!
The scaled zero lambda0 branch expressed through symmetric exponential integrals.
Source: Zhao 2025, display 2.19 and the proof of Lemma 2.3, page 6.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- Scaling the zero lambda0 branch gives an integral and a squared half interval integral. -/
theorem B_zero_scaled_eq (t l : ℝ) (hl : l ≠ 0) :
    Real.exp (l * t) * B t l 0 =
      1 / 6 * (∫ u in 0..t, Real.exp (l * u) + Real.exp (-l * u)) +
      (∫ u in 0..(t / 2), Real.exp (l * u) + Real.exp (-l * u)) ^ 2 := by
  have he0 : Real.exp (l * t) * Real.exp (-(l * t)) = 1 := by
    rw [← Real.exp_add, show l * t + -(l * t) = 0 by ring, Real.exp_zero]
  have he2 : Real.exp (l * t) * Real.exp (-(2 * l * t)) = Real.exp (-(l * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : Real.exp (l * t) * B t l 0 =
      1 / 6 * ((Real.exp (l * t) - Real.exp (-(l * t))) / l) +
        (Real.exp (l * t) + Real.exp (-(l * t)) - 2) / l ^ 2 := by
    rw [B_zero_eq t l hl]
    calc
      _ = 1 / 6 * ((Real.exp (l * t) -
            Real.exp (l * t) * Real.exp (-(2 * l * t))) / l) +
          (Real.exp (l * t) - 2 * (Real.exp (l * t) * Real.exp (-(l * t))) +
            (Real.exp (l * t) * Real.exp (-(l * t))) * Real.exp (-(l * t))) / l ^ 2 := by
              field_simp [hl]
              <;> ring
      _ = _ := by simp only [he0, he2, one_mul]; ring
  have hP : Real.exp (l * (t / 2)) ^ 2 = Real.exp (l * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hM : Real.exp (-l * (t / 2)) ^ 2 = Real.exp (-(l * t)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hPM : Real.exp (l * (t / 2)) * Real.exp (-l * (t / 2)) = 1 := by
    rw [← Real.exp_add, show l * (t / 2) + -l * (t / 2) = 0 by ring, Real.exp_zero]
  have hhalf : ((Real.exp (l * (t / 2)) - Real.exp (-l * (t / 2))) / l) ^ 2 =
      (Real.exp (l * t) + Real.exp (-(l * t)) - 2) / l ^ 2 := by
    calc
      _ = (Real.exp (l * (t / 2)) ^ 2 + Real.exp (-l * (t / 2)) ^ 2 -
          2 * (Real.exp (l * (t / 2)) * Real.exp (-l * (t / 2)))) / l ^ 2 := by
            field_simp [hl]
            <;> ring
      _ = _ := by rw [hP, hM, hPM]; ring
  have hE : Real.exp (-l * t) = Real.exp (-(l * t)) := by congr 1; ring
  rw [hs, exp_pair_integral t l hl, exp_pair_integral (t / 2) l hl, hhalf, hE]

#print axioms B_zero_scaled_eq

end LeanLab.Zhao2025.Task56
