import LeanLab.Zhao2025.BOrder

/-!
The monotonicity input used in display 3.13 follows from Lemma 2.3.
Source: Zhao 2025, Lemma 2.3 on page 6 and display 3.5 on page 8.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- For positive parameters, C decreases as the cutoff increases. -/
theorem C_antitone (x y z l L l0 : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hl : 0 < l) (h0 : 0 < l0) (hL : l ≤ L) : C x y z L l0 ≤ C x y z l l0 := by
  have ht : 0 ≤ 1 / 3 + x + y := by linarith
  have h1 := B_order (1 / 3 + x + y) l L l0 ht hl h0 hL
  have h2 := B_order z l L l0 hz.le hl h0 hL
  have h2L := (B_order z L L l0 hz.le (hl.trans_le hL) h0 le_rfl).1
  have hp : B (1 / 3 + x + y) L l0 * B z L l0 ≤
      B (1 / 3 + x + y) l l0 * B z l l0 := mul_le_mul h1.2 h2.2 h2L h1.1
  unfold C
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hp)
  positivity

#print axioms C_antitone

end LeanLab.Zhao2025.Task56
