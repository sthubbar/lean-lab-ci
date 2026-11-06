/-
The integer lifting step in Shao 1206.6139v2 page 16.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.DensityGoldbach.Wrap408

/-- Shao page 16, the no wraparound assertion after the choice of N.
Mathlib Nat.ModEq.eq_of_abs_lt gives equality from the short difference. -/
theorem interval_no_wrap (Q n s : ℕ) (hcong : Nat.ModEq Q n s)
    (hQ : n < Q) (hs : s < 2 * n) : n = s := by
  apply hcong.eq_of_abs_lt
  rw [abs_lt]
  constructor <;> omega

/-- Shao page 16, the quotient representation gives an integer prime sum.
The three strict cutoffs make their total less than 2n. The group modulus
WN is larger than n, so the cyclic representation has no wraparound. -/
theorem triple_no_wrap (W N n t b₁ b₂ b₃ q₁ q₂ q₃ : ℕ)
    (hn : n = W * t + (b₁ + b₂ + b₃)) (hWN : n < W * N)
    (h₁ : 3 * (W * q₁ + b₁) < 2 * n)
    (h₂ : 3 * (W * q₂ + b₂) < 2 * n)
    (h₃ : 3 * (W * q₃ + b₃) < 2 * n)
    (hq : Nat.ModEq N t (q₁ + q₂ + q₃)) :
    n = (W * q₁ + b₁) + (W * q₂ + b₂) + (W * q₃ + b₃) := by
  have hid : W * (q₁ + q₂ + q₃) + (b₁ + b₂ + b₃) =
      (W * q₁ + b₁) + (W * q₂ + b₂) + (W * q₃ + b₃) := by ring
  have hcong := (hq.mul_left' W).add_right (b₁ + b₂ + b₃)
  rw [← hn, hid] at hcong
  exact interval_no_wrap (W * N) n _ hcong hWN (by omega)

end LeanLab.DensityGoldbach.Wrap408

#print axioms LeanLab.DensityGoldbach.Wrap408.interval_no_wrap
#print axioms LeanLab.DensityGoldbach.Wrap408.triple_no_wrap
