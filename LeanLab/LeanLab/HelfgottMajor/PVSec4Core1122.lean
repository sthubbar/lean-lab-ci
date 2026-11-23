import Mathlib
import LeanLab.HelfgottMajor.PVLemmas1122

/-!
Route burst S68, burst-20261122, tag sec4-core.
Proof of the LEAF `PVLemmas1122.sec4_core`, Pomerance 2011 Section 4 as quoted without proof
in Frolenkov arXiv 1107.0381 Lemma 2.

The reduction is a reconstruction, Pomerance's text is not available here. With
`u = (A+B)/2`, `v = (A-B)/2` one has `cos A - cos B = -2 sin u sin v`, so by AM-GM
`|cos A - cos B| ≤ sin² u + sin² v = 1 - (cos (A+B) + cos (A-B))/2`. Summing with weight 1/m,
`∑ |cos mα - cos mβ|/m ≤ H_n - C(α+β)/2 - C(α-β)/2` with `C y = ∑ cos(m y)/m`, and each `C`
is at least `-(log 2 + 2/n)` by the cosine partial sum lower bound.

`sec4_core_of_cos` takes that lower bound as a hypothesis and has no sorry. `sec4_core` applies
it to `PVLemmas1122.cos_partial_lower`, a separate LEAF, so it is unconditional exactly when that
LEAF is.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVSec4Core1122

open Real Finset

/-- Pointwise AM-GM step of the reconstructed Section 4 argument:
`|cos A - cos B| ≤ 1 - (cos (A+B) + cos (A-B))/2`. -/
theorem abs_cos_sub_le (A B : ℝ) :
    |cos A - cos B| ≤ 1 - (cos (A + B) + cos (A - B)) / 2 := by
  set u := (A + B) / 2
  set v := (A - B) / 2
  have hA : A = u + v := by simp only [u, v]; ring
  have hB : B = u - v := by simp only [u, v]; ring
  have hS : A + B = 2 * u := by simp only [u]; ring
  have hD : A - B = 2 * v := by simp only [v]; ring
  rw [hS, hD, hA, hB, cos_add, cos_sub, cos_two_mul, cos_two_mul]
  have hu := sin_sq_add_cos_sq u
  have hv := sin_sq_add_cos_sq v
  have key : cos u * cos v - sin u * sin v - (cos u * cos v + sin u * sin v) =
      -2 * (sin u * sin v) := by ring
  rw [key, abs_le]
  constructor <;> nlinarith [sq_nonneg (sin u - sin v), sq_nonneg (sin u + sin v)]

/-- Section 4 core, conditional on the cosine partial sum lower bound `hcos`. -/
theorem sec4_core_of_cos
    (hcos : ∀ (y : ℝ) (n : ℕ), 1 ≤ n → -(log 2 + 2 / n) ≤ ∑ j ∈ Icc 1 n, cos (j * y) / j)
    (α β : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Icc 1 n, |cos (m * α) - cos (m * β)| / m ≤
      ∑ m ∈ Icc 1 n, (1 : ℝ) / m + (log 2 + 2 / n) := by
  have h1 := hcos (α + β) n hn
  have h2 := hcos (α - β) n hn
  have hterm : ∀ m ∈ Icc 1 n, |cos (m * α) - cos (m * β)| / (m : ℝ) ≤
      (1 : ℝ) / m - (1 / 2) * (cos (m * (α + β)) / m) - (1 / 2) * (cos (m * (α - β)) / m) := by
    intro m _
    have hm : (0 : ℝ) ≤ m := by positivity
    have h := abs_cos_sub_le (m * α) (m * β)
    have e1 : (m : ℝ) * α + m * β = m * (α + β) := by ring
    have e2 : (m : ℝ) * α - m * β = m * (α - β) := by ring
    rw [e1, e2] at h
    have e : (1 : ℝ) / m - (1 / 2) * (cos (m * (α + β)) / m) - (1 / 2) * (cos (m * (α - β)) / m)
        = (1 - (cos (m * (α + β)) + cos (m * (α - β))) / 2) / m := by ring
    rw [e]
    exact div_le_div_of_nonneg_right h hm
  have hs := sum_le_sum hterm
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum] at hs
  linarith

/-- Exactly the LEAF `PVLemmas1122.sec4_core`, from `sec4_core_of_cos` and
`PVLemmas1122.cos_partial_lower`. -/
theorem sec4_core (α β : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Icc 1 n, |cos (m * α) - cos (m * β)| / m ≤
      ∑ m ∈ Icc 1 n, (1 : ℝ) / m + (log 2 + 2 / n) :=
  sec4_core_of_cos LeanLab.HelfgottMajor.PVLemmas1122.cos_partial_lower α β n hn

example : type_of% @sec4_core = type_of% @LeanLab.HelfgottMajor.PVLemmas1122.sec4_core := rfl

end LeanLab.HelfgottMajor.PVSec4Core1122

#print axioms LeanLab.HelfgottMajor.PVSec4Core1122.abs_cos_sub_le
#print axioms LeanLab.HelfgottMajor.PVSec4Core1122.sec4_core_of_cos
#print axioms LeanLab.HelfgottMajor.PVSec4Core1122.sec4_core
