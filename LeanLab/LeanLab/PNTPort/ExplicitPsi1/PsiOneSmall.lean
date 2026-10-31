import LeanLab.Dudek2014.Lemma5

/-!
# `ψ₁(y) = 0` for `0 ≤ y < 2`

Lab proof, CLOUD 20261020T1518Z-cloud45, unit U-6557. AI wrote this file. Elementary: only
`n ≤ 1` enter and `Λ(0) = Λ(1) = 0`.
-/

namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

theorem psi1_eq_zero_of_lt_two {y : ℝ} (hy0 : 0 ≤ y) (hy : y < 2) :
    LeanLab.Dudek2014.Section22.psi1 y = 0 := by
  unfold LeanLab.Dudek2014.Section22.psi1
  apply Finset.sum_eq_zero
  intro n hn
  have hn1 : n ≤ 1 := by
    have h := Finset.mem_Iic.mp hn
    have : ⌊y⌋₊ < 2 := (Nat.floor_lt hy0).mpr (by exact_mod_cast hy)
    omega
  interval_cases n <;> simp
end LeanLab.PNTPort.ExplicitPsi1.Trivial

namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

/-- `ψ₁(y) ≥ 0` for `y ≥ 0`, unit U-6558. -/
theorem psi1_nonneg {y : ℝ} (hy0 : 0 ≤ y) : 0 ≤ LeanLab.Dudek2014.Section22.psi1 y := by
  unfold LeanLab.Dudek2014.Section22.psi1
  apply Finset.sum_nonneg
  intro n hn
  have h : (n : ℝ) ≤ y := (Nat.le_floor_iff hy0).mp (Finset.mem_Iic.mp hn)
  exact mul_nonneg (by linarith) ArithmeticFunction.vonMangoldt_nonneg

end LeanLab.PNTPort.ExplicitPsi1.Trivial

namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

/-- `ψ₁(y) ≤ y Σ_{n ≤ y} Λ(n) = y ψ(y)` for every `y`, unit U-6559. -/
theorem psi1_le (y : ℝ) :
    LeanLab.Dudek2014.Section22.psi1 y ≤
      y * ∑ n ∈ Finset.Iic ⌊y⌋₊, ArithmeticFunction.vonMangoldt n := by
  unfold LeanLab.Dudek2014.Section22.psi1
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

end LeanLab.PNTPort.ExplicitPsi1.Trivial
