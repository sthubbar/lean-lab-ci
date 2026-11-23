import LeanLab.ExceptionalSet.State1539

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

example (N₁ : ℕ) : True := by
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, N₁ = N₁ := ⟨0, rfl⟩
  have hFval : F (5 / 4 : ℝ) (max N₁ 3)
      = Real.exp (Real.log ((max N₁ 3 : ℕ) : ℝ) ^ ((5:ℝ)/4)) := rfl
  trivial

example (N₁ : ℕ) : True := by
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, N₁ = N₁ := ⟨0, rfl⟩
  have hFval : F (5 / 4 : ℝ) (max N₁ 3)
      = Real.exp (Real.log ((max N₁ 3 : ℕ) : ℝ) ^ ((5:ℝ)/4)) := by
    unfold F
    rfl
  trivial

end LeanLab.ExceptionalSet.U1539
