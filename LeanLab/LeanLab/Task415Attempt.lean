import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Range
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Round

open Finset
open scoped Classical

namespace Task415Attempt

noncomputable def countIn (A : Set ℕ) (N : ℕ) : ℕ := #{n ∈ Icc 1 N | n ∈ A}

def PStar : Set ℕ := Set.univ

def PosUpperDensityIn (A B : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ c * (countIn B N : ℝ) < countIn A N

def InP (p : ℕ) : Prop := p.Prime

noncomputable def distInt (x : ℝ) : ℝ := |x - round x|

theorem dense_attempt (A : Set ℕ)
    (hA : A ⊆ PStar) (hδ : PosUpperDensityIn A PStar) :
    ∀ X : ℕ, ∃ N a b c : ℕ, X ≤ N ∧
      a ∈ A ∧ b ∈ A ∧ c ∈ A ∧
      N < 3 * a ∧ 3 * a < 2 * N ∧
      N < 3 * b ∧ 3 * b < 2 * N ∧
      N < 3 * c ∧ 3 * c < 2 * N ∧
      a ≠ b ∧ (a : ZMod N) + c = 2 * b := by
  intro X
  unfold PosUpperDensityIn at hδ
  obtain ⟨c, hc, hδ⟩ := hδ
  obtain ⟨N, hN, hcount⟩ := hδ X
  have hcountA : 0 < countIn A N := by
    have hB : 0 ≤ (countIn PStar N : ℝ) := by
      unfold countIn
      positivity
    unfold countIn at hcount hB ⊢
    have hmul : 0 ≤ c * (#({n ∈ Icc 1 N | n ∈ PStar}) : ℝ) := mul_nonneg hc.le hB
    linarith
  exact hcountA

theorem dyadic_attempt (ξ : ℝ) (hξ : Irrational ξ) (hξ0 : 0 < ξ)
    (κ θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1 / 80) :
    ∀ X : ℕ, ∃ N p : ℕ, max 1 X ≤ N ∧ N ≤ p ∧ p ≤ 2 * N ∧
      InP p ∧ distInt (ξ * p + κ) ≤ (N : ℝ) ^ (-θ) / 2 := by
  intro X
  have hN0 : 0 < (max 1 X : ℝ) := by
    positivity
  have hθ01 : 0 ≤ θ := hθ0.le
  have hθ11 : θ ≤ 1 := by linarith
  exact hN0

end Task415Attempt
