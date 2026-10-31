/-
Links between the density theorems and the classical ternary statements.
AI-written Lean code, Claude, 2026-10-16, run 20261016T2303Z-22954, unit U-0081.
-/
import LeanLab.DensityGoldbach.Statements
import LeanLab.Ternary.Statements

open Finset Filter
open scoped Classical

namespace LeanLab.DensityGoldbach

/-- The primes have relative ratio `1` from `N = 2` on. -/
lemma relRatio_P (N : ℕ) (hN : 2 ≤ N) : relRatio P N = 1 := by
  unfold relRatio
  have h : #{n ∈ Icc 1 N | n ∈ P ∧ n.Prime} = #{n ∈ Icc 1 N | n.Prime} := by
    congr 1; ext n; simp [P]
  rw [h]
  have hpos : 0 < #{n ∈ Icc 1 N | n.Prime} :=
    card_pos.2 ⟨2, mem_filter.2 ⟨mem_Icc.2 ⟨by norm_num, hN⟩, Nat.prime_two⟩⟩
  exact div_self (by exact_mod_cast hpos.ne')

/-- `δ(P) = 1`. -/
theorem lowerDensity_P : lowerDensity P = 1 := by
  unfold lowerDensity
  have : relRatio P =ᶠ[atTop] fun _ => (1 : ℝ) :=
    eventually_atTop.2 ⟨2, fun N hN => relRatio_P N hN⟩
  rw [liminf_congr this, liminf_const]

/-- **Shao's Theorem 1.1 gives Vinogradov's theorem**, taking `A = P`. -/
theorem vinogradov_of_shao (h : Shao11) : ∃ C : ℝ, LeanLab.Ternary.TernaryAbove C := by
  obtain ⟨N₀, hN₀⟩ := h P subset_rfl (by rw [lowerDensity_P]; norm_num)
  refine ⟨N₀, fun n hn hC => ?_⟩
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hN₀ n (by exact_mod_cast hC) hn
  exact ⟨a, b, c, ha, hb, hc, rfl⟩

/-- **Li-Pan gives Vinogradov's theorem**, taking `A₁ = A₂ = A₃ = P`. -/
theorem vinogradov_of_liPan (h : LiPan) : ∃ C : ℝ, LeanLab.Ternary.TernaryAbove C := by
  obtain ⟨N₀, hN₀⟩ := h P P P subset_rfl subset_rfl subset_rfl
    (by rw [lowerDensity_P]; norm_num)
  refine ⟨N₀, fun n hn hC => ?_⟩
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hN₀ n (by exact_mod_cast hC) hn
  exact ⟨a, b, c, ha, hb, hc, rfl⟩

/-- For a single set, Shao's `5/8` is stronger than the diagonal case of Li-Pan, `δ > 2/3`. -/
theorem liPan_diag_of_shao (h : Shao11) (A : Set ℕ) (hA : A ⊆ P)
    (hd : 2 < lowerDensity A + lowerDensity A + lowerDensity A) : LargeOddIn A A A :=
  h A hA (by linarith)

end LeanLab.DensityGoldbach
