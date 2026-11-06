/-
Perelli 1996, page 479, Theorem 2 and Corollary 2.
Bridges between the existing constants and theorem statements.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Decomp400a
import LeanLab.Perelli1996.Decomp400e
import LeanLab.Perelli1996.Cor2

namespace LeanLab.Perelli1996.Decomp400b
open Finset Real Polynomial
noncomputable section

/-- Page 478. The root representatives in both encodings are identical. -/
theorem rho_eq_encA (F : ℤ[X]) (d : ℕ) :
    (Roots.rootResidues F d).card = EncA.rhoF F d := rfl

/-- Page 479. Both encodings give the same constant C of F. -/
theorem averageConstant_eq (F : ℤ[X]) : Section3.averageConstant F = EncA.CF F := by
  unfold Section3.averageConstant EncA.CF
  simp only [rho_eq_encA]
  change (F.leadingCoeff : ℝ) * (EncA.rhoF F 2 : ℝ) / 2 * EncA.SingConst * _ = _
  ring

/-- Page 479 Theorem 2. The current statement implies encoding A's exact statement.
CONDITIONAL ON the explicit current Theorem 2 input. -/
theorem theorem2_encA_of (F : ℤ[X]) (h : Section3.Theorem2 F) : EncA.Theorem2 F := by
  intro hF A ε hA hε
  obtain ⟨C, N₀, hb⟩ := h hF A ε hA hε
  refine ⟨C, max 3 N₀, ?_⟩
  intro N H hN hH hHu
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have ht := hb N H ((le_max_right _ _).trans hN) hH hHu
  have hsum : (∑ n ∈ win F N H, R (Fv F n).toNat) =
      ∑ n ∈ EncA.nRange (N ^ (1 / EncA.deg F)) H, EncA.R (EncA.Fn F n) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact Decomp400a.R_eq_encA _
  rw [hsum, averageConstant_eq, Real.rpow_neg hL.le, ← div_eq_mul_inv] at ht
  exact ht

/-- Page 479 Theorem 2. Encoding A implies the exact current statement.
CONDITIONAL ON the explicit encoding A input. -/
theorem theorem2_of_encA (F : ℤ[X]) (h : EncA.Theorem2 F) : Section3.Theorem2 F := by
  intro hF A ε hA hε
  obtain ⟨C, N₀, hb⟩ := h hF A ε hA hε
  refine ⟨C, max 3 N₀, ?_⟩
  intro N H hN hH hHu
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have ht := hb N H ((le_max_right _ _).trans hN) hH hHu
  rw [Real.rpow_neg hL.le, ← div_eq_mul_inv, averageConstant_eq]
  convert ht using 2
  apply congrArg (fun t : ℝ => t - EncA.CF F * H * N)
  apply Finset.sum_congr rfl
  intro n hn
  exact Decomp400a.R_eq_encA _

/-- Page 479 Theorem 2. Use the existing prime mean decomposition through the bridge.
CONDITIONAL ON the principal and singular tail leaves of Decomp400e,
the existing character remainder input and the higher degree Weyl input. -/
theorem theorem2 (F : ℤ[X]) : EncA.Theorem2 F :=
  theorem2_encA_of F (Section3.theorem2_of_prime_mean F (Decomp400e.leaf_prime_mean_estimate F))

/-- Page 479 Corollary 2. Use its existing proof and the bridged Theorem 2.
CONDITIONAL ON the principal and singular tail leaves of Decomp400e,
the existing character remainder input and the higher degree Weyl input. -/
theorem corollary2 (F : ℤ[X]) : EncA.Corollary2 F :=
  corollary2_of_theorem2 (theorem2 F)

end
end LeanLab.Perelli1996.Decomp400b
