/-
P0045, journal pages 777 to 779, displays 20, 28 and 30.
The single exponent tail is small once the coefficient tail and product remainder are small.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LPZ2007.D4Support

namespace LeanLab.LPZ2007.D4SingleBound

open Finset Real
open LeanLab.LPZ2007 LeanLab.LPZ2007.D4Tail LeanLab.LPZ2007.D4Product
open LeanLab.LPZ2007.D4Support

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The single exponent tail is at most two times delta times L. -/
theorem weighted_one_small (F : Finset ℕ) (M m : ℕ) {X L δ : ℝ}
    (hF : ∀ d ∈ F, OddSqf d) (hpow : ∀ a ∈ Icc 1 M, 2 ^ a < m)
    (hX : 0 < X) (hδ : 0 < δ) (hlog : log X = L * log 2)
    (hmX : (m : ℝ) ≤ X) (hM : (M : ℝ) ≤ L)
    (hcoeff : ∑ d ∈ F, romanovTerm d ≤ δ)
    (hL : (6 * exp 27 / δ) ^ 2 + 1 ≤ L) :
    ∑ d ∈ F, fd d * (oneCount d M m : ℝ) ≤ 2 * δ * L := by
  have hprod := product_weight_small (Icc 1 M) (fun a => m - 2 ^ a) hX hδ hlog
    (fun a ha => by have := hpow a ha; omega)
    (fun a _ => (show ((m - 2 ^ a : ℕ) : ℝ) ≤ m by exact_mod_cast Nat.sub_le m (2 ^ a)).trans hmX)
    (by simpa using hM) hL
  have hmain := weighted_one_le F M m hF hpow
  have hcoeff' : (M : ℝ) * ∑ d ∈ F, romanovTerm d ≤ δ * L := by
    calc (M : ℝ) * ∑ d ∈ F, romanovTerm d ≤ M * δ :=
        mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
      _ ≤ L * δ := mul_le_mul_of_nonneg_right hM hδ.le
      _ = δ * L := mul_comm _ _
  linarith

end
end LeanLab.LPZ2007.D4SingleBound

#print axioms LeanLab.LPZ2007.D4SingleBound.weighted_one_small
