/-
P0045, journal pages 778 to 779, displays 28 and 30.
This is the uniform window form of the A prime estimate used by the averaging argument.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LPZ2007.D4ProductLog
import LeanLab.LPZ2007.D4Support

namespace LeanLab.LPZ2007.APrimeWindow

open Finset Real
open LeanLab.LPZ2007 LeanLab.LPZ2007.Eq14FromCor42 LeanLab.LPZ2007.D4Tail

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The weighted support A star on the application window. -/
def AStarWindow (X : ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ ((Icc 1 ⌊X⌋₊).filter OddSqf).filter (fun d => 0 < oneCount d ⌊Lp X⌋₊ m), fd d

/-- A star is at most five times exp 27 times log L on the required window. -/
theorem aStarWindow_log {X : ℝ} (hX : 0 < X) (hL : 36 ≤ Lg X) {m : ℕ}
    (hm0 : X / 2 ≤ (m : ℝ)) (hmX : (m : ℝ) ≤ X) :
    AStarWindow X m ≤ 5 * exp 27 * log (Lg X) := by
  let M := ⌊Lp X⌋₊
  have hpow : ∀ a ∈ Icc 1 M, 2 ^ a < m := by
    intro a ha
    let ν : Fin 1 → ℕ := fun _ => a
    have hν : ν ∈ tuples 1 M := by
      simp only [tuples, Fintype.mem_piFinset]
      intro i
      exact ha
    have hp := pow2sum_small (by decide : 1 ≤ 1) hX (by simpa using hL) hν
    have he : pow2sum ν = 2 ^ a := by simp [pow2sum, ν]
    rw [he] at hp
    exact_mod_cast (show ((2 ^ a : ℕ) : ℝ) < m by linarith)
  have hM : (M : ℝ) ≤ Lg X := by
    have hs : √(Lg X) ≤ Lg X := (sqrt_le_left (by linarith)).2 (by nlinarith)
    have hLp : 0 ≤ Lp X := by unfold Lp; linarith
    have hf := Nat.floor_le hLp
    change (M : ℝ) ≤ Lg X - √(Lg X) at hf
    linarith [sqrt_nonneg (Lg X)]
  have hlog : log X = Lg X * log 2 := by unfold Lg Real.logb; field_simp
  have hprod := D4ProductLog.product_weight_log (Icc 1 M) (fun a => m - 2 ^ a) hX
    (by linarith : 2 ≤ Lg X) hlog
    (fun a ha => by have := hpow a ha; omega)
    (fun a _ => (show ((m - 2 ^ a : ℕ) : ℝ) ≤ m by exact_mod_cast Nat.sub_le m _).trans hmX)
    (by simpa using hM)
  exact (D4Support.support_sum_le ((Icc 1 ⌊X⌋₊).filter OddSqf) M m
    (fun d hd => (mem_filter.1 hd).2) hpow).trans hprod

/-- The uniform window maximum bound holds with an explicit constant and threshold. -/
theorem aPrimeWindowBound_proved : (∃ C : ℝ, 0 < C ∧ ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ m : ℕ,
    X / 2 ≤ (m : ℝ) → (m : ℝ) ≤ X → AStarWindow X m ≤ C * log (Lg X)) := by
  refine ⟨5 * exp 27, by positivity, (2 : ℝ) ^ (36 : ℝ), fun X hX m hm0 hmX => ?_⟩
  have hL : 36 ≤ Lg X := Lg_ge hX
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
  exact aStarWindow_log hX0 hL hm0 hmX

end
end LeanLab.LPZ2007.APrimeWindow

#print axioms LeanLab.LPZ2007.APrimeWindow.aStarWindow_log

#print axioms LeanLab.LPZ2007.APrimeWindow.aPrimeWindowBound_proved
