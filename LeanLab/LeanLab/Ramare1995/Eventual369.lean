/-
Ramaré 1995 p. 704, the limit of the method paragraph, mentions five primes for
sufficiently large odd integers. This file proves that ineffective conclusion from the
lab's already proved density zero theorem for the binary Goldbach exceptional set.
Two Goldbach sums give four primes for sufficiently large even integers. Adding 3 gives
five primes for sufficiently large odd integers. No fixed numerical threshold is certified.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Ramare1995.Theorem2Weak
import LeanLab.SchnirelmannConstant.Defs

namespace LeanLab.Ramare1995.Eventual369
open Finset
open LeanLab LeanLab.SchnirelmannConstant

/-- A pointwise exceptional count bound supplies two complementary Goldbach sums.
CONDITIONAL ON the displayed exceptional count bound. This is the elementary covering
step for the ineffective conclusion discussed on p. 704. -/
theorem four_of_exceptional_bound (n : ℕ) (hn : Even n) (hn20 : 20 ≤ n)
    (hE : (LeanLab.ExceptionalSet.E n : ℝ) ≤ n / 10) : AtMostPrimes 4 n := by
  classical
  let S := {m ∈ Ioc 3 (n - 4) | Even m}
  let B := {m ∈ Icc 4 n | Even m ∧ ¬ IsGoldbachSum m}
  let C := B ∪ B.image (fun m => n - m)
  have hB : #B = LeanLab.ExceptionalSet.E n := rfl
  have hC : #C ≤ 2 * LeanLab.ExceptionalSet.E n := by
    have h1 := card_union_le B (B.image (fun m => n - m))
    have h2 := card_image_le (s := B) (f := fun m => n - m)
    dsimp [C]
    omega
  have hs := Theorem2Weak.card_even_Ioc 3 (n - 4)
  have hS : n ≤ 2 * #S + 8 := by
    change (n - 4) / 2 - 3 / 2 ≤ #S at hs
    omega
  have hcR : (#C : ℝ) ≤ 2 * (LeanLab.ExceptionalSet.E n : ℝ) := by exact_mod_cast hC
  have hsR : (n : ℝ) ≤ 2 * (#S : ℝ) + 8 := by exact_mod_cast hS
  have hnR : (20 : ℝ) ≤ n := by exact_mod_cast hn20
  have hlt : #C < #S := by
    exact_mod_cast (show (#C : ℝ) < #S by linarith)
  obtain ⟨m, hm, hnot⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hm' : 3 < m ∧ m ≤ n - 4 ∧ Even m := by
    simpa only [S, mem_filter, mem_Ioc, and_assoc] using hm
  have hGm : IsGoldbachSum m := by
    by_contra hng
    apply hnot
    apply mem_union_left
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hm'.2.2, hng⟩
  have he : Even (n - m) := by
    have hn2 := Nat.even_iff.mp hn
    have hm2 := Nat.even_iff.mp hm'.2.2
    exact Nat.even_iff.mpr (by omega)
  have hGnm : IsGoldbachSum (n - m) := by
    by_contra hng
    apply hnot
    apply mem_union_right
    refine mem_image.mpr ⟨n - m, ?_, by omega⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, he, hng⟩
  have hsum := (AtMostPrimes.of_goldbach hGm).add (AtMostPrimes.of_goldbach hGnm)
  rwa [show m + (n - m) = n by omega] at hsum

/-- Sufficiently large even integers are sums of at most four primes.
The threshold is ineffective. This uses the proved exceptional set density theorem,
not a cited hypothesis or the open numerical leaves. Auxiliary to the p. 704 conclusion. -/
theorem eventual_even_four :
    ∃ N₀ : ℕ, ∀ n : ℕ, Even n → N₀ ≤ n → AtMostPrimes 4 n := by
  obtain ⟨Y₀, hY⟩ := Theorem2Weak.E_small
  refine ⟨max Y₀ 20, fun n hn hlarge => ?_⟩
  exact four_of_exceptional_bound n hn (le_trans (le_max_right _ _) hlarge)
    (hY n (le_trans (le_max_left _ _) hlarge))

/-- Ramaré 1995 p. 704, the sufficiently large odd five prime conclusion.
The threshold is ineffective. The proof uses the lab's exceptional set theorem.
It supplies no value for the fixed thresholds in DecompJ1133. -/
theorem eventual_odd_five :
    ∃ N₀ : ℕ, ∀ n : ℕ, Odd n → N₀ ≤ n → AtMostPrimes 5 n := by
  obtain ⟨N₀, hN⟩ := eventual_even_four
  refine ⟨N₀ + 3, fun n hn hlarge => ?_⟩
  have he : Even (n - 3) := by
    have hn2 := Nat.odd_iff.mp hn
    exact Nat.even_iff.mpr (by omega)
  have h4 := hN (n - 3) he (by omega)
  have hs := (AtMostPrimes.prime Nat.prime_three).add h4
  rwa [show 3 + (n - 3) = n by omega] at hs

end LeanLab.Ramare1995.Eventual369
