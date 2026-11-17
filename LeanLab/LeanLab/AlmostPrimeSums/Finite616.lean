/-
AI wrote the Lean code. Goldbach is open.
Task616 U-1690. Finite form of Buchstab1938 pp. 381 to 383, display 7.
-/
import LeanLab.BakerHarmanPintz1997.Buchstab

open Finset
noncomputable section
namespace LeanLab.AlmostPrimeSums.Finite616
open LeanLab.BakerHarmanPintz1997
attribute [local instance] Classical.propDecidable

/-- P0072 p. 63 sieve count with a strict real prime cutoff. The input set is P0072 p. 61. -/
def sifted (N : ℕ) (z : ℝ) : Finset ℕ :=
  ((Icc 1 N).filter fun n => n.Coprime N).filter fun n => Rough (n * (N - n)) z

/-- The exact finite mass removed between two strict cutoffs.
The quotient is the original product divided by its least prime factor. -/
def removed (N : ℕ) (w z : ℝ) : ℂ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime N),
    ∑ p ∈ (n * (N - n)).primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z),
      psi (n * (N - n) / p) (p : ℝ)

/-- The product in the Buchstab identity is positive on the actual P0072 input set for N above one. -/
theorem product_pos {N n : ℕ} (hN : 1 < N)
    (hn : n ∈ (Icc 1 N).filter fun n => n.Coprime N) : 0 < n * (N - n) := by
  obtain ⟨hnI, hc⟩ := mem_filter.mp hn
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hnI
  have hne : n ≠ N := by
    intro he
    subst n
    have : N = 1 := by simpa using hc
    omega
  exact Nat.mul_pos (by omega) (Nat.sub_pos_of_lt (lt_of_le_of_ne hnN hne))

/-- A sum of roughness indicators is exactly the cardinality of the P0072 sifted set. -/
theorem card_eq_sum (N : ℕ) (z : ℝ) :
    ((sifted N z).card : ℂ) =
      ∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime N), psi (n * (N - n)) z := by
  classical
  simp only [psi, sifted, sum_boole]

/-- Buchstab1938 display 7 for the P0072 product sequence, with exact finite endpoints.
This uses the existing proved buchstab_identity once for every product. -/
theorem buchstab_count {N : ℕ} (hN : 1 < N) {w z : ℝ} (hwz : w ≤ z) :
    ((sifted N z).card : ℂ) = (sifted N w).card - removed N w z := by
  classical
  unfold removed
  rw [card_eq_sum, card_eq_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  exact buchstab_identity (product_pos hN hn) hwz

/-- The removed mass is real and is the exact nonnegative difference of the two counts. -/
theorem removed_eq {N : ℕ} (hN : 1 < N) {w z : ℝ} (hwz : w ≤ z) :
    removed N w z = ((sifted N w).card : ℂ) - (sifted N z).card := by
  have h := buchstab_count hN hwz
  linear_combination h

/-- Increasing the strict cutoff removes elements from the P0072 sieve. -/
theorem sifted_antitone (N : ℕ) {w z : ℝ} (hwz : w ≤ z) :
    sifted N z ⊆ sifted N w := by
  intro n hn
  obtain ⟨hnA, hr⟩ := mem_filter.mp hn
  refine mem_filter.mpr ⟨hnA, ?_⟩
  intro p hp hpw
  exact hr p hp (hpw.trans_le hwz)

/-- The real removed mass is nonnegative, including empty sieve sets. -/
theorem removed_re_nonneg {N : ℕ} (hN : 1 < N) {w z : ℝ} (hwz : w ≤ z) :
    0 ≤ (removed N w z).re := by
  rw [removed_eq hN hwz]
  simp only [Complex.sub_re, Complex.natCast_re]
  exact sub_nonneg.mpr (by exact_mod_cast card_le_card (sifted_antitone N hwz))

/-- A concrete even P0072 input with two surviving products at strict cutoff two. -/
theorem instance_ten : (sifted 10 2).card = 4 := by
  classical
  have hr : ∀ n : ℕ, Rough n 2 := by
    intro n p hp hp2
    have h := hp.two_le
    have : (2 : ℝ) ≤ p := by exact_mod_cast h
    linarith
  simp only [sifted, hr, filter_true]
  decide

end LeanLab.AlmostPrimeSums.Finite616
