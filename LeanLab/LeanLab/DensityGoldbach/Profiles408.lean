/-
The explicit residue weight in Shao 1206.6139v2 pages 15 to 16.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.AlsetriTransfer
import LeanLab.DensityGoldbach.Prop16

open Finset
open scoped Classical

namespace LeanLab.DensityGoldbach.Profiles408

/-- Shao page 16, identification of units modulo m with odd units modulo 2m.
The representative is chosen in the interval from zero to 2m. -/
def oddRepresentative (m : ℕ) [NeZero m] (b : ZMod m) : ℕ :=
  if Odd b.val then b.val else b.val + m

/-- Shao page 15, the displayed residue profile before equation 28.
The strict cutoff is encoded by 3p < 2n. This is a finite weighted sum. -/
noncomputable def primeProfile (A : Set ℕ) (W n : ℕ) (δ : ℝ) (b : ℕ) : ℝ :=
  max ((3 * (W.totient : ℝ) / (2 * n)) *
    ∑ p ∈ (range (n + 1)).filter
      (fun p => p ∈ A ∧ p % W = b % W ∧ 3 * p < 2 * n), Real.log p - δ / 8) 0

/-- Shao page 16, the displayed profile after writing m = W/2. -/
noncomputable def halfProfile (A : Set ℕ) (z n : ℕ) (δ : ℝ)
    (m : ℕ) [NeZero m] (b : ZMod m) : ℝ :=
  primeProfile A (primorial z) n δ (oddRepresentative m b)

/-- Shao page 16, odd representatives stay below 2m and reduce to b modulo m. -/
theorem oddRepresentative_properties (m : ℕ) [NeZero m] (hodd : Odd m) (b : ZMod m) :
    oddRepresentative m b < 2 * m ∧ Odd (oddRepresentative m b) ∧
      oddRepresentative m b % m = b.val := by
  have hb := ZMod.val_lt b
  unfold oddRepresentative
  split_ifs with h
  · exact ⟨by omega, h, Nat.mod_eq_of_lt hb⟩
  · have heven : Even b.val := (Nat.not_odd_iff_even).mp h
    exact ⟨by omega, heven.add_odd hodd, by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hb]⟩

/-- Shao page 16, the parity lift of equation 30 from m to W = 2m.
Mathlib's coprime congruence theorem supplies the CRT step. -/
theorem triple_parity_lift (m n b₁ b₂ b₃ : ℕ) (hm : Odd m) (hn : Odd n)
    (h₁ : Odd b₁) (h₂ : Odd b₂) (h₃ : Odd b₃)
    (hcong : Nat.ModEq m n (b₁ + b₂ + b₃)) :
    Nat.ModEq (2 * m) n (b₁ + b₂ + b₃) := by
  apply (Nat.modEq_and_modEq_iff_modEq_mul (Nat.coprime_two_left.mpr hm)).mp
  refine ⟨?_, hcong⟩
  unfold Nat.ModEq
  rw [Nat.odd_iff.mp hn, Nat.odd_iff.mp ((h₁.add_odd h₂).add_odd h₃)]

end LeanLab.DensityGoldbach.Profiles408

#print axioms LeanLab.DensityGoldbach.Profiles408.oddRepresentative_properties
#print axioms LeanLab.DensityGoldbach.Profiles408.triple_parity_lift
