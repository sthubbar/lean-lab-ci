/-
# R-0016 addendum: additive energy is difference data

Unit U-1128, T3 MOONSHOT, run 20261019T2303Z-16260.

Plain math. For finite A ⊂ ℤ, the second moment of the Goldbach counts equals the second
moment of the difference counts, both being the additive energy:

  Σ_N s_A(N)² = #{(a,b,c,e) ∈ A⁴ : a + b = c + e} = Σ_h d_A(h)².

So every L² statement about the Goldbach function of a set, mean square, variance, the
Cauchy-Schwarz sumset bound |A+A| ≥ |A|⁴/E(A), is a statement about difference data, and by
`R0016.difference_data_not_sum_data` cannot decide one N. The homometric pair has equal
energy, 66 for both by Python, equality kernel checked by `homometric_energy`, and different s(4).

AI wrote this Lean code. KNOWN mathematics. Binary Goldbach is OPEN.
-/
import LeanLab.Routes.R0016Homometric

namespace LeanLab.Routes.R0016

open Finset

/-- Quadruples with equal sums. -/
def eSum (A : Finset ℤ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter fun x => x.1.1 + x.1.2 = x.2.1 + x.2.2

/-- Quadruples with equal differences. -/
def eDif (A : Finset ℤ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter fun x => x.1.1 - x.1.2 = x.2.1 - x.2.2

lemma card_eSum (A : Finset ℤ) :
    (eSum A).card = ∑ N ∈ (A ×ˢ A).image (fun p => p.1 + p.2), sumCount A N ^ 2 := by
  rw [card_eq_sum_card_fiberwise (f := fun x => x.1.1 + x.1.2)
    (t := (A ×ˢ A).image (fun p => p.1 + p.2))]
  · refine sum_congr rfl fun N _ => ?_
    have : (eSum A).filter (fun x => x.1.1 + x.1.2 = N) =
        ((A ×ˢ A).filter fun p => p.1 + p.2 = N) ×ˢ ((A ×ˢ A).filter fun p => p.1 + p.2 = N) := by
      ext ⟨⟨a, b⟩, ⟨c, e⟩⟩
      simp only [eSum, mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩, h6⟩; exact ⟨⟨⟨h1, h2⟩, h6⟩, ⟨h3, h4⟩, by omega⟩
      · rintro ⟨⟨⟨h1, h2⟩, h6⟩, ⟨h3, h4⟩, h7⟩; exact ⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, by omega⟩, h6⟩
    rw [this, card_product, sumCount, sq]
  · intro x hx
    simp only [eSum, coe_filter, mem_product, Set.mem_ofPred_eq] at hx
    simp only [coe_image, coe_product, Set.mem_image, Set.mem_prod, mem_coe]
    exact ⟨x.1, ⟨hx.1.1.1, hx.1.1.2⟩, rfl⟩

lemma card_eDif (A : Finset ℤ) :
    (eDif A).card = ∑ h ∈ (A ×ˢ A).image (fun p => p.1 - p.2), diffCount A h ^ 2 := by
  rw [card_eq_sum_card_fiberwise (f := fun x => x.1.1 - x.1.2)
    (t := (A ×ˢ A).image (fun p => p.1 - p.2))]
  · refine sum_congr rfl fun h _ => ?_
    have : (eDif A).filter (fun x => x.1.1 - x.1.2 = h) =
        ((A ×ˢ A).filter fun p => p.1 - p.2 = h) ×ˢ ((A ×ˢ A).filter fun p => p.1 - p.2 = h) := by
      ext ⟨⟨a, b⟩, ⟨c, e⟩⟩
      simp only [eDif, mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩, h6⟩; exact ⟨⟨⟨h1, h2⟩, h6⟩, ⟨h3, h4⟩, by omega⟩
      · rintro ⟨⟨⟨h1, h2⟩, h6⟩, ⟨h3, h4⟩, h7⟩; exact ⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, by omega⟩, h6⟩
    rw [this, card_product, diffCount, sq]
  · intro x hx
    simp only [eDif, coe_filter, mem_product, Set.mem_ofPred_eq] at hx
    simp only [coe_image, coe_product, Set.mem_image, Set.mem_prod, mem_coe]
    exact ⟨x.1, ⟨hx.1.1.1, hx.1.1.2⟩, rfl⟩

lemma card_eSum_eq_card_eDif (A : Finset ℤ) : (eSum A).card = (eDif A).card := by
  refine card_nbij' (fun x => ((x.1.1, x.2.1), (x.2.2, x.1.2)))
    (fun y => ((y.1.1, y.2.2), (y.1.2, y.2.1))) ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, ⟨c, e⟩⟩ hx
    simp only [eSum, eDif, coe_filter, mem_product, Set.mem_ofPred_eq] at hx ⊢
    exact ⟨⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.1.2.2, hx.1.1.2⟩, by linarith [hx.2]⟩
  · rintro ⟨⟨a, b⟩, ⟨c, e⟩⟩ hx
    simp only [eSum, eDif, coe_filter, mem_product, Set.mem_ofPred_eq] at hx ⊢
    exact ⟨⟨⟨hx.1.1.1, hx.1.2.2⟩, hx.1.1.2, hx.1.2.1⟩, by linarith [hx.2]⟩
  · rintro ⟨⟨a, b⟩, ⟨c, e⟩⟩ _; rfl
  · rintro ⟨⟨a, b⟩, ⟨c, e⟩⟩ _; rfl

/-- **Energy identity**: `Σ_N s_A(N)² = Σ_h d_A(h)²`. -/
theorem energy_identity (A : Finset ℤ) :
    ∑ N ∈ (A ×ˢ A).image (fun p => p.1 + p.2), sumCount A N ^ 2 =
      ∑ h ∈ (A ×ˢ A).image (fun p => p.1 - p.2), diffCount A h ^ 2 := by
  rw [← card_eSum, ← card_eDif, card_eSum_eq_card_eDif]

/-- The homometric pair has equal energy, so equal Goldbach second moments. -/
theorem homometric_energy :
    ∑ N ∈ (A0 ×ˢ A0).image (fun p => p.1 + p.2), sumCount A0 N ^ 2 =
      ∑ N ∈ (B0 ×ˢ B0).image (fun p => p.1 + p.2), sumCount B0 N ^ 2 := by
  rw [energy_identity, energy_identity]
  decide

/-- The barrier in one line: equal Goldbach second moments, different Goldbach count at 4. -/
theorem second_moment_not_pointwise :
    (∑ N ∈ (A0 ×ˢ A0).image (fun p => p.1 + p.2), sumCount A0 N ^ 2 =
      ∑ N ∈ (B0 ×ˢ B0).image (fun p => p.1 + p.2), sumCount B0 N ^ 2) ∧
    0 < sumCount A0 4 ∧ sumCount B0 4 = 0 :=
  ⟨homometric_energy, sum_four⟩

/-- The common value: energy 66 for `A0`. -/
theorem energy_A0 : (eSum A0).card = 66 := by decide

end LeanLab.Routes.R0016
