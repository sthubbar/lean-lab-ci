/-
Jia 1996 pages 262, 263 and 279, Lemma 21 and display 48.
Source https://doi.org/10.4064/aa-77-3-207-287.
Exact arithmetic support for the Omega4 integer model.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
namespace LeanLab.Languasco2004.Cofactor708
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pages 262 and 263 support: multiplication by a rough positive divisor
identifies sifted multiples with sifted cofactors in the exact quotient interval. -/
theorem sifted_multiples_card (L U d : ℕ) (z : ℝ) (hd : 0 < d)
    (hrough : ∀ r : ℕ, r.Prime → (r : ℝ) < z → ¬ r ∣ d) :
    ((Ioc L U).filter (fun a => d ∣ a ∧
      ∀ r : ℕ, r.Prime → (r : ℝ) < z → ¬ r ∣ a)).card =
    ((Ioc (L / d) (U / d)).filter (fun m =>
      ∀ r : ℕ, r.Prime → (r : ℝ) < z → ¬ r ∣ m)).card := by
  classical
  symm
  apply Finset.card_bij (fun m _ => m * d)
  · intro m hm
    obtain ⟨hmI, hmR⟩ := mem_filter.mp hm
    obtain ⟨hL, hU⟩ := mem_Ioc.mp hmI
    apply mem_filter.mpr
    refine ⟨mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul hd).mp hL,
      (Nat.le_div_iff_mul_le hd).mp hU⟩, dvd_mul_left d m, ?_⟩
    intro r hr hrz hrmd
    rcases hr.dvd_mul.mp hrmd with hrm | hrd
    · exact hmR r hr hrz hrm
    · exact hrough r hr hrz hrd
  · intro m hm k hk hmk
    exact Nat.eq_of_mul_eq_mul_right hd hmk
  · intro a ha
    obtain ⟨haI, hda, haR⟩ := mem_filter.mp ha
    obtain ⟨m, rfl⟩ := hda
    refine ⟨m, mem_filter.mpr ⟨?_, ?_⟩, Nat.mul_comm m d⟩
    · apply mem_Ioc.mpr
      constructor
      · apply (Nat.div_lt_iff_lt_mul hd).mpr
        simpa only [Nat.mul_comm] using (mem_Ioc.mp haI).1
      · apply (Nat.le_div_iff_mul_le hd).mpr
        simpa only [Nat.mul_comm] using (mem_Ioc.mp haI).2
    · intro r hr hrz hrm
      exact haR r hr hrz (dvd_mul_of_dvd_right hrm d)

#print axioms sifted_multiples_card
end
end LeanLab.Languasco2004.Cofactor708
