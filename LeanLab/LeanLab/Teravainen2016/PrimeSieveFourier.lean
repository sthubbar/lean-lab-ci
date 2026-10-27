/-
P0076 Lemma 5.4, page 19. Prime modulus local Fourier bounds for an affine sieve.
These bounds are uniform in the affine shift.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.NormalizedFourier

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Removing T from a cyclic group leaves a nontrivial character sum of norm at most card T. -/
theorem character_complement_bound {N : ℕ} [NeZero N] (k : ZMod N) (hk : k ≠ 0)
    (T : Finset (ZMod N)) :
    ‖∑ x ∈ Tᶜ, ZMod.stdAddChar (k * x)‖ ≤ (T.card : ℝ) := by
  have hsum : ∑ x : ZMod N, ZMod.stdAddChar (k * x) = 0 := by
    simpa [mul_comm, hk] using LeanLab.Routes.R0001.sum_stdAddChar_mul k
  have hs := sum_add_sum_compl T (fun x : ZMod N => ZMod.stdAddChar (k * x))
  rw [hsum] at hs
  have he : ∑ x ∈ Tᶜ, ZMod.stdAddChar (k * x) = -(∑ x ∈ T, ZMod.stdAddChar (k * x)) := by
    linear_combination hs
  rw [he, norm_neg]
  calc
    _ ≤ ∑ x ∈ T, ‖ZMod.stdAddChar (k * x)‖ := norm_sum_le _ _
    _ = _ := by simp [ZMod.stdAddChar_apply]

/-- Over a prime field an affine map preserves the number of forbidden residues. -/
theorem affine_forbidden_preimage_card {p : ℕ} [Fact p.Prime] (a b : ZMod p) (ha : a ≠ 0)
    (F : Finset (ZMod p)) :
    #{x : ZMod p | a * x + b ∈ F} ≤ F.card := by
  have hx : ∀ x z : ZMod p, x = (z - b) / a ↔ a * x + b = z := by
    intro x z
    rw [eq_div_iff ha]
    constructor <;> intro h <;> linear_combination h
  have he : (univ : Finset (ZMod p)).filter (fun x => a * x + b ∈ F) =
      F.image (fun z => (z - b) / a) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h
      exact ⟨a * x + b, h, ((hx x (a * x + b)).mpr rfl).symm⟩
    · rintro ⟨z, hz, he⟩
      have hh := (hx x z).mp he.symm
      simpa [hh] using hz
  rw [he]
  exact card_image_le

/-- A nontrivial character over affine sifted residues is bounded by the forbidden count. -/
theorem affine_sifted_character_bound {p : ℕ} [Fact p.Prime] (a b k : ZMod p) (hk : k ≠ 0)
    (F : Finset (ZMod p)) :
    ‖∑ x ∈ (univ : Finset (ZMod p)).filter (fun x => a * x + b ∉ F),
      ZMod.stdAddChar (k * x)‖ ≤ (F.card : ℝ) := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b ∈ F
    · simp [hb]
    · simp only [zero_mul, zero_add, hb, not_false_eq_true, filter_true]
      have hs : ∑ x : ZMod p, ZMod.stdAddChar (k * x) = 0 := by
        simpa [mul_comm, hk] using LeanLab.Routes.R0001.sum_stdAddChar_mul k
      rw [hs, norm_zero]
      positivity
  · let T := (univ : Finset (ZMod p)).filter (fun x => a * x + b ∈ F)
    have he : (univ : Finset (ZMod p)).filter (fun x => a * x + b ∉ F) = Tᶜ := by
      ext x
      simp [T]
    rw [he]
    exact (character_complement_bound k hk T).trans (by
      exact_mod_cast affine_forbidden_preimage_card a b ha F)

/-- The two forbidden residues in the half dimensional sieve cost at most 2. -/
theorem affine_two_residue_bound {p : ℕ} [Fact p.Prime] (a b k : ZMod p) (hk : k ≠ 0) :
    ‖∑ x ∈ (univ : Finset (ZMod p)).filter (fun x => a * x + b ≠ 0 ∧ a * x + b ≠ 1),
      ZMod.stdAddChar (k * x)‖ ≤ 2 := by
  have h := affine_sifted_character_bound a b k hk ({0, 1} : Finset (ZMod p))
  have he : (univ : Finset (ZMod p)).filter (fun x => a * x + b ∉ ({0, 1} : Finset (ZMod p))) =
      (univ : Finset (ZMod p)).filter (fun x => a * x + b ≠ 0 ∧ a * x + b ≠ 1) := by
    ext x
    simp
  rw [he] at h
  exact h.trans (by exact_mod_cast (card_le_two : #({0, 1} : Finset (ZMod p)) ≤ 2))

/-- Sifting only the zero residue costs at most 1. -/
theorem affine_one_residue_bound {p : ℕ} [Fact p.Prime] (a b k : ZMod p) (hk : k ≠ 0) :
    ‖∑ x ∈ (univ : Finset (ZMod p)).filter (fun x => a * x + b ≠ 0),
      ZMod.stdAddChar (k * x)‖ ≤ 1 := by
  simpa using affine_sifted_character_bound a b k hk ({0} : Finset (ZMod p))

example : ∃ k : ZMod 5, k ≠ 0 := ⟨1, by decide⟩

#print axioms character_complement_bound
#print axioms affine_forbidden_preimage_card
#print axioms affine_sifted_character_bound
#print axioms affine_two_residue_bound
#print axioms affine_one_residue_bound

end LeanLab.Teravainen2016
