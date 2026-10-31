/-
P0070 Section 6, page 367, the primitive character reduction before 36.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.Section6

namespace LeanLab.PerelliPintz1992.Section6
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A character modulo q is induced from the fixed character ψ modulo r. -/
def Induced {r q : ℕ+} (ψ : DirichletCharacter ℂ (r : ℕ))
    (χ : DirichletCharacter ℂ (q : ℕ)) : Prop :=
  ∃ h : (r : ℕ) ∣ (q : ℕ), ψ.changeLevel h = χ

/-- All induced characters with modulus in Q, retaining the modulus as part of the index. -/
def inducedFamily (Q : Finset ℕ+) {r : ℕ+} (ψ : DirichletCharacter ℂ (r : ℕ)) :
    Finset (Σ q : Q, DirichletCharacter ℂ (q.val : ℕ)) :=
  univ.filter (fun c => Induced ψ c.2)

/-- A fixed character induces exactly one character at each allowed multiple of its modulus. -/
theorem inducedFamily_card (Q : Finset ℕ+) {r : ℕ+} (ψ : DirichletCharacter ℂ (r : ℕ)) :
    (inducedFamily Q ψ).card = (Q.filter (fun q : ℕ+ => (r : ℕ) ∣ (q : ℕ))).card := by
  apply Finset.card_nbij (fun c => c.1.val)
  · intro c hc
    obtain ⟨h, _⟩ := (mem_filter.mp hc).2
    exact mem_filter.mpr ⟨c.1.property, h⟩
  · rintro ⟨⟨q, hq⟩, χ⟩ hc ⟨⟨q', hq'⟩, χ'⟩ hc' heq
    dsimp at heq
    subst q'
    obtain ⟨h, hh⟩ := (mem_filter.mp hc).2
    obtain ⟨h', hh'⟩ := (mem_filter.mp hc').2
    change (r : ℕ) ∣ (q : ℕ) at h h'
    change ψ.changeLevel h = χ at hh
    change ψ.changeLevel h' = χ' at hh'
    have hchars : χ = χ' := hh.symm.trans hh'
    exact Sigma.ext rfl (heq_of_eq hchars)
  · intro q hq
    obtain ⟨hqQ, h⟩ := mem_filter.mp hq
    refine ⟨⟨⟨q, hqQ⟩, ψ.changeLevel h⟩, ?_, rfl⟩
    exact mem_filter.mpr ⟨mem_univ _, h, rfl⟩

#print axioms inducedFamily_card


/-- At most X/r positive multiples of r occur in any modulus set bounded by X. -/
theorem modulus_multiples_card_le (Q : Finset ℕ+) (r : ℕ+) (X : ℕ)
    (hQ : ∀ q ∈ Q, (q : ℕ) ≤ X) :
    (Q.filter (fun q : ℕ+ => (r : ℕ) ∣ (q : ℕ))).card ≤ X / (r : ℕ) := by
  let T := Q.filter (fun q : ℕ+ => (r : ℕ) ∣ (q : ℕ))
  have hc : T.card ≤ (Finset.Icc 1 (X / (r : ℕ))).card := by
    apply Finset.card_le_card_of_injOn (fun q : ℕ+ => (q : ℕ) / (r : ℕ))
    · intro q hq
      obtain ⟨hqQ, hd⟩ := mem_filter.mp hq
      apply mem_Icc.mpr
      refine ⟨?_, Nat.div_le_div_right (hQ q hqQ)⟩
      exact Nat.div_pos (Nat.le_of_dvd q.property hd) r.property
    · intro q hq q' hq' heq
      dsimp at heq
      have h1 := Nat.div_mul_cancel (mem_filter.mp hq).2
      have h2 := Nat.div_mul_cancel (mem_filter.mp hq').2
      apply Subtype.ext
      change (q : ℕ) = (q' : ℕ)
      rw [← h1, ← h2, heq]
  simpa [T, Nat.card_Icc] using hc

#print axioms modulus_multiples_card_le


/-- The real counting bound used before equation 36. -/
theorem inducedFamily_card_le (Q : Finset ℕ+) {r : ℕ+}
    (ψ : DirichletCharacter ℂ (r : ℕ)) (X : ℕ)
    (hQ : ∀ q ∈ Q, (q : ℕ) ≤ X) :
    ((inducedFamily Q ψ).card : ℝ) ≤ (X : ℝ) / (r : ℝ) := by
  rw [inducedFamily_card]
  calc
    ((Q.filter (fun q : ℕ+ => (r : ℕ) ∣ (q : ℕ))).card : ℝ) ≤
        ((X / (r : ℕ) : ℕ) : ℝ) := by
      exact_mod_cast modulus_multiples_card_le Q r X hQ
    _ ≤ (X : ℝ) / (r : ℝ) := Nat.cast_div_le

#print axioms inducedFamily_card_le

end
end LeanLab.PerelliPintz1992.Section6
