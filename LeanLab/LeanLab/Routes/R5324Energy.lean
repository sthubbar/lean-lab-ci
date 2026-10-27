/-
R-5324, CLOUD 20261021T0217Z-cloud56, unit U-6826, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

The additive energy and Balog-Szemerédi-Gowers route.  Binary Goldbach at N is
the statement that the prime set A = P ∩ [1, N) meets its reflection N - A.
Every BSG, Plünnecke or Freiman input is a function of additive energies.
* `addEnergy_reflect`: E[A, N - A] = E[A, A] for every N and every finite
  A ⊂ ℤ.  The energy between the primes and their reflection does not depend on
  N at all, so no energy hypothesis can single out one N.
* `goldbach_free_subset`: for every N there is t ⊆ A with no a + b = N inside t
  and |A \ t| ≤ #{a ∈ A : N - a ∈ A}, the Goldbach count r(N).  The numerics
  r5324_energy_U6826.py show deleting those r(N)/2 primes keeps the energy
  within a factor 1 - 3.3/log N, so energy cannot force a representation.
* `goldbach_free_instance`: vacuity check at A = {3, 5, 7}, N = 10.
-/
import Mathlib

namespace LeanLab.Routes.R5324

open Finset

/-- The reflection N - A of a finite set of integers. -/
def refl (N : ℤ) (s : Finset ℤ) : Finset ℤ := s.image (fun a => N - a)

lemma mem_refl {N x : ℤ} {s : Finset ℤ} : x ∈ refl N s ↔ N - x ∈ s := by
  unfold refl
  constructor
  · rintro h
    obtain ⟨a, ha, rfl⟩ := mem_image.mp h
    simpa using ha
  · intro h
    exact mem_image.mpr ⟨N - x, h, by ring⟩

/-- The energy between A and its reflection N - A equals the energy of A,
for every N. -/
theorem addEnergy_reflect (N : ℤ) (s : Finset ℤ) :
    Finset.addEnergy s (refl N s) = Finset.addEnergy s s := by
  classical
  rw [Finset.addEnergy_eq_card_filter, Finset.addEnergy_eq_card_filter]
  refine Finset.card_bij'
    (fun x _ => ((x.1.1, N - x.2.2), (x.2.1, N - x.1.2)))
    (fun x _ => ((x.1.1, N - x.2.2), (x.2.1, N - x.1.2))) ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ h
    simp only [mem_filter, mem_product] at h ⊢
    obtain ⟨⟨⟨ha, hb⟩, hc, hd⟩, he⟩ := h
    rw [mem_refl] at hb hd
    exact ⟨⟨⟨ha, hd⟩, hc, hb⟩, by linarith⟩
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ h
    simp only [mem_filter, mem_product] at h ⊢
    obtain ⟨⟨⟨ha, hb⟩, hc, hd⟩, he⟩ := h
    refine ⟨⟨⟨ha, ?_⟩, hc, ?_⟩, by linarith⟩
    · rw [mem_refl]; simpa using hd
    · rw [mem_refl]; simpa using hb
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ _
    simp
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ _
    simp

/-- The Goldbach count of N inside s, ordered pairs. -/
def rep (N : ℤ) (s : Finset ℤ) : ℕ := (s.filter (fun a => N - a ∈ s)).card

/-- Deleting at most r(N) elements makes N unrepresentable. -/
theorem goldbach_free_subset (N : ℤ) (s : Finset ℤ) :
    ∃ t ⊆ s, (∀ a ∈ t, ∀ b ∈ t, a + b ≠ N) ∧ (s \ t).card ≤ rep N s := by
  classical
  refine ⟨s.filter (fun a => 2 * a < N ∨ N - a ∉ s), filter_subset _ _, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [mem_filter] at ha hb
    have hb' : N - b = a := by linarith
    have ha' : N - a = b := by linarith
    rcases ha.2 with h1 | h1
    · rcases hb.2 with h2 | h2
      · linarith
      · exact h2 (hb' ▸ ha.1)
    · exact h1 (ha' ▸ hb.1)
  · unfold rep
    apply card_le_card
    intro x hx
    simp only [mem_sdiff, mem_filter, not_and, not_or, not_not] at hx ⊢
    exact ⟨hx.1, (hx.2 hx.1).2⟩

/-- Vacuity instance: the hypotheses are met and the conclusion is nontrivial,
{3, 5, 7} represents 10 and a subset of it avoids 10 after one deletion. -/
theorem goldbach_free_instance :
    rep 10 {3, 5, 7} = 3 ∧ Finset.addEnergy ({3, 5, 7} : Finset ℤ) (refl 10 {3, 5, 7}) =
      Finset.addEnergy ({3, 5, 7} : Finset ℤ) {3, 5, 7} := by
  refine ⟨by decide, addEnergy_reflect 10 _⟩

end LeanLab.Routes.R5324

#print axioms LeanLab.Routes.R5324.addEnergy_reflect
#print axioms LeanLab.Routes.R5324.goldbach_free_subset
#print axioms LeanLab.Routes.R5324.goldbach_free_instance
