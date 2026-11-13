/-
P0094 Gallagher 1975 p.131 display 14.
Branch repair of free-nv-minimax/task331. The target statement of the unit is
Linnik.Decomp482b.corrected_energy_decay. Main moved its definitions to
Linnik.Decomp486c and proved it there from the two case estimates, so this folder
carries the statement of the unit beside them, following the t345 pattern.
Source https://doi.org/10.1007/BF01390190
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Linnik.Decomp482b

namespace LeanLab.Linnik.Task331

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp482a
open LeanLab.Linnik.Decomp466a
open LeanLab.Linnik.Decomp1532b (zeroCount excSet)
open LeanLab.Linnik.Decomp482b
open LeanLab.PNTPort.LargeSieve (e)

/-- Gallagher 1975 p.131 display 14 and the paragraph following it, the target statement
of the branch, restated verbatim in this namespace. The proof is main's proof, not a new
one, and the twin adds nothing to main; it is here so the statement of the unit sits in
the folder the gate reads. Axioms: propext, Classical.choice, Quot.sound. -/
theorem t331_corrected_energy_decay :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ r : ℕ, ∃ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) ∧
          normalizedEnergy N θ r γ ≤ C * Real.exp (-c / θ) :=
  LeanLab.Linnik.Decomp482b.corrected_energy_decay

/-- Gallagher 1975 p.131 display 14, the step branch free-nv-minimax/task331 tried to
take. Its proof of the target replaced the open assembly by an appeal to
`density_near_one`, which bounds a zero count, so it needed the principal case decay
without the hypothesis that no exceptional character occurs. This theorem is the
precise content of that attempt: the unconditional principal case decay does imply the
target. Nothing in the lab supplies the premise, and this theorem does not either; the
no exception hypothesis of `Decomp486c.energy_decay_without_exception` is what fails for
the branch, since the exceptional case cannot be dropped. -/
theorem t331_principal_decay_unconditional_suffices
    (hPrincipal :
      ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
        ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          normalizedEnergy N θ 0 0 ≤ C * Real.exp (-c / θ)) :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ r : ℕ, ∃ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) ∧
          normalizedEnergy N θ r γ ≤ C * Real.exp (-c / θ) := by
  obtain ⟨c, C, θ₀, hc, hC, hθ₀, hθ₀1, h⟩ := hPrincipal
  refine LeanLab.Linnik.Decomp486c.corrected_energy_decay_of_cases
    ⟨c, C, θ₀, hc, hC, hθ₀, hθ₀1, fun θ hθ hθle => ?_⟩
    LeanLab.Linnik.Decomp486c.energy_decay_with_exception
  obtain ⟨N₀, hN₀⟩ := h θ hθ hθle
  exact ⟨N₀, fun N hN _ => hN₀ N hN⟩

end LeanLab.Linnik.Task331
