/-
Audit of the two leaves of SPLIT_major_arc_energy_exceptional.
Gallagher 1975 p.127 Theorem 3 and p.131 display 13 bound the DIFFERENCE of the
major arc integral and the main term. The split asks for a separate bound on each
summand. Decomp497a already proves the separate main leaf equivalent to eventual
absence of exceptional conductors below P at all small theta. This file adds the
matching statement for the separate arc leaf: it holds vacuously under that absence,
and together with the faithful difference bound it is equivalent to that absence.
So both leaves are equivalent to a Landau Siegel type absence statement that the
paper never asserts. This is a QUESTION about the lab split and asserts no paper error.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.Decomp497a

namespace LeanLab.Linnik.Audit1122ArcLeafNoException

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp1532b (Jn singSeries majorArcs excSet)
open LeanLab.Linnik.U7204 (Sg)
open LeanLab.Linnik.Decomp466a
open LeanLab.Linnik.Decomp482a
open LeanLab.Linnik.Decomp482b

/-- Gallagher 1975 pp.127 and 131, lab split audit.
Eventual absence of exceptional conductors below P at all small theta makes the
separate arc leaf of SPLIT_major_arc_energy_exceptional hold vacuously, since the
leaf only quantifies over positive r coming from an exceptional conductor. -/
theorem separate_arc_bound_of_eventual_no_exception
    (hz : ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      ∀ᶠ N : ℕ in Filter.atTop,
        ¬ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ) :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
              ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n) := by
  obtain ⟨θz, hθz, hz⟩ := hz
  refine ⟨1, min θz 1, by norm_num, lt_min hθz (by norm_num), min_le_right _ _, ?_⟩
  intro θ hθ hθ₀
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hz θ hθ (hθ₀.trans (min_le_left _ _)))
  refine ⟨N₀, ?_⟩
  intro N hN r γ hcase hr n hn
  rcases hcase with h0 | ⟨x, hx, hrx, hrP, _, _, _⟩
  · omega
  · exact False.elim (hN₀ N hN ⟨x, hx, by simpa only [hrx] using hrP⟩)

/-- CONDITIONAL ON the faithful difference bound hError, which is the Decomp486b
statement major_arc_energy_exceptional, Gallagher 1975 p.127 Theorem 3.
Gallagher 1975 pp.127 and 131, lab split audit equivalence.
Given the faithful difference bound, the separate arc leaf is equivalent to eventual
absence of exceptional conductors below P at all small theta. No side is asserted. -/
theorem separate_arc_bound_iff_eventual_no_exception
    (hError : ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n)) :
    (∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
              ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n)) ↔
      ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
        ∀ᶠ N : ℕ in Filter.atTop,
          ¬ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ :=
  ⟨fun hArc => LeanLab.Linnik.Decomp497a.separate_arc_bound_forces_eventual_no_exception
      hArc hError,
    separate_arc_bound_of_eventual_no_exception⟩

end LeanLab.Linnik.Audit1122ArcLeafNoException

#print axioms LeanLab.Linnik.Audit1122ArcLeafNoException.separate_arc_bound_of_eventual_no_exception
#print axioms LeanLab.Linnik.Audit1122ArcLeafNoException.separate_arc_bound_iff_eventual_no_exception
