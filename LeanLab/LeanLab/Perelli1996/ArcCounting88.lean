/-
P0083, page 483, equations 12 through 14. The interval counting step.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.Perelli1996.Farey
open Finset Set
attribute [local instance] Classical.propDecidable

/-- A query shorter than every arc meets at most two arcs in an ordered dissection.
This isolates the elementary counting step of equations 12 through 14 on page 483. -/
theorem short_interval_meets_at_most_two {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (left right : ι → ℝ) {x y δ : ℝ}
    (hδ : 0 < δ) (hshort : y - x < δ)
    (hwidth : ∀ i ∈ s, δ ≤ right i - left i)
    (horder : ∀ i ∈ s, ∀ j ∈ s, i < j → right i ≤ left j) :
    ((s.filter (fun i => (Set.Icc x y ∩ Set.Icc (left i) (right i)).Nonempty)).card) ≤ 2 := by
  classical
  let t := s.filter (fun i => (Set.Icc x y ∩ Set.Icc (left i) (right i)).Nonempty)
  have hbad (i j k : ι) (hi : i ∈ t) (hj : j ∈ t) (hk : k ∈ t)
      (hij : i < j) (hjk : j < k) : False := by
    obtain ⟨his, ⟨p, hpq, hpi⟩⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjs, _⟩ := Finset.mem_filter.mp hj
    obtain ⟨hks, ⟨r, hrq, hrk⟩⟩ := Finset.mem_filter.mp hk
    have h1 := horder i his j hjs hij
    have h2 := horder j hjs k hks hjk
    have hw := hwidth j hjs
    linarith [hpq.1, hpi.2, hrq.2, hrk.1]
  apply Nat.le_of_not_gt
  intro hcard
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hcard
  change a ∈ t at ha
  change b ∈ t at hb
  change c ∈ t at hc
  rcases lt_or_gt_of_ne hab with hab | hba
  · rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact hbad a b c ha hb hc hab hbc
    · rcases lt_or_gt_of_ne hac with hac | hca
      · exact hbad a c b ha hc hb hac hcb
      · exact hbad c a b hc ha hb hca hab
  · rcases lt_or_gt_of_ne hac with hac | hca
    · exact hbad b a c hb ha hc hba hac
    · rcases lt_or_gt_of_ne hbc with hbc | hcb
      · exact hbad b c a hb hc ha hbc hca
      · exact hbad c b a hc hb ha hcb hba

end LeanLab.Perelli1996.Farey
