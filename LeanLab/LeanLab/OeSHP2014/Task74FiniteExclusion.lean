import Mathlib

/-! The finite inclusion exclusion step behind equation 2.1 on page 2045.
Taking the base set to be even starts removes the singleton prime two boundary.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

/-- Inclusion exclusion inside a distinguished base event. -/
theorem inclusion_exclusion_with_base {ι α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (s : Finset ι) (S : ι → Finset α) :
    ((B ∩ s.inf (fun i => (S i)ᶜ)).card : ℤ) =
      ∑ t ∈ s.powerset, (-1 : ℤ)^t.card * ((B ∩ t.inf S).card : ℤ) := by
  classical
  have h := Finset.inclusion_exclusion_sum_inf_compl (G := ℤ) s S
    (fun a => if a ∈ B then 1 else 0)
  simpa [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm,
    zsmul_eq_mul] using h

/-- Inclusion exclusion on an arbitrary finite domain, with no finite ambient type. -/
theorem finite_exclusion {ι α : Type*} [DecidableEq α]
    (U : Finset α) (s : Finset ι) (P : ι → α → Prop) [∀ i, DecidablePred (P i)] :
    ((U.filter (fun a => ∀ i ∈ s, ¬ P i a)).card : ℤ) =
      ∑ t ∈ s.powerset, (-1 : ℤ)^t.card *
        ((U.filter (fun a => ∀ i ∈ t, P i a)).card : ℤ) := by
  classical
  let S : ι → Finset U := fun i => Finset.univ.filter fun a => P i a.val
  have h := inclusion_exclusion_with_base (Finset.univ : Finset U) s S
  have hc (Q : α → Prop) [DecidablePred Q] :
      ((Finset.univ : Finset U).filter fun a => Q a.val).card = (U.filter Q).card := by
    apply Finset.card_bij (fun a _ => a.val)
    · intro a ha
      exact Finset.mem_filter.mpr ⟨a.property, (Finset.mem_filter.mp ha).2⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro a ha
      refine ⟨⟨a, (Finset.mem_filter.mp ha).1⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp ha).2
  have hm (t : Finset ι) (A : ι → Finset U) (a : U) :
      a ∈ t.inf A ↔ ∀ i ∈ t, a ∈ A i := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih => simp [Finset.inf_insert, hi, Finset.inf_eq_inter, ih]
  have he (t : Finset ι) : t.inf S = Finset.univ.filter (fun a : U => ∀ i ∈ t, P i a.val) := by
    ext a
    simp only [hm, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
  have hn : s.inf (fun i => (S i)ᶜ) =
      Finset.univ.filter (fun a : U => ∀ i ∈ s, ¬ P i a.val) := by
    ext a
    simp only [hm, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
  have hl := hc (fun a => ∀ i ∈ s, ¬ P i a)
  have hr (t : Finset ι) := hc (fun a => ∀ i ∈ t, P i a)
  simpa only [Finset.univ_inter, hn, he, hl, hr] using h

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.inclusion_exclusion_with_base

#print axioms LeanLab.OeSHP2014.Task74.finite_exclusion
