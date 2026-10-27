/-
R-route of unit U-6831, CLOUD 20261021T0316Z-cloud57, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

The group Goldbach route.  In a finite group G with S a set of elements of prime
order, the representation count c(g) = #{x ∈ S : x⁻¹ g ∈ S} is what binary Goldbach
asks about.  In nonabelian simple groups such as PSL₂(p) every g ≠ 1 is represented,
because S is a union of conjugacy classes, so c is a class function and the
Frobenius character formula damps every nontrivial character by its degree.
* `count_conj`: if S is closed under conjugation, c(h g h⁻¹) = c(g).
* `comm_conj_closed`: in a commutative group every set is closed under conjugation,
  so normality carries no information in (ℤ, +), where every character has degree 1.
* `kill_subset`: for any S and g there is T ⊆ S with no x ∈ T, x⁻¹ g ∈ T, and
  |S \ T| ≤ c(g); such a T is not conjugation closed in general.
* `count_univ`: vacuity, c(g) = |G| for S = G.
-/
import Mathlib

namespace LeanLab.Routes.U6831

open Finset

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The Goldbach count of g in S: the x ∈ S with x⁻¹ g ∈ S. -/
def count (S : Finset G) (g : G) : ℕ := (S.filter (fun x => x⁻¹ * g ∈ S)).card

/-- S is closed under conjugation, a union of conjugacy classes. -/
def ConjClosed (S : Finset G) : Prop := ∀ x ∈ S, ∀ h : G, h * x * h⁻¹ ∈ S

omit [Fintype G] in
/-- For a conjugation closed S the Goldbach count is a class function. -/
theorem count_conj (S : Finset G) (hS : ConjClosed S) (g h : G) :
    count S (h * g * h⁻¹) = count S g := by
  unfold count
  symm
  refine Finset.card_nbij' (fun x => h * x * h⁻¹) (fun x => h⁻¹ * x * h) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
    refine ⟨hS x hx.1 h, ?_⟩
    have := hS _ hx.2 h
    convert this using 1
    group
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
    refine ⟨?_, ?_⟩
    · have := hS x hx.1 h⁻¹
      simpa using this
    · have := hS _ hx.2 h⁻¹
      convert this using 1
      group
  · intro x _
    group
  · intro x _
    group

/-- In a commutative group every set is conjugation closed. -/
theorem comm_conj_closed {A : Type*} [CommGroup A] (S : Finset A) :
    ∀ x ∈ S, ∀ h : A, h * x * h⁻¹ ∈ S := by
  intro x hx h
  simpa [mul_comm h x, mul_assoc] using hx

/-- Deleting at most c(g) elements of S kills every representation of g. -/
theorem kill_subset (S : Finset G) (g : G) :
    ∃ T ⊆ S, (∀ x ∈ T, x⁻¹ * g ∉ T) ∧ (S \ T).card ≤ count S g := by
  refine ⟨S.filter (fun x => x⁻¹ * g ∉ S), Finset.filter_subset _ _, ?_, ?_⟩
  · intro x hx hmem
    exact (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hmem).1
  · unfold count
    apply le_of_eq
    congr 1
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    tauto

/-- Vacuity: with S = G every g has |G| representations. -/
theorem count_univ (g : G) : count (Finset.univ : Finset G) g = Fintype.card G := by
  unfold count
  simp

end LeanLab.Routes.U6831

#print axioms LeanLab.Routes.U6831.count_conj
#print axioms LeanLab.Routes.U6831.comm_conj_closed
#print axioms LeanLab.Routes.U6831.kill_subset
#print axioms LeanLab.Routes.U6831.count_univ
