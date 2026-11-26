import Mathlib

/-!
Finite selection and counting for Jutila 1977 page 51, display 3.1.
DOI https://doi.org/10.7146/math.scand.a-11701.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.Selection637

open Finset

attribute [local instance] Classical.propDecidable

/-- Jutila page 51, display 3.1, finite packing version of the selection.
A maximal separated subset covers the original set by its conflict neighborhoods.
The bound on each neighborhood gives the counting loss. -/
theorem packing {α : Type*} (u : Finset α) (R : α → α → Prop)
    (hsymm : ∀ {x y}, R x y → R y x) (hirr : ∀ x, ¬ R x x) (K : ℝ)
    (hK : ∀ x ∈ u, ∀ v : Finset α, v ⊆ u →
      (∀ y ∈ v, ¬ R x y) → (v.card : ℝ) ≤ K) :
    ∃ s : Finset α, s ⊆ u ∧ (s : Set α).Pairwise R ∧ (u.card : ℝ) ≤ K * s.card := by
  classical
  let v := u.powerset.filter (fun s : Finset α => (s : Set α).Pairwise R)
  have hv : v.Nonempty := ⟨∅, by simp [v]⟩
  obtain ⟨s, hs, hmax⟩ := v.exists_max_image Finset.card hv
  have hsu : s ⊆ u := mem_powerset.mp (mem_filter.mp hs).1
  have hsep : (s : Set α).Pairwise R := (mem_filter.mp hs).2
  have hcover : u ⊆ s.biUnion (fun x => u.filter (fun y => ¬ R x y)) := by
    intro y hy
    by_contra hn
    have hgood : ∀ x ∈ s, R x y := by
      intro x hx
      by_contra hbad
      exact hn (mem_biUnion.mpr ⟨x, hx, mem_filter.mpr ⟨hy, hbad⟩⟩)
    have hys : y ∉ s := fun h => hirr y (hgood y h)
    have hins : (↑(insert y s) : Set α).Pairwise R := by
      intro a ha b hb hab
      rcases mem_insert.mp ha with hya | has
      · subst a
        rcases mem_insert.mp hb with hyb | hbs
        · exact (hab hyb.symm).elim
        · exact hsymm (hgood b hbs)
      · rcases mem_insert.mp hb with hyb | hbs
        · subst b
          exact hgood a has
        · exact hsep has hbs hab
    have hi : insert y s ∈ v := mem_filter.mpr
      ⟨mem_powerset.mpr (insert_subset hy hsu), hins⟩
    have hc := hmax (insert y s) hi
    rw [card_insert_of_notMem hys] at hc
    omega
  refine ⟨s, hsu, hsep, ?_⟩
  have hc : u.card ≤ ∑ x ∈ s, (u.filter (fun y => ¬ R x y)).card :=
    (card_le_card hcover).trans card_biUnion_le
  calc
    (u.card : ℝ) ≤ ∑ x ∈ s, ((u.filter (fun y => ¬ R x y)).card : ℝ) := by
      exact_mod_cast hc
    _ ≤ ∑ _x ∈ s, K := sum_le_sum (fun x hx =>
      hK x (hsu hx) _ (filter_subset _ _) (fun y hy => (mem_filter.mp hy).2))
    _ = K * s.card := by simp [mul_comm]

/-- Jutila page 51, display 3.1, one representative of each occupied cell.
The cell label includes the character as well as the height interval. -/
theorem cell_representatives {α β : Type*} (u : Finset α) (cell : α → β) :
    ∃ s : Finset α, s ⊆ u ∧ Set.InjOn cell (s : Set α) ∧ s.image cell = u.image cell := by
  classical
  obtain ⟨s, hsu, hinj, himg⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn (u : Set α) (u.image cell)
      (by
        intro y hy
        obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hy
        exact ⟨a, ha, he⟩)
  exact ⟨s, hsu, hinj, himg⟩

/-- Jutila pages 51 and 52, the larger of the two parity classes.
At least half of a finite family lies in one Boolean class. -/
theorem larger_class {α : Type*} (s : Finset α) (evenCell : α → Prop) :
    ∃ b : Bool, s.card ≤ 2 * (s.filter (fun x => decide (evenCell x) = b)).card := by
  classical
  have hsum := Finset.card_filter_add_card_filter_not (s := s) evenCell
  by_cases h : (s.filter evenCell).card ≤ (s.filter (fun x => ¬ evenCell x)).card
  · refine ⟨false, ?_⟩
    simpa only [Bool.decide_false_iff] using (show s.card ≤
      2 * (s.filter (fun x => ¬ evenCell x)).card by omega)
  · refine ⟨true, ?_⟩
    simpa only [Bool.decide_iff] using (show s.card ≤
      2 * (s.filter evenCell).card by omega)

/-- Jutila page 51, display 3.1, distinct cells of one parity are separated.
The cell of t is floor of t divided by the positive mesh width. -/
theorem parity_spacing {δ t u : ℝ} (hδ : 0 < δ)
    (hpar : ⌊t / δ⌋ % 2 = ⌊u / δ⌋ % 2) (hne : ⌊t / δ⌋ ≠ ⌊u / δ⌋) :
    δ ≤ |t - u| := by
  have ht0 := Int.floor_le (t / δ)
  have ht1 := Int.lt_floor_add_one (t / δ)
  have hu0 := Int.floor_le (u / δ)
  have hu1 := Int.lt_floor_add_one (u / δ)
  rcases (show ⌊t / δ⌋ + 2 ≤ ⌊u / δ⌋ ∨ ⌊u / δ⌋ + 2 ≤ ⌊t / δ⌋ by omega) with h | h
  · have hr : (⌊t / δ⌋ : ℝ) + 2 ≤ ⌊u / δ⌋ := by exact_mod_cast h
    have hd : t / δ + 1 ≤ u / δ := by linarith
    have hm := (le_div_iff₀ hδ).mp hd
    have he : t / δ * δ = t := div_mul_cancel₀ t hδ.ne'
    have hdiff : δ ≤ u - t := by nlinarith
    exact hdiff.trans (by simpa only [abs_sub_comm] using (le_abs_self (u - t)))
  · have hr : (⌊u / δ⌋ : ℝ) + 2 ≤ ⌊t / δ⌋ := by exact_mod_cast h
    have hd : u / δ + 1 ≤ t / δ := by linarith
    have hm := (le_div_iff₀ hδ).mp hd
    have he : u / δ * δ = u := div_mul_cancel₀ u hδ.ne'
    have hdiff : δ ≤ t - u := by nlinarith
    exact hdiff.trans (le_abs_self _)

end LeanLab.LPZ2007.Selection637

#print axioms LeanLab.LPZ2007.Selection637.packing

#print axioms LeanLab.LPZ2007.Selection637.cell_representatives
#print axioms LeanLab.LPZ2007.Selection637.larger_class
#print axioms LeanLab.LPZ2007.Selection637.parity_spacing
