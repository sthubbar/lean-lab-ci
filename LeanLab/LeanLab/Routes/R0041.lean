import Mathlib

/-!
# R-0041, T3 MOONSHOT: density transference for P + P, the removal decoy

Unit U-1370, PC run 20261021T0604Z-1697. AI wrote the Lean code. Binary Goldbach is OPEN.
Nothing here is progress on Goldbach. Label KNOWN in substance, folklore; compare
Alsetri and Shao, Density versions of the binary Goldbach problem, arXiv 2405.18576.

Route: Green-Tao style transference. Majorize the primes by a pseudorandom sieve weight,
pass to a dense model, and conclude `N ∈ A + A` from relative density plus Fourier
pseudorandomness. The lemmas below show that relative density alone can never reach a
fixed `N`: deleting at most `(r_A(N) + 1) / 2` elements of any finite set `A` kills
every representation of `N`.
-/

namespace LeanLab.Routes.R0041

open Finset

/-- The representation set: `a ∈ A`, `a ≤ N`, `N - a ∈ A`.
Plain math: `R_A(N) = {a ∈ A : a ≤ N, N - a ∈ A}`, so `#R_A(N) = r_A(N)` ordered. -/
def reps (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  A.filter (fun a => a ≤ N ∧ N - a ∈ A)

/-- The removed set: representations with the larger summand, `2a ≥ N`.
Plain math: `D = {a ∈ R_A(N) : 2a ≥ N}`. -/
def removed (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (reps A N).filter (fun a => N ≤ 2 * a)

/-- The decoy `A' = A \ D`. -/
def decoy (A : Finset ℕ) (N : ℕ) : Finset ℕ := A \ removed A N

/-- HELPER. Membership in `removed`. -/
theorem mem_removed {A : Finset ℕ} {N a : ℕ} :
    a ∈ removed A N ↔ a ∈ A ∧ a ≤ N ∧ N - a ∈ A ∧ N ≤ 2 * a := by
  simp [removed, reps, and_assoc]

/-- NEW. The decoy misses `N`.
Plain math: if `a, b ∈ A \ D` and `a + b = N` then, taking the larger of the two, it lies in `D`,
a contradiction; so `N ∉ A' + A'`. -/
theorem decoy_misses (A : Finset ℕ) (N : ℕ) :
    ∀ a ∈ decoy A N, ∀ b ∈ decoy A N, a + b ≠ N := by
  intro a ha b hb hab
  simp only [decoy, mem_sdiff, mem_removed, not_and] at ha hb
  rcases le_total b a with h | h
  · exact ha.2 ha.1 (by omega) (by rw [show N - a = b by omega]; exact hb.1) (by omega)
  · exact hb.2 hb.1 (by omega) (by rw [show N - b = a by omega]; exact ha.1) (by omega)

/-- HELPER. The decoy is a subset of `A`. -/
theorem decoy_subset (A : Finset ℕ) (N : ℕ) : decoy A N ⊆ A := sdiff_subset

/-- NEW. Sharp loss bound: `2 #D ≤ r_A(N) + 1`.
Plain math: `a ↦ N - a` maps `D` injectively into `{a ∈ R : 2a ≤ N}`, which is
`R \ D` plus at most the single point `N/2`; so `#D ≤ #R - #D + 1`. -/
theorem two_mul_card_removed_le (A : Finset ℕ) (N : ℕ) :
    2 * #(removed A N) ≤ #(reps A N) + 1 := by
  set D := removed A N
  set R := reps A N
  have hDR : D ⊆ R := filter_subset _ _
  have himg : D.image (fun a => N - a) ⊆ (R \ D) ∪ (R.filter (fun a => 2 * a = N)) := by
    intro x hx
    simp only [mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [mem_removed] at ha
    obtain ⟨haA, haN, hNa, h2⟩ := ha
    have hxR : N - a ∈ R := by
      simp only [R, reps, mem_filter]
      exact ⟨hNa, by omega, by rw [show N - (N - a) = a by omega]; exact haA⟩
    by_cases heq : 2 * (N - a) = N
    · exact mem_union_right _ (mem_filter.2 ⟨hxR, heq⟩)
    · refine mem_union_left _ (mem_sdiff.2 ⟨hxR, ?_⟩)
      rw [mem_removed]; omega
  have hinj : Set.InjOn (fun a => N - a) (D : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_filter, D, removed, reps, mem_filter, Set.mem_ofPred_eq] at ha hb
    simp only at hab
    omega
  have hcard := card_le_card himg
  rw [card_image_of_injOn hinj] at hcard
  have hone : #(R.filter (fun a => 2 * a = N)) ≤ 1 := by
    rw [card_le_one]
    intro a ha b hb
    simp only [mem_filter] at ha hb
    omega
  have hsd : #(R \ D) = #R - #D := card_sdiff_of_subset hDR
  have hle : #D ≤ #R := card_le_card hDR
  have hu := card_union_le (R \ D) (R.filter (fun a => 2 * a = N))
  omega

/-- NEW. Density form: the decoy keeps all but `(r_A(N)+1)/2` elements.
Plain math: `#A' ≥ #A - (r_A(N) + 1)/2`, with `N ∉ A' + A'`. -/
theorem decoy_card (A : Finset ℕ) (N : ℕ) :
    2 * #A ≤ 2 * #(decoy A N) + #(reps A N) + 1 := by
  have h1 : removed A N ⊆ A := fun a ha => (mem_removed.1 ha).1
  have h2 : #(decoy A N) = #A - #(removed A N) := card_sdiff_of_subset h1
  have h3 := card_le_card h1
  have h4 := two_mul_card_removed_le A N
  omega

/-- NEW. Transference blindness: no statement of the form "every `B ⊆ A` with
`#A ≤ 2 #B + r_A(N) + 1` represents `N`" holds, for any `A` and `N`.
Plain math: a density threshold below `1 - (r_A(N)+1)/(2#A)` cannot certify a fixed `N`. -/
theorem no_density_certificate (A : Finset ℕ) (N : ℕ) :
    ¬ ∀ B ⊆ A, 2 * #A ≤ 2 * #B + #(reps A N) + 1 → ∃ a ∈ B, ∃ b ∈ B, a + b = N := by
  intro h
  obtain ⟨a, ha, b, hb, hab⟩ := h (decoy A N) (decoy_subset A N) (decoy_card A N)
  exact decoy_misses A N a ha b hb hab

/-- Vacuity instance: `A = {2,3,5,7}` the primes up to 10, `N = 10`: the decoy is `{2,3}`,
nonempty, and `10 = 3 + 7 = 5 + 5` in `A` is not a sum from the decoy. -/
example : decoy {2, 3, 5, 7} 10 = {2, 3} := by decide

example : ∃ a ∈ ({2, 3, 5, 7} : Finset ℕ), ∃ b ∈ ({2, 3, 5, 7} : Finset ℕ), a + b = 10 :=
  ⟨3, by decide, 7, by decide, rfl⟩

/-- Vacuity instance at `N = 100`, primes up to 100: 25 primes, `r = 12`, 6 removed,
decoy of 19 primes. -/
example : #(decoy ((Finset.range 101).filter Nat.Prime) 100) = 19 := by decide

end LeanLab.Routes.R0041
