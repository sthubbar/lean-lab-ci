/-
R-0014, T3 MOONSHOT, unit U-1106, PC run 20261019T2003Z-20508.
Fake primes: Goldbach for one N is not a linear statistic.

From any finite set `A`, the primes up to `N` say, remove `R`, the larger member of each pair
`p + q = N`; then no two elements of `A' = A \ R` sum to `N`, and `#R` is at most the number of
pairs. Add fakes `M`, each `m ≤ N` with `N − m` outside `A' ∪ M`; then still no two elements of
`F = A' ∪ M` sum to `N`. If the fakes match `R` class by class mod `W`, `F` and `A` have the same
count in every residue class mod `W` and the same size.

So no statement about the counts of primes in residue classes, the inputs of the major arcs,
can by itself force `N = p + q` for one given `N`. Numerics in numerics/r0014_fake_primes*.py
show the change can also be kept near √N in every exponential sum, below the Vinogradov scale.
KNOWN in spirit as a heuristic; the Lean lemmas are elementary. AI wrote this Lean code.
Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Routes.R0014

open Finset

/-- `R`, the larger member `q`, `N ≤ 2q ≤ 2N`, of each pair `(N − q, q)` inside `A`. -/
def removeSet (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  A.filter (fun q => N ≤ 2 * q ∧ q ≤ N ∧ N - q ∈ A)

/-- `A' = A \ R`. -/
def thinned (A : Finset ℕ) (N : ℕ) : Finset ℕ := A \ removeSet A N

/-- No two elements of `A'`, equal ones allowed, sum to `N`. -/
theorem thinned_no_pair (A : Finset ℕ) (N : ℕ) :
    ∀ x ∈ thinned A N, ∀ y ∈ thinned A N, x + y ≠ N := by
  intro x hx y hy hxy
  simp only [thinned, removeSet, mem_sdiff, mem_filter, not_and] at hx hy
  rcases le_total x y with h | h
  · exact hy.2 hy.1 (by omega) (by omega) (by rw [show N - y = x by omega]; exact hx.1)
  · exact hx.2 hx.1 (by omega) (by omega) (by rw [show N - x = y by omega]; exact hy.1)

/-- `#R` is at most the number of pairs `p ≤ q` in `A` with `p + q = N`. -/
theorem card_removeSet_le (A : Finset ℕ) (N : ℕ) :
    (removeSet A N).card ≤ ((A ×ˢ A).filter (fun pq => pq.1 + pq.2 = N ∧ pq.1 ≤ pq.2)).card := by
  apply Finset.card_le_card_of_injOn (fun q => (N - q, q))
  · intro q hq
    simp only [removeSet, coe_filter, Set.mem_setOf_eq] at hq
    simp only [coe_filter, mem_product, Set.mem_setOf_eq]
    exact ⟨⟨hq.2.2.2, hq.1⟩, by omega, by omega⟩
  · intro a _ b _ h
    simp only [Prod.mk.injEq] at h
    exact h.2

/-- Adding fakes `m ≤ N` with `N − m` outside `A' ∪ M` keeps `N` out of `F + F`. -/
theorem fake_no_pair (A M : Finset ℕ) (N : ℕ)
    (hM : ∀ m ∈ M, m ≤ N ∧ N - m ∉ thinned A N ∧ N - m ∉ M) :
    ∀ x ∈ thinned A N ∪ M, ∀ y ∈ thinned A N ∪ M, x + y ≠ N := by
  intro x hx y hy hxy
  rw [mem_union] at hx hy
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · exact thinned_no_pair A N x hx y hy hxy
    · have := hM y hy
      rw [show N - y = x by omega] at this
      exact this.2.1 hx
  · have := hM x hx
    rw [show N - x = y by omega] at this
    rcases hy with hy | hy
    · exact this.2.1 hy
    · exact this.2.2 hy

/-- Class counts: if `M` is disjoint from `A'` and some bijection `R → M` keeps every residue
class mod `W`, then `F = A' ∪ M` and `A` have the same count in every class mod `W`. -/
theorem class_count_eq (A M : Finset ℕ) (N W : ℕ) (hdisj : Disjoint (thinned A N) M)
    (e : ℕ → ℕ) (he : ∀ q ∈ removeSet A N, e q ∈ M)
    (hinj : ∀ q₁ ∈ removeSet A N, ∀ q₂ ∈ removeSet A N, e q₁ = e q₂ → q₁ = q₂)
    (hsurj : ∀ m ∈ M, ∃ q ∈ removeSet A N, e q = m)
    (hmod : ∀ q ∈ removeSet A N, e q % W = q % W) (a : ℕ) :
    ((thinned A N ∪ M).filter (fun x => x % W = a)).card = (A.filter (fun x => x % W = a)).card := by
  have hRA : removeSet A N ⊆ A := filter_subset _ _
  have hA : A = thinned A N ∪ removeSet A N := by
    unfold thinned; rw [sdiff_union_of_subset hRA]
  have hdA : Disjoint (thinned A N) (removeSet A N) := by unfold thinned; exact sdiff_disjoint
  have hM : (M.filter (fun x => x % W = a)).card = ((removeSet A N).filter (fun x => x % W = a)).card := by
    symm
    apply Finset.card_bij (fun q _ => e q)
    · intro q hq
      rw [mem_filter] at hq ⊢
      exact ⟨he q hq.1, by rw [hmod q hq.1]; exact hq.2⟩
    · intro q₁ h₁ q₂ h₂ h
      exact hinj q₁ (mem_filter.mp h₁).1 q₂ (mem_filter.mp h₂).1 h
    · intro m hm
      rw [mem_filter] at hm
      obtain ⟨q, hq, rfl⟩ := hsurj m hm.1
      exact ⟨q, mem_filter.mpr ⟨hq, by rw [← hmod q hq]; exact hm.2⟩, rfl⟩
  conv_rhs => rw [hA]
  rw [filter_union, filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj),
    card_union_of_disjoint (disjoint_filter_filter hdA), hM]

/-- The fake prime theorem: the same count as `A` in every class mod `W`, and `N ∉ F + F`. -/
theorem fake_primes (A M : Finset ℕ) (N W : ℕ) (hdisj : Disjoint (thinned A N) M)
    (hM : ∀ m ∈ M, m ≤ N ∧ N - m ∉ thinned A N ∧ N - m ∉ M)
    (e : ℕ → ℕ) (he : ∀ q ∈ removeSet A N, e q ∈ M)
    (hinj : ∀ q₁ ∈ removeSet A N, ∀ q₂ ∈ removeSet A N, e q₁ = e q₂ → q₁ = q₂)
    (hsurj : ∀ m ∈ M, ∃ q ∈ removeSet A N, e q = m)
    (hmod : ∀ q ∈ removeSet A N, e q % W = q % W) :
    (∀ x ∈ thinned A N ∪ M, ∀ y ∈ thinned A N ∪ M, x + y ≠ N) ∧
    (∀ a, ((thinned A N ∪ M).filter (fun x => x % W = a)).card = (A.filter (fun x => x % W = a)).card) ∧
    (thinned A N ∪ M).card = A.card := by
  refine ⟨fake_no_pair A M N hM, class_count_eq A M N W hdisj e he hinj hsurj hmod, ?_⟩
  have := class_count_eq A M N 1 hdisj e he hinj hsurj (by intro q _; rw [Nat.mod_one, Nat.mod_one]) 0
  rwa [Finset.filter_true_of_mem (fun x _ => Nat.mod_one x),
    Finset.filter_true_of_mem (fun x _ => Nat.mod_one x)] at this

/-- Vacuity: `A = {3, 5, 7}`, `N = 10`. Thinning leaves `{3}`; the fakes `M = {2, 4}` satisfy
the hypothesis of `fake_no_pair`, and `F = {2, 3, 4}` has the size of `A` and no pair summing to
`10`. -/
theorem vacuity_thinned : thinned {3, 5, 7} 10 = {3} := by decide

theorem vacuity_fakes :
    (∀ m ∈ ({2, 4} : Finset ℕ), m ≤ 10 ∧ 10 - m ∉ thinned {3, 5, 7} 10 ∧ 10 - m ∉ ({2, 4} : Finset ℕ)) ∧
    (thinned {3, 5, 7} 10 ∪ {2, 4}).card = ({3, 5, 7} : Finset ℕ).card := by decide

end LeanLab.Routes.R0014
