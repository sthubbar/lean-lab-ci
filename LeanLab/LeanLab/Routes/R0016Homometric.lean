/-
# R-0016, difference data versus sum data: homometric sets

Unit U-1117, T3 MOONSHOT, run 20261019T2303Z-16260.

Plain math. For a finite set `A ⊂ ℤ` let `d_A(h) = #{(a, b) ∈ A² : a − b = h}`, the pair
correlation or difference function, the data of the Hardy-Littlewood k = 2 conjecture and of
GPY and Maynard sieves, and `s_A(N) = #{(a, b) ∈ A² : a + b = N}`, the Goldbach count.

* `diffCount_reflect`: the reflection `c − A` has the same difference function as `A`.
* `sumCount_reflect`: its Goldbach count at `N` is that of `A` at `2c − N`.
* `homometric_classic`: the sets `{0,1,4,10,12,17}` and `{0,1,8,11,13,17}` have the same
  difference function, are not translates or reflections of each other, yet `4` is a sum
  from the first and not from the second.

So difference data, however complete, does not determine sum data; a route to binary
Goldbach through pair correlations of the primes must add phase information, which is the
circle method's `S(α)²` against `|S(α)|²`, the minor arc problem. Barrier map, KNOWN
mathematics, homometric sets go back to Patterson 1944.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Routes.R0016

open Finset

/-- `d_A(h)`, the number of ordered pairs in `A` with difference `h`. -/
def diffCount (A : Finset ℤ) (h : ℤ) : ℕ := ((A ×ˢ A).filter fun p => p.1 - p.2 = h).card

/-- `s_A(N)`, the number of ordered pairs in `A` with sum `N`. -/
def sumCount (A : Finset ℤ) (N : ℤ) : ℕ := ((A ×ˢ A).filter fun p => p.1 + p.2 = N).card

/-- The reflection `c − A`. -/
def reflect (c : ℤ) (A : Finset ℤ) : Finset ℤ := A.image fun a => c - a

lemma mem_reflect {c x : ℤ} {A : Finset ℤ} : x ∈ reflect c A ↔ c - x ∈ A := by
  simp only [reflect, mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro h; exact ⟨c - x, h, by ring⟩

/-- Reflection keeps the difference function. -/
theorem diffCount_reflect (c : ℤ) (A : Finset ℤ) (h : ℤ) :
    diffCount (reflect c A) h = diffCount A h := by
  unfold diffCount
  refine Finset.card_nbij' (fun p => (c - p.2, c - p.1)) (fun p => (c - p.2, c - p.1))
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_reflect] at hp ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa using hp.1.2
    · simpa using hp.1.1
    · linarith [hp.2]
  · intro p hp
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_reflect] at hp ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa using hp.1.2
    · simpa using hp.1.1
    · linarith [hp.2]
  · intro p _; ext <;> simp
  · intro p _; ext <;> simp

/-- Reflection moves the Goldbach count from `2c − N` to `N`. -/
theorem sumCount_reflect (c : ℤ) (A : Finset ℤ) (N : ℤ) :
    sumCount (reflect c A) N = sumCount A (2 * c - N) := by
  unfold sumCount
  refine Finset.card_nbij' (fun p => (c - p.1, c - p.2)) (fun p => (c - p.1, c - p.2))
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_reflect] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2⟩, by linarith [hp.2]⟩
  · intro p hp
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_reflect] at hp ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa using hp.1.1
    · simpa using hp.1.2
    · linarith [hp.2]
  · intro p _; ext <;> simp
  · intro p _; ext <;> simp

def A0 : Finset ℤ := {0, 1, 4, 10, 12, 17}
def B0 : Finset ℤ := {0, 1, 8, 11, 13, 17}

/-- Every difference lies in `[-17, 17]` for both sets. -/
lemma diffCount_A0_out (h : ℤ) (hh : 17 < |h|) : diffCount A0 h = 0 := by
  unfold diffCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  simp only [A0, mem_product, mem_insert, mem_singleton] at hp
  rcases hp with ⟨h1 | h1 | h1 | h1 | h1 | h1, h2 | h2 | h2 | h2 | h2 | h2⟩ <;>
    · intro e; rw [h1, h2] at e; subst e; norm_num at hh

lemma diffCount_B0_out (h : ℤ) (hh : 17 < |h|) : diffCount B0 h = 0 := by
  unfold diffCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  simp only [B0, mem_product, mem_insert, mem_singleton] at hp
  rcases hp with ⟨h1 | h1 | h1 | h1 | h1 | h1, h2 | h2 | h2 | h2 | h2 | h2⟩ <;>
    · intro e; rw [h1, h2] at e; subst e; norm_num at hh

lemma diffCount_eq_inside : ∀ h ∈ Finset.Icc (-17 : ℤ) 17, diffCount A0 h = diffCount B0 h := by
  decide

/-- The classic homometric pair: the same difference function. -/
theorem homometric_classic : ∀ h : ℤ, diffCount A0 h = diffCount B0 h := by
  intro h
  by_cases hh : 17 < |h|
  · rw [diffCount_A0_out h hh, diffCount_B0_out h hh]
  · apply diffCount_eq_inside
    rw [Finset.mem_Icc]
    constructor <;> [linarith [neg_abs_le h]; linarith [le_abs_self h]]

/-- Not a translate: `B0 ≠ A0 + t` for every `t`; the minima force `t = 0`. -/
theorem not_translate : ∀ t : ℤ, B0 ≠ A0.image (· + t) := by
  intro t h
  have h0 : (0 : ℤ) ∈ A0.image (· + t) := h ▸ (by decide : (0 : ℤ) ∈ B0)
  simp only [A0, mem_image, mem_insert, mem_singleton] at h0
  obtain ⟨a, ha, hat⟩ := h0
  have h17 : (17 : ℤ) + t ∈ B0 := h ▸ (by simp [A0])
  have h0' : (0 : ℤ) + t ∈ B0 := h ▸ (by simp [A0])
  simp only [B0, mem_insert, mem_singleton] at h17 h0'
  have : t = 0 := by omega
  subst this
  have h4 : (4 : ℤ) ∈ B0 := h ▸ (by simp [A0])
  exact absurd h4 (by decide)

/-- Not a reflection: `B0 ≠ c − A0` for every `c`. -/
theorem not_reflect : ∀ c : ℤ, B0 ≠ reflect c A0 := by
  intro c h
  have h17 : c - 0 ∈ B0 := h ▸ (by rw [mem_reflect]; simp [A0])
  have h0' : c - 17 ∈ B0 := h ▸ (by rw [mem_reflect]; simp [A0])
  simp only [B0, mem_insert, mem_singleton] at h17 h0'
  have : c = 17 := by omega
  subst this
  have h13 : (17 - 4 : ℤ) ∈ B0 := h ▸ (by rw [mem_reflect]; simp [A0])
  have h7 : (17 - 10 : ℤ) ∈ B0 := h ▸ (by rw [mem_reflect]; simp [A0])
  exact absurd h7 (by decide)

/-- Yet the Goldbach counts differ: `4` is a sum from `A0` and not from `B0`. -/
theorem sum_four : 0 < sumCount A0 4 ∧ sumCount B0 4 = 0 := by decide

/-- The barrier in one line: same difference function, different sum sets. -/
theorem difference_data_not_sum_data :
    ∃ A B : Finset ℤ, (∀ h, diffCount A h = diffCount B h) ∧
      (∀ t, B ≠ A.image (· + t)) ∧ (∀ c, B ≠ reflect c A) ∧
      0 < sumCount A 4 ∧ sumCount B 4 = 0 :=
  ⟨A0, B0, homometric_classic, not_translate, not_reflect, sum_four⟩

end LeanLab.Routes.R0016
