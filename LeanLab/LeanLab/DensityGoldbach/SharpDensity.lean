/-
P0038 Shao 2012, arXiv 1206.6139 v2, Section 1 after Theorem 1.1: "The constant 5/8 in
Theorem 1.1 cannot be improved. In fact, we may take A = {p ∈ P : p ≡ 1, 2, 4, 7, 13 mod 15}.
Then δ(A) = 5/8. It is not hard to see that if N ≡ 14 (mod 15) then N cannot be written as sum
of three elements of A."

Here the density `δ(A) = 5/8` is PROVED, using `pi_ap_lower` (primes in a reduced class get at
least their share, from the lab's Siegel-Walfisz chain), so the whole sharpness remark is formal:
Theorem 1.1 with `≥ 5/8` in place of `> 5/8` is false.

AI-written Lean code, Claude, 2026-10-21, run PC 20261021T0403Z-14344, unit U-1347.
Ternary Goldbach is a theorem; binary Goldbach is OPEN.
-/
import LeanLab.DensityGoldbach.Local
import LeanLab.DensityGoldbach.PrimesAP

open Finset Filter
open scoped Classical

namespace LeanLab.DensityGoldbach

/-- Shao's sharpness set: primes `≡ 1, 2, 4, 7, 13 mod 15`. -/
def shaoSet : Set ℕ := {p | p.Prime ∧ (p : ZMod 15) ∈ S15}

/-- The residues of `S15` as naturals. -/
def R5 : Finset ℕ := {1, 2, 4, 7, 13}

/-- The other reduced residues mod 15. -/
def R3 : Finset ℕ := {8, 11, 14}

/-- Primes up to `N` in the class `r mod 15`. -/
noncomputable def cnt (r N : ℕ) : ℕ := #{p ∈ range (N + 1) | p.Prime ∧ p % 15 = r % 15}

/-- Primes up to `N` whose residue mod 15 lies in `R`. -/
noncomputable def cntR (R : Finset ℕ) (N : ℕ) : ℕ := #{p ∈ range (N + 1) | p.Prime ∧ p % 15 ∈ R}

/-- Primes up to `N`. -/
noncomputable def piN (N : ℕ) : ℕ := #{p ∈ range (N + 1) | p.Prime}

lemma mem_S15_iff (n : ℕ) : (n : ZMod 15) ∈ S15 ↔ n % 15 ∈ R5 := by
  have h : (n : ZMod 15) = ((n % 15 : ℕ) : ZMod 15) := (ZMod.natCast_mod n 15).symm
  rw [h]
  have key : ∀ r < 15, ((r : ℕ) : ZMod 15) ∈ S15 ↔ r ∈ R5 := by decide
  exact key _ (Nat.mod_lt _ (by norm_num))

lemma cntR_eq (R : Finset ℕ) (hR : ∀ r ∈ R, r < 15) (N : ℕ) :
    cntR R N = ∑ r ∈ R, cnt r N := by
  unfold cntR cnt
  rw [card_eq_sum_card_fiberwise (f := fun p => p % 15) (t := R)
    (fun p hp => (mem_filter.1 hp).2.2)]
  refine sum_congr rfl fun r hr => ?_
  congr 1
  ext p
  simp only [mem_filter, mem_range]
  rw [Nat.mod_eq_of_lt (hR r hr)]
  constructor
  · rintro ⟨⟨h1, h2, _⟩, h4⟩; exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h4⟩; exact ⟨⟨h1, h2, h4 ▸ hr⟩, h4⟩

lemma cntR_union_le (N : ℕ) : cntR R5 N + cntR R3 N ≤ piN N := by
  have hd : Disjoint R5 R3 := by decide
  have h1 : cntR (R5 ∪ R3) N = cntR R5 N + cntR R3 N := by
    rw [cntR_eq _ (by decide), cntR_eq _ (by decide), cntR_eq _ (by decide), sum_union hd]
  rw [← h1]
  exact card_le_card fun p hp => by
    simp only [mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩

lemma relRatio_shao (N : ℕ) : relRatio shaoSet N = (cntR R5 N : ℝ) / piN N := by
  unfold relRatio cntR piN
  congr 2
  · congr 1; ext n
    simp only [mem_filter, mem_Icc, mem_range, shaoSet, Set.mem_setOf_eq, mem_S15_iff]
    constructor
    · rintro ⟨⟨_, h2⟩, ⟨h3, h4⟩, _⟩; exact ⟨by omega, h3, h4⟩
    · rintro ⟨h1, h3, h4⟩; exact ⟨⟨h3.one_lt.le, by omega⟩, ⟨h3, h4⟩, h3⟩
  · congr 1; ext n
    simp only [mem_filter, mem_Icc, mem_range]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨by omega, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h3.one_lt.le, by omega⟩, h3⟩

lemma ev_class (r : ℕ) (hr : Nat.Coprime r 15) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N in atTop, (1 - η) / 8 * (piN N : ℝ) ≤ cnt r N := by
  obtain ⟨N₀, h⟩ := pi_ap_lower 15 r (by norm_num) hr η hη
  refine eventually_atTop.2 ⟨N₀, fun N hN => ?_⟩
  have := h N hN
  rw [totient15] at this
  exact_mod_cast this

lemma ev_sum (R : Finset ℕ) (hR : ∀ r ∈ R, Nat.Coprime r 15) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N in atTop, (R.card : ℝ) * ((1 - η) / 8 * (piN N : ℝ)) ≤ ∑ r ∈ R, (cnt r N : ℝ) := by
  have := (eventually_all_finset R).2 fun r hr => ev_class r (hR r hr) η hη
  filter_upwards [this] with N hN
  calc (R.card : ℝ) * ((1 - η) / 8 * (piN N : ℝ)) = ∑ _r ∈ R, (1 - η) / 8 * (piN N : ℝ) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := sum_le_sum hN

/-- The relative ratio of Shao's set tends to `5/8`. -/
theorem tendsto_relRatio_shao : Tendsto (relRatio shaoSet) atTop (nhds (5 / 8)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h5 := ev_sum R5 (by decide) ε hε
  have h3 := ev_sum R3 (by decide) ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((h5.and h3).and (eventually_ge_atTop 2))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨a5, a3⟩, hN2⟩ := hN₀ N hN
  have c5 : R5.card = 5 := by decide
  have c3 : R3.card = 3 := by decide
  rw [c5] at a5; rw [c3] at a3
  rw [← Nat.cast_sum, ← cntR_eq _ (by decide)] at a5 a3
  have hle : (cntR R5 N : ℝ) + cntR R3 N ≤ piN N := by exact_mod_cast cntR_union_le N
  have hpos : (0 : ℝ) < piN N := by
    have : 0 < piN N := card_pos.2 ⟨2, by simp [mem_filter, mem_range, Nat.prime_two]; omega⟩
    exact_mod_cast this
  rw [Real.dist_eq, relRatio_shao, abs_lt]
  push_cast at a5 a3
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hpos]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hpos]; nlinarith

/-- **Shao, Section 1: `δ(A) = 5/8`** for `A` the primes `≡ 1, 2, 4, 7, 13 mod 15`. -/
theorem lowerDensity_shaoSet : lowerDensity shaoSet = 5 / 8 :=
  tendsto_relRatio_shao.liminf_eq

lemma shaoSet_sub : shaoSet ⊆ P := fun _ h => h.1

/-- Shao's set misses every `N ≡ 14 mod 15`, among them infinitely many odd `N`. -/
theorem not_largeOdd_shaoSet : ¬ LargeOddIn shaoSet shaoSet shaoSet := by
  rintro ⟨N₀, h⟩
  have hodd : Odd (30 * N₀ + 29) := ⟨15 * N₀ + 14, by ring⟩
  exact shao_example_set (30 * N₀ + 29) (by omega) (h _ (by omega) hodd)

/-- **The sharpness remark in full**: a set of primes with relative lower density exactly `5/8`
whose triple sumset misses infinitely many odd integers. -/
theorem shao_sharp : ∃ A : Set ℕ, A ⊆ P ∧ lowerDensity A = 5 / 8 ∧ ¬ LargeOddIn A A A :=
  ⟨shaoSet, shaoSet_sub, lowerDensity_shaoSet, not_largeOdd_shaoSet⟩

/-- Theorem 1.1 with the non-strict hypothesis `δ(A) ≥ 5/8`. -/
def Shao11Weak : Prop := ∀ A : Set ℕ, A ⊆ P → 5 / 8 ≤ lowerDensity A → LargeOddIn A A A

/-- **5/8 cannot be improved**: Theorem 1.1 fails with `≥ 5/8`. -/
theorem not_shao11Weak : ¬ Shao11Weak := fun h =>
  not_largeOdd_shaoSet (h shaoSet shaoSet_sub lowerDensity_shaoSet.ge)

/-- For every `c ≤ 5/8`, relative lower density `≥ c` does not suffice. -/
theorem not_shao11_below (c : ℝ) (hc : c ≤ 5 / 8) :
    ¬ ∀ A : Set ℕ, A ⊆ P → c ≤ lowerDensity A → LargeOddIn A A A := fun h =>
  not_largeOdd_shaoSet (h shaoSet shaoSet_sub (lowerDensity_shaoSet ▸ hc))

end LeanLab.DensityGoldbach
