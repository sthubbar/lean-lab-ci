/-
P0089 pages 224 and 227: bounded exception counts and eventual representation.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Elementary96

namespace LeanLab.Languasco2004

open Finset Real

attribute [local instance] Classical.propDecidable

/-- Pages 224 and 227: a set of positive integer exceptions is finite exactly
when its counts in the intervals from 1 to X have one uniform bound. -/
theorem finite_iff_bounded_interval_count (P : ℕ → Prop) :
    {n : ℕ | 1 ≤ n ∧ P n}.Finite ↔
      ∃ C : ℕ, ∀ X : ℝ,
        ((Finset.range (⌊X⌋₊ + 1)).filter
          (fun n : ℕ => (1 : ℝ) ≤ n ∧ (n : ℝ) ≤ X ∧ P n)).card ≤ C := by
  constructor
  · intro h
    refine ⟨h.toFinset.card, fun X => Finset.card_le_card ?_⟩
    intro n hn
    apply h.mem_toFinset.mpr
    obtain ⟨_, hn, _, hp⟩ := Finset.mem_filter.mp hn
    exact ⟨by exact_mod_cast hn, hp⟩
  · rintro ⟨C, hC⟩
    by_contra h
    obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq h (C + 1)
    have hsub : s ⊆ (Finset.range (⌊((s.sup id : ℕ) : ℝ)⌋₊ + 1)).filter
        (fun n : ℕ => (1 : ℝ) ≤ n ∧ (n : ℝ) ≤ ((s.sup id : ℕ) : ℝ) ∧ P n) := by
      intro n hn
      have hnN : n ≤ s.sup id := Finset.le_sup (f := id) hn
      have hp := hs hn
      apply Finset.mem_filter.mpr
      refine ⟨?_, by exact_mod_cast hp.1, by exact_mod_cast hnN, hp.2⟩
      rw [Nat.floor_natCast, Finset.mem_range]
      omega
    have hle := (Finset.card_le_card hsub).trans (hC ((s.sup id : ℕ) : ℝ))
    omega

#print axioms finite_iff_bounded_interval_count

/-- Pages 224 and 227: finiteness of positive integer exceptions is equivalent
to the absence of exceptions beyond a natural threshold. -/
theorem finite_positive_iff_eventually_not (P : ℕ → Prop) :
    {n : ℕ | 1 ≤ n ∧ P n}.Finite ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ P n := by
  rw [Set.finite_iff_bddAbove]
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N + 1, fun n hn hp => ?_⟩
    have hb := hN (show n ∈ {n : ℕ | 1 ≤ n ∧ P n} from ⟨by omega, hp⟩)
    omega
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    by_contra h
    exact hN n (by omega) hn.2

#print axioms finite_positive_iff_eventually_not

/-- Pages 224 and 227: an eventual constant bound for the counting function
already forces the positive exception set to be finite. -/
theorem finite_iff_eventually_bounded_interval_count (P : ℕ → Prop) :
    {n : ℕ | 1 ≤ n ∧ P n}.Finite ↔
      ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
        (((Finset.range (⌊X⌋₊ + 1)).filter
          (fun n : ℕ => (1 : ℝ) ≤ n ∧ (n : ℝ) ≤ X ∧ P n)).card : ℝ) ≤ C := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := (finite_iff_bounded_interval_count P).mp h
    refine ⟨(C : ℝ) + 1, 0, by positivity, fun X _ => ?_⟩
    exact_mod_cast Nat.le_succ_of_le (hC X)
  · rintro ⟨C, X₀, _, hC⟩
    by_contra h
    obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq h (⌊C⌋₊ + 1)
    let N : ℕ := max (s.sup id) ⌈X₀⌉₊
    have hXN : X₀ ≤ (N : ℝ) := (Nat.le_ceil X₀).trans (by
      exact_mod_cast (le_max_right (s.sup id) ⌈X₀⌉₊))
    have hsub : s ⊆ (Finset.range (⌊(N : ℝ)⌋₊ + 1)).filter
        (fun n : ℕ => (1 : ℝ) ≤ n ∧ (n : ℝ) ≤ N ∧ P n) := by
      intro n hn
      have hnN : n ≤ N := (Finset.le_sup (f := id) hn).trans (le_max_left _ _)
      have hp := hs hn
      apply Finset.mem_filter.mpr
      refine ⟨?_, by exact_mod_cast hp.1, by exact_mod_cast hnN, hp.2⟩
      rw [Nat.floor_natCast, Finset.mem_range]
      omega
    have hle := (Finset.card_le_card hsub).trans (Nat.le_floor (hC N hXN))
    omega

#print axioms finite_iff_eventually_bounded_interval_count

/-- Page 224: bounded global Goldbach exception counts are equivalent to
Goldbach representations for all sufficiently large even integers. -/
theorem EX_bounded_iff_eventual_goldbach :
    (∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → (EX X : ℝ) ≤ C) ↔
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → 4 ≤ n → IsGoldbachSum n := by
  have hcount := finite_iff_eventually_bounded_interval_count InE
  have hfinite := finite_positive_iff_eventually_not InE
  have hkey : (∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → (EX X : ℝ) ≤ C) ↔
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ InE n := by
    simpa only [EX, EXH, add_sub_cancel] using hcount.symm.trans hfinite
  rw [hkey]
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn he h4 => ?_⟩
    by_contra hg
    exact hN n hn ⟨he, by omega, hg⟩
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn he => ?_⟩
    have h4 : 4 ≤ n := by
      have hmod := Nat.even_iff.mp he.1
      have h2 := he.2.1
      omega
    exact he.2.2 (hN n hn he.1 h4)

#print axioms EX_bounded_iff_eventual_goldbach

/-- Page 227: bounded global Hardy Littlewood exception counts are equivalent
to eventual representation as an HL-number or a perfect power.
This uses the sealed IsHL and InEk conventions. -/
theorem Ek_bounded_iff_eventual_representation (k : ℕ) :
    (∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → (EkXH k 1 (X - 1) : ℝ) ≤ C) ↔
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsHL k n ∨ ∃ m : ℕ, m ^ k = n := by
  have hcount := finite_iff_eventually_bounded_interval_count (InEk k)
  have hfinite := finite_positive_iff_eventually_not (InEk k)
  have hkey : (∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
      (EkXH k 1 (X - 1) : ℝ) ≤ C) ↔
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ InEk k n := by
    simpa only [EkXH, add_sub_cancel] using hcount.symm.trans hfinite
  rw [hkey]
  simp only [InEk, not_and_or, not_not]

#print axioms Ek_bounded_iff_eventual_representation

end LeanLab.Languasco2004
