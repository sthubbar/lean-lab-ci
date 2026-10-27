/-
R-5250, CLOUD 20261020T1816Z-cloud48, unit U-6714, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

Optimal transport between μ_N, the counting measure on the primes p ≤ N - 2,
and its reflection ν_N, the counting measure on N - p.
* `goldbach_iff_mismatch_lt`: for the zero-one cost, the q → 0 end of the
  W_q^q family, the optimal cost is the mismatched mass |A| - r(N); a
  representation N = a + b inside A exists iff this cost is below |A|.
* `fake_one_mod_six_no_rep`: the fake multiset f(p) = 6⌊p/6⌋ + 1, every point
  moved at most 4, has no representation of any N ≡ 0 mod 6.
* `pair_dev_lipschitz`: moving the two points of a pair by d₁, d₂ changes the
  pairing deviation |a + b - N| by at most d₁ + d₂, so the W_1 cost moves by
  at most 8 per unit mass under the fake map: W_1 is blind to r(N).
* `w1_linear_of_dominance`: if every monotone pair has a + b < N, the W_1 cost
  Σ |a + b - N| equals Σ (N - a - b), a linear statistic.
-/
import Mathlib

namespace LeanLab.Routes.R5250

/-- Zero-one transport cost: Goldbach inside `A` for `N` iff the mismatched
mass, the points `a` with `N - a ∉ A`, is smaller than `|A|`. -/
theorem goldbach_iff_mismatch_lt (N : ℕ) (A : Finset ℕ) :
    (∃ a ∈ A, N - a ∈ A) ↔ (A.filter (fun a => N - a ∉ A)).card < A.card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := A) (p := fun a => N - a ∈ A)
  constructor
  · rintro ⟨a, ha, hb⟩
    have : 0 < (A.filter (fun a => N - a ∈ A)).card :=
      Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hb⟩⟩
    omega
  · intro hlt
    have : 0 < (A.filter (fun a => N - a ∈ A)).card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp this
    exact ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩

/-- The fake set in the class 1 mod 6 never represents a multiple of 6. -/
theorem fake_one_mod_six_no_rep (N a b : ℕ) (hN : N % 6 = 0)
    (ha : a % 6 = 1) (hb : b % 6 = 1) : a + b ≠ N := by
  omega

/-- The fake map moves each point by at most 4: for p ≥ 5 prime-like input,
`6 * (p / 6) + 1` lies within 4 of `p` whenever `p % 6 ∈ {1, 5}`. -/
theorem fake_shift_le (p : ℕ) (hp : p % 6 = 1 ∨ p % 6 = 5) :
    (6 * (p / 6) + 1 : ℤ) ≤ p ∧ (p : ℤ) ≤ 6 * (p / 6) + 1 + 4 := by
  omega

/-- Lipschitz bound for a pairing deviation. -/
theorem pair_dev_lipschitz (a b a' b' N : ℤ) :
    |a' + b' - N| ≤ |a + b - N| + |a' - a| + |b' - b| := by
  have h1 := abs_add_le (a + b - N) ((a' - a) + (b' - b))
  have h2 := abs_add_le (a' - a) (b' - b)
  have e : a' + b' - N = (a + b - N) + ((a' - a) + (b' - b)) := by ring
  rw [e]; linarith

/-- Under dominance, every pair below N, the W_1 cost is linear. -/
theorem w1_linear_of_dominance {ι : Type*} (s : Finset ι) (a b : ι → ℤ) (N : ℤ)
    (h : ∀ i ∈ s, a i + b i < N) :
    ∑ i ∈ s, |a i + b i - N| = ∑ i ∈ s, (N - a i - b i) := by
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have := h i hi
  rw [abs_of_neg (by linarith)]; ring

/-- Vacuity test: the hypotheses hold, A = {3, 5, 7}, N = 10 has 3 + 7. -/
example : ∃ a ∈ ({3, 5, 7} : Finset ℕ), 10 - a ∈ ({3, 5, 7} : Finset ℕ) :=
  ⟨3, by decide, by decide⟩

example : (7 : ℕ) + 13 ≠ 18 := fake_one_mod_six_no_rep 18 7 13 rfl rfl rfl

end LeanLab.Routes.R5250
