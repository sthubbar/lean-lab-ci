import LeanLab.ExceptionalSet.ChenClass2Barrier
import LeanLab.Routes.R0011Ergodic

/-!
# T2 FRONTIER: the density form of the class 2 mod 6 barrier for two Chen primes

Unit U-1073, PC run 20261019T1403Z-32628. AI wrote this Lean code. KNOWN mathematics in method.

P0039 proves a DENSITY statement in the class 4 mod 6: the exceptions are `O(N^{1-δ})`. The
cofinite barrier of ChenClass2Barrier.lean is therefore stronger in its hypothesis than the
paper's kind of result. This file proves the barrier in the paper's own form for the class
2 mod 6: if the number of `m ≤ N`, `m ≡ 2 mod 6`, that are not sums of two Chen primes is
`o(N)`, then there are infinitely many Dickson pairs `r`, `3 r - 2` both prime, an open
statement of twin prime type.

Proof: if every Dickson pair has `r ≤ B`, a representation `m = p + q` by Chen primes with
`m ≡ 2 mod 6` and `m > 6 B` must use `p = 3`, so `m - 3` is prime; at most `π(N)` such `m` lie
below `N`, `π(N) = o(N)` by `primes_density_zero`, while the class has about `N/6` members, so
the exceptions are at least about `N/6`.

Not progress on binary Goldbach, which is open.
-/

open Finset Filter Topology

namespace LeanLab.ExceptionalSet.ChenClass2Density

open LeanLab.ExceptionalSet LeanLab.ExceptionalSet.ChenClass2Barrier

attribute [local instance] Classical.propDecidable

/-- the class 2 mod 6 exceptional count for two Chen primes -/
noncomputable def EChen2 (N : ℕ) : ℕ :=
  #{m ∈ Icc 1 N | m % 6 = 2 ∧ ¬ ∃ p q, IsChenPrime p ∧ IsChenPrime q ∧ p + q = m}

/-- with all Dickson pairs below `B`, a Chen representation of `m ≡ 2 mod 6`, `m > 6 B + 6`,
has `m - 3` prime -/
theorem sub_three_prime {B m : ℕ} (hB : ∀ r, DicksonPair r → r ≤ B) (hm : 6 * B + 6 < m)
    (h2 : m % 6 = 2) (hrep : ∃ p q, IsChenPrime p ∧ IsChenPrime q ∧ p + q = m) :
    (m - 3).Prime := by
  obtain ⟨p, q, hp, hq, hpq⟩ := hrep
  have hp2 := hp.1.two_le
  have hq2 := hq.1.two_le
  -- p = 2 or q = 2 is impossible: the partner would be even and above 2
  have hpne2 : p ≠ 2 := by
    rintro rfl
    have := hq.1.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega)); omega
  have hqne2 : q ≠ 2 := by
    rintro rfl
    have := hp.1.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega)); omega
  by_cases hp3 : p = 3
  · subst hp3
    have : m - 3 = q := by omega
    rw [this]; exact hq.1
  by_cases hq3 : q = 3
  · subst hq3
    have : m - 3 = p := by omega
    rw [this]; exact hp.1
  exfalso
  have hp3' : 3 < p := by omega
  have hq3' : 3 < q := by omega
  obtain ⟨r, hr, hpr⟩ := chen_pair_of_class2 hp hq.1 hp3' hq3' (by omega)
  obtain ⟨s, hs, hqs⟩ := chen_pair_of_class2 hq hp.1 hq3' hp3' (by omega)
  have := hB r hr
  have := hB s hs
  omega

/-- the class `2 mod 6` in `[1, N]` has at least `N/6` members -/
theorem card_class2 (N : ℕ) : N / 6 ≤ #{m ∈ Icc 1 N | m % 6 = 2} := by
  have hsub : (range (N / 6)).image (fun k => 6 * k + 2) ⊆ {m ∈ Icc 1 N | m % 6 = 2} := by
    intro m hm
    simp only [mem_image, mem_range] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    have : 6 * (k + 1) ≤ 6 * (N / 6) := Nat.mul_le_mul_left 6 hk
    omega
  calc N / 6 = (range (N / 6)).card := (card_range _).symm
    _ = ((range (N / 6)).image (fun k => 6 * k + 2)).card :=
        (card_image_of_injective _ (fun x y h => by
          have : 6 * x + 2 = 6 * y + 2 := h
          omega)).symm
    _ ≤ _ := card_le_card hsub

/-- at most `π(N)` of the `m ∈ [1, N]` have `m - 3` prime -/
theorem card_sub_three_prime (N : ℕ) :
    #{m ∈ Icc 4 N | (m - 3).Prime} ≤ Nat.primeCounting N := by
  have hmap : ∀ m ∈ ({m ∈ Icc 4 N | (m - 3).Prime} : Finset ℕ),
      (fun m => m - 3) m ∈ Nat.primesBelow (N + 1) := by
    intro m hm
    simp only [mem_filter, mem_Icc] at hm
    rw [Nat.mem_primesBelow]
    exact ⟨show m - 3 < N + 1 by omega, hm.2⟩
  have hinj : Set.InjOn (fun m => m - 3) ({m ∈ Icc 4 N | (m - 3).Prime} : Finset ℕ) := by
    intro a ha b hb h
    simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at ha hb
    simp only at h
    omega
  calc _ ≤ (Nat.primesBelow (N + 1)).card := card_le_card_of_injOn _ hmap hinj
    _ = Nat.primeCounting N := Nat.primesBelow_card_eq_primeCounting' (N + 1)

/-- the counting inequality: class members are exceptions, small, or have `m - 3` prime -/
theorem class2_le {B : ℕ} (hB : ∀ r, DicksonPair r → r ≤ B) (N : ℕ) :
    #{m ∈ Icc 1 N | m % 6 = 2} ≤ EChen2 N + (6 * B + 6) + Nat.primeCounting N := by
  have hsub : ({m ∈ Icc 1 N | m % 6 = 2} : Finset ℕ) ⊆
      {m ∈ Icc 1 N | m % 6 = 2 ∧ ¬ ∃ p q, IsChenPrime p ∧ IsChenPrime q ∧ p + q = m} ∪
      (Icc 1 (6 * B + 6) ∪ {m ∈ Icc 4 N | (m - 3).Prime}) := by
    intro m hm
    simp only [mem_filter, mem_Icc] at hm
    by_cases hrep : ∃ p q, IsChenPrime p ∧ IsChenPrime q ∧ p + q = m
    · apply mem_union_right
      by_cases hsmall : m ≤ 6 * B + 6
      · exact mem_union_left _ (by simp only [mem_Icc]; omega)
      · apply mem_union_right
        simp only [mem_filter, mem_Icc]
        exact ⟨⟨by omega, hm.1.2⟩, sub_three_prime hB (by omega) hm.2 hrep⟩
    · exact mem_union_left _ (by simp only [mem_filter, mem_Icc]; exact ⟨hm.1, hm.2, hrep⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have h1 := card_union_le (Icc 1 (6 * B + 6)) ({m ∈ Icc 4 N | (m - 3).Prime} : Finset ℕ)
  have h2 := card_sub_three_prime N
  have h3 : (Icc 1 (6 * B + 6)).card = 6 * B + 6 := by simp
  unfold EChen2
  omega

/-- **the density barrier.** If the class 2 mod 6 exceptions for two Chen primes are `o(N)`,
there are Dickson pairs `(r, 3 r - 2)` with `r` arbitrarily large. -/
theorem dickson_of_class2_density
    (h : Tendsto (fun N : ℕ => (EChen2 N : ℝ) / N) atTop (𝓝 0)) :
    ∀ B, ∃ r, B < r ∧ DicksonPair r := by
  intro B
  by_contra hno
  push Not at hno
  have hB : ∀ r, DicksonPair r → r ≤ B := fun r hr => by
    by_contra h'; exact hno r (by omega) hr
  -- (EChen2 N + π N + 6B + 6)/N ≥ 1/6 - 1/N for every N ≥ 1, but the left side → 0
  have hπ := LeanLab.Routes.R0011.primes_density_zero
  have hc : Tendsto (fun N : ℕ => ((6 * B + 7 : ℕ) : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hsum := (h.add hπ).add hc
  simp only [add_zero] at hsum
  have ev := hsum.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6))
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp ev
  set N := max N0 1
  have hN := hN0 N (le_max_left _ _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have key : N ≤ 6 * (EChen2 N + Nat.primeCounting N + (6 * B + 7)) := by
    have a := card_class2 N
    have b := class2_le hB N
    omega
  have key' : (N : ℝ) ≤ 6 * ((EChen2 N : ℝ) + Nat.primeCounting N + ((6 * B + 7 : ℕ) : ℝ)) := by
    exact_mod_cast key
  have : (EChen2 N : ℝ) / N + (Nat.primeCounting N : ℝ) / N + ((6 * B + 7 : ℕ) : ℝ) / N =
      ((EChen2 N : ℝ) + Nat.primeCounting N + ((6 * B + 7 : ℕ) : ℝ)) / N := by
    field_simp
  rw [this, div_lt_iff₀ hNpos] at hN
  linarith

end LeanLab.ExceptionalSet.ChenClass2Density
