import LeanLab.Routes.U1568Frontier

/-!
# T2 FRONTIER: the shift step of I-0134 is a bounded gap problem for Goldbach numbers

Unit U-1571, architect run 20261027T0403Z-13216. AI wrote this Lean code, Claude, checked only
by the Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

Question, the Next line of I-0134. Shift a class `5 mod 6` integer `N` by the small Dickson
Chen primes `s = 3 r - 2`, namely `7, 13, 19, 31, 37`, and ask whether the Grimmelt-Teräväinen
method, P0039 arXiv 2508.16400 Theorem 1.1 p. 2, the lab's `GT11`, bounds the overlap of the
shifted exception sets `E₂(4) + s` well enough to make the class 5 ternary exceptions finite.

Answer in this file.
* `gaps_of_shiftCover`, PROVED: if a FIXED finite shift set `S` covers every large `N ≡ 5 mod 6`,
  then every interval `[x - max S, x + 5]` contains a sum of two Chen primes. Bounded gaps
  between Goldbach numbers are open: the best unconditional window is `x^{21/800}`, Pintz,
  arXiv 1206.0149 display 1.4, and `C log² x` under RH.
* `dickson_or_gaps`, PROVED: if all but finitely many `N ≡ 5 mod 6` are sums of three Chen
  primes, then either there are infinitely many Chen primes `≡ 1 mod 6`, that is infinitely many
  prime pairs `r, 3 r - 2` by `chen_one_mod_six`, or the sums of two primes have bounded gaps.
  Both alternatives are open problems. So finiteness in class 5 is out of reach today, while the
  power saving of I-0134 is not.
* `density_model`, PROVED: a set of the `GT11` shape with `δ = 1/2` can contain infinitely many
  full windows `M, M - 6, M - 12, M - 24, M - 30`. So the overlap of the shifted exception sets
  cannot be bounded below the trivial `min` bound from a density statement alone; the GT method
  outputs only a density statement.
-/

open Finset
open LeanLab.AlmostPrimes LeanLab.ExceptionalSet LeanLab.Routes.U1568

namespace LeanLab.Routes.U1571

attribute [local instance] Classical.propDecidable

/-- Plain math: `m = p + q` with `p, q` prime, a Goldbach number in the wide sense. -/
def IsTwoPrimeSum (m : ℕ) : Prop := ∃ p q, p.Prime ∧ q.Prime ∧ p + q = m

/-- Plain math: `m = p + q` with `p, q` Chen primes. -/
def IsChenPair (m : ℕ) : Prop := ∃ p q, IsChenPrime p ∧ IsChenPrime q ∧ p + q = m

/-- Plain math: every `N ≥ N₀`, `N ≡ 5 mod 6`, has `N - s` a sum of two Chen primes for some
`s ∈ S`, `s ≤ N`. With `S` the Dickson Chen primes this is the I-0134 shift step. -/
def ShiftCover (S : Finset ℕ) (N0 : ℕ) : Prop :=
  ∀ N, N0 ≤ N → N % 6 = 5 → ∃ s ∈ S, s ≤ N ∧ IsChenPair (N - s)

/-- Plain math: all but finitely many `N ≡ 5 mod 6` are sums of three Chen primes. -/
def ClassFiveTernary : Prop := ∃ N0, ∀ N, N0 ≤ N → N % 6 = 5 → IsChenTernary N

/-- Plain math: infinitely many Chen primes `≡ 1 mod 6`, equivalently infinitely many prime pairs
`r, 3 r - 2`. Open, a Dickson type prime pair statement. -/
def InfDickson : Prop := ∀ K, ∃ p, K < p ∧ IsChenPrime p ∧ p % 6 = 1

/-- Plain math: there is `B` with a sum of two primes in every `[x - B, x + 5]`, `x ≥ x₀`,
bounded gaps between Goldbach numbers. Open. -/
def BoundedTwoPrimeGaps : Prop :=
  ∃ B x0 : ℕ, ∀ x, x0 ≤ x → ∃ m, IsTwoPrimeSum m ∧ m ≤ x + 5 ∧ x ≤ m + B

/-- The next integer `≥ x` in the class `5 mod 6`. -/
lemma next_five (x : ℕ) : ∃ N, N % 6 = 5 ∧ x ≤ N ∧ N ≤ x + 5 :=
  ⟨x + (11 - x % 6) % 6, by omega, by omega, by omega⟩

/-- **A fixed shift set forces bounded gaps, PROVED.**
Plain math: if `ShiftCover S N₀`, then for all `x ≥ N₀` some sum of two Chen primes `m` has
`x - max S ≤ m ≤ x + 5`. -/
theorem gaps_of_shiftCover (S : Finset ℕ) (N0 : ℕ) (h : ShiftCover S N0) :
    ∀ x, N0 ≤ x → ∃ m, IsChenPair m ∧ m ≤ x + 5 ∧ x ≤ m + S.sup id := by
  intro x hx
  obtain ⟨N, hN5, hxN, hNx⟩ := next_five x
  obtain ⟨s, hs, hsN, hp⟩ := h N (by omega) hN5
  have hsup : s ≤ S.sup id := Finset.le_sup (f := id) hs
  exact ⟨N - s, hp, by omega, by omega⟩

/-- A sum of two Chen primes is a sum of two primes. -/
lemma twoPrime_of_chenPair {m : ℕ} (h : IsChenPair m) : IsTwoPrimeSum m := by
  obtain ⟨p, q, hp, hq, hpq⟩ := h
  exact ⟨p, q, hp.1, hq.1, hpq⟩

/-- **A shift cover by Chen primes gives the ternary statement, PROVED.**
Plain math: if every `s ∈ S` is a Chen prime and `ShiftCover S N₀`, every `N ≥ N₀`,
`N ≡ 5 mod 6`, is a sum of three Chen primes. -/
theorem ternary_of_shiftCover (S : Finset ℕ) (N0 : ℕ) (hS : ∀ s ∈ S, IsChenPrime s)
    (h : ShiftCover S N0) : ∀ N, N0 ≤ N → N % 6 = 5 → IsChenTernary N := by
  intro N hN h5
  obtain ⟨s, hs, hsN, p, q, hp, hq, hpq⟩ := h N hN h5
  exact ⟨s, p, q, hS s hs, hp, hq, by omega⟩

/-- One summand of a class 5 Chen ternary sum is small once the Dickson primes are bounded. -/
lemma bounded_summand {K N : ℕ} (hK : ∀ p, IsChenPrime p → p % 6 = 1 → p ≤ K)
    (hN : N % 6 = 5) (hT : IsChenTernary N) :
    ∃ a, a ≤ K + 3 ∧ a ≤ N ∧ IsTwoPrimeSum (N - a) := by
  obtain ⟨p, q, r, hp, hq, hr, hsum⟩ := hT
  have key : ∀ x, IsChenPrime x → x ≤ K + 3 ∨ x % 6 = 5 := by
    intro x hx
    by_cases h3 : 3 < x
    · rcases prime_mod_six hx.1 h3 with h | h
      · left; have := hK x hx h; omega
      · right; exact h
    · left; omega
  rcases key p hp with h1 | h1
  · exact ⟨p, h1, by omega, q, r, hq.1, hr.1, by omega⟩
  rcases key q hq with h2 | h2
  · exact ⟨q, h2, by omega, p, r, hp.1, hr.1, by omega⟩
  rcases key r hr with h3 | h3
  · exact ⟨r, h3, by omega, p, q, hp.1, hq.1, by omega⟩
  omega

/-- **Barrier for class 5, PROVED unconditional.**
Plain math: if all but finitely many `N ≡ 5 mod 6` are sums of three Chen primes, then there are
infinitely many prime pairs `r, 3 r - 2`, or there is `B` such that every `[x - B, x + 5]`,
`x` large, contains a sum of two primes. Both alternatives are open. -/
theorem dickson_or_gaps (h : ClassFiveTernary) : InfDickson ∨ BoundedTwoPrimeGaps := by
  by_cases hD : InfDickson
  · exact Or.inl hD
  right
  have hK : ∃ K, ∀ p, IsChenPrime p → p % 6 = 1 → p ≤ K := by
    by_contra hc
    apply hD
    intro K
    by_contra hK
    apply hc
    refine ⟨K, fun p hp h1 => ?_⟩
    by_contra hpK
    exact hK ⟨p, by omega, hp, h1⟩
  obtain ⟨K, hK⟩ := hK
  obtain ⟨N0, hN0⟩ := h
  refine ⟨K + 3, N0, fun x hx => ?_⟩
  obtain ⟨N, hN5, hxN, hNx⟩ := next_five x
  obtain ⟨a, ha, haN, hs⟩ := bounded_summand hK hN5 (hN0 N (by omega) hN5)
  exact ⟨N - a, hs, by omega, by omega⟩

/-! ## The five Dickson Chen primes of the I-0134 Next line -/

lemma chen_of_three_mul {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (h : p + 2 = 3 * r) :
    IsChenPrime p := by
  refine ⟨hp, ?_⟩
  rw [bigOmega_eq_cardFactors, h, ArithmeticFunction.cardFactors_mul (by norm_num) hr.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime Nat.prime_three,
    ArithmeticFunction.cardFactors_apply_prime hr]

/-- `S₀ = {7, 13, 19, 31, 37}`, the Dickson Chen primes `3 r - 2` with `r = 3, 5, 7, 11, 13`. -/
def S0 : Finset ℕ := {7, 13, 19, 31, 37}

theorem S0_dickson : ∀ s ∈ S0, IsChenPrime s ∧ s % 6 = 1 := by
  intro s hs
  simp only [S0, mem_insert, mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact ⟨chen_of_three_mul (by norm_num) Nat.prime_three (by norm_num), by norm_num⟩
  · exact ⟨chen_of_three_mul (by norm_num) (by norm_num : (5:ℕ).Prime) (by norm_num), by norm_num⟩
  · exact ⟨chen_of_three_mul (by norm_num) (by norm_num : (7:ℕ).Prime) (by norm_num), by norm_num⟩
  · exact ⟨chen_of_three_mul (by norm_num) (by norm_num : (11:ℕ).Prime) (by norm_num), by norm_num⟩
  · exact ⟨chen_of_three_mul (by norm_num) (by norm_num : (13:ℕ).Prime) (by norm_num), by norm_num⟩

lemma S0_sup : S0.sup id = 37 := by decide

/-- **The I-0134 shift step, specialised, PROVED.**
Plain math: if the shifts `7, 13, 19, 31, 37` cover every large `N ≡ 5 mod 6`, then every large
`N ≡ 5 mod 6` is a sum of three Chen primes and every `[x - 37, x + 5]` contains a sum of two
Chen primes, hence of two primes. -/
theorem S0_cover_consequences (N0 : ℕ) (h : ShiftCover S0 N0) :
    (∀ N, N0 ≤ N → N % 6 = 5 → IsChenTernary N) ∧
    ∀ x, N0 ≤ x → ∃ m, IsTwoPrimeSum m ∧ m ≤ x + 5 ∧ x ≤ m + 37 := by
  refine ⟨ternary_of_shiftCover S0 N0 (fun s hs => (S0_dickson s hs).1) h, fun x hx => ?_⟩
  obtain ⟨m, hm, h1, h2⟩ := gaps_of_shiftCover S0 N0 h x hx
  rw [S0_sup] at h2
  exact ⟨m, twoPrime_of_chenPair hm, h1, h2⟩

/-! ## Density alone cannot bound the overlap -/

/-- Model exception set: `m ≡ 4 mod 6` within `34` above some `36 k²`. -/
def ModelE (m : ℕ) : Prop := m % 6 = 4 ∧ ∃ k, 36 * k ^ 2 ≤ m ∧ m ≤ 36 * k ^ 2 + 34

lemma model_count_nat (X : ℕ) : #{m ∈ Icc 1 X | ModelE m} ≤ 35 * (Nat.sqrt X + 1) := by
  classical
  have hsub : {m ∈ Icc 1 X | ModelE m} ⊆
      ((range (Nat.sqrt X + 1)) ×ˢ (range 35)).image (fun kj => 36 * kj.1 ^ 2 + kj.2) := by
    intro m hm
    obtain ⟨hmI, _, k, hk1, hk2⟩ := Finset.mem_filter.1 hm
    have hmX : m ≤ X := (Finset.mem_Icc.1 hmI).2
    simp only [mem_image, mem_product, mem_range, Prod.exists]
    refine ⟨k, m - 36 * k ^ 2, ⟨?_, by omega⟩, by omega⟩
    have : k * k ≤ X := by nlinarith
    exact Nat.lt_succ_of_le (Nat.le_sqrt.2 this)
  calc #{m ∈ Icc 1 X | ModelE m} ≤ _ := card_le_card hsub
    _ ≤ _ := card_image_le
    _ = 35 * (Nat.sqrt X + 1) := by rw [card_product, card_range, card_range]; ring

/-- **Density model, PROVED.**
Plain math: there is a set `E` of `m ≡ 4 mod 6` with `#(E ∩ [1, X]) ≤ 70 X^{1/2}` for all
`X ≥ 1`, the `GT11` shape with `δ = 1/2`, that contains `M, M - 6, M - 12, M - 24, M - 30` for
infinitely many `M`. So `GT11` alone, at any `δ ≤ 1/2`, does not make the overlap of the shifts
by `7, 13, 19, 31, 37` finite. -/
theorem density_model : ∃ E : ℕ → Prop,
    (∀ m, E m → m % 6 = 4) ∧
    (∀ X : ℕ, 1 ≤ X → ((#{m ∈ Icc 1 X | E m} : ℕ) : ℝ) ≤ 70 * (X : ℝ) ^ ((1 : ℝ) / 2)) ∧
    ∀ K, ∃ M, K ≤ M ∧ M % 6 = 4 ∧ ∀ t ∈ ({0, 6, 12, 24, 30} : Finset ℕ), t ≤ M ∧ E (M - t) := by
  refine ⟨ModelE, fun m hm => hm.1, fun X hX => ?_, fun K => ?_⟩
  · have h1 := model_count_nat X
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hs : ((Nat.sqrt X : ℕ) : ℝ) ≤ Real.sqrt X := Real.nat_sqrt_le_real_sqrt
    have hs1 : (1 : ℝ) ≤ Real.sqrt X := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hX1
    rw [← Real.sqrt_eq_rpow]
    have : ((#{m ∈ Icc 1 X | ModelE m} : ℕ) : ℝ) ≤ 35 * ((Nat.sqrt X : ℝ) + 1) := by
      exact_mod_cast h1
    linarith
  · refine ⟨36 * (K + 1) ^ 2 + 34, by nlinarith, by omega, fun t ht => ?_⟩
    simp only [mem_insert, mem_singleton] at ht
    generalize hy : (K + 1) ^ 2 = y
    have key : ∀ t, t ≤ 34 → t % 6 = 0 → t ≤ 36 * y + 34 ∧ ModelE (36 * y + 34 - t) := by
      intro t ht34 ht6
      exact ⟨by omega, by omega, K + 1, by rw [hy]; omega, by rw [hy]; omega⟩
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> exact key _ (by norm_num) (by norm_num)

/-! ## Vacuity instances -/

/-- Vacuity for `ShiftCover S0`: at `N = 41`, `41 - 7 = 34 = 3 + 31` with `3, 31` Chen primes. -/
theorem shiftCover_vacuity : ∃ s ∈ S0, s ≤ 41 ∧ IsChenPair (41 - s) :=
  ⟨7, by simp [S0], by norm_num, 3, 31, chen_three, (S0_dickson 31 (by simp [S0])).1, by norm_num⟩

/-- Vacuity for `InfDickson` and `ClassFiveTernary`: the predicates in them are not empty,
`37` is a Chen prime `≡ 1 mod 6` and `17 = 7 + 5 + 5` is a class 5 Chen ternary sum. -/
theorem barrier_vacuity : (∃ p, 13 < p ∧ IsChenPrime p ∧ p % 6 = 1) ∧ IsChenTernary 17 ∧
    17 % 6 = 5 :=
  ⟨⟨37, by norm_num, S0_dickson 37 (by simp [S0])⟩, ternary_vacuity.2, by norm_num⟩

/-- Vacuity for `BoundedTwoPrimeGaps`' body at one point: `x = 10`, `m = 10 = 3 + 7`. -/
theorem gaps_vacuity : ∃ m, IsTwoPrimeSum m ∧ m ≤ 10 + 5 ∧ 10 ≤ m + 0 :=
  ⟨10, ⟨3, 7, Nat.prime_three, by norm_num, rfl⟩, by norm_num, by norm_num⟩

end LeanLab.Routes.U1571

#print axioms LeanLab.Routes.U1571.next_five
#print axioms LeanLab.Routes.U1571.gaps_of_shiftCover
#print axioms LeanLab.Routes.U1571.twoPrime_of_chenPair
#print axioms LeanLab.Routes.U1571.ternary_of_shiftCover
#print axioms LeanLab.Routes.U1571.bounded_summand
#print axioms LeanLab.Routes.U1571.dickson_or_gaps
#print axioms LeanLab.Routes.U1571.chen_of_three_mul
#print axioms LeanLab.Routes.U1571.S0_dickson
#print axioms LeanLab.Routes.U1571.S0_sup
#print axioms LeanLab.Routes.U1571.S0_cover_consequences
#print axioms LeanLab.Routes.U1571.model_count_nat
#print axioms LeanLab.Routes.U1571.density_model
#print axioms LeanLab.Routes.U1571.shiftCover_vacuity
#print axioms LeanLab.Routes.U1571.barrier_vacuity
#print axioms LeanLab.Routes.U1571.gaps_vacuity
