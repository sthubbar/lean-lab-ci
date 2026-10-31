import LeanLab.ExceptionalSet.ChenPrimes
import LeanLab.ExceptionalSet.ChenClass2Barrier
import LeanLab.ExceptionalSet.ChenClass2Density
import LeanLab.Routes.R0011Ergodic

/-!
# T2 FRONTIER DISCOVER: binary Goldbach with ONE prime a Chen prime, by class mod 6

Unit U-1354, run 20261021T0503Z-11296. AI wrote this Lean code. Checked only by the Lean kernel.
Binary Goldbach is OPEN.

`EOne A c N` counts `m ≤ N`, `m ≡ c mod 6`, that are not `p + q` with `A p` and `q` prime.

* Class 4 mod 6, KNOWN. Grimmelt and Teräväinen, arXiv 2207.08805 Theorem 1.1, give
  `E(N,2,3) ≪ N^{1-δ}`, and arXiv 2508.16400 Theorem 1.1 gives two Chen primes, the lab's `GT11`.
  Either gives a power saving with one Chen prime, `oneChen_class4_of_GT11`, CONDITIONAL ON GT11.
* Class 0 mod 6, TARGET. One Chen prime `≡ 5 mod 6` plus a prime `≡ 1 mod 6` has no
  congruence obstruction, but no stated result was found: `TargetClass0`, a Prop, not proved.
* Class 2 mod 6, BARRIER, PROVED. A one-Chen representation with both primes above 3 forces
  `p = 3 r - 2`, `r` prime. So an `o(N)` exceptional set in this class gives Dickson pairs
  `r, 3 r - 2` with `r` arbitrarily large, `dickson_of_oneChen_class2_density`, open. This
  strengthens ExceptionalSet/ChenClass2Density.lean, where both primes were Chen.

Helpers PROVED: monotonicity under shrinking the prime set, one-restricted below two-restricted,
and the binary Goldbach count `E` below the sum of the three restricted class counts.
-/

open Finset Filter Topology

namespace LeanLab.ChenPrimeExceptional

open LeanLab.ExceptionalSet LeanLab.ExceptionalSet.ChenClass2Barrier

attribute [local instance] Classical.propDecidable

/-- exceptions in the class `c mod 6`, one prime from `A`, the other any prime -/
noncomputable def EOne (A : ℕ → Prop) (c N : ℕ) : ℕ :=
  #{m ∈ Icc 1 N | m % 6 = c ∧ ¬ ∃ p q, A p ∧ q.Prime ∧ p + q = m}

/-- exceptions in the class `c mod 6`, both primes from `A` -/
noncomputable def ETwo (A : ℕ → Prop) (c N : ℕ) : ℕ :=
  #{m ∈ Icc 1 N | m % 6 = c ∧ ¬ ∃ p q, A p ∧ A q ∧ p + q = m}

/-! ### Elementary helpers, PROVED -/

/-- **monotonicity**: a smaller restricted set has a larger exceptional set -/
theorem EOne_mono {A B : ℕ → Prop} (h : ∀ p, A p → B p) (c N : ℕ) :
    EOne B c N ≤ EOne A c N := by
  unfold EOne
  refine card_le_card ?_
  intro m hm
  simp only [mem_filter] at hm ⊢
  refine ⟨hm.1, hm.2.1, ?_⟩
  rintro ⟨p, q, hp, hq, hpq⟩
  exact hm.2.2 ⟨p, q, h p hp, hq, hpq⟩

theorem ETwo_mono {A B : ℕ → Prop} (h : ∀ p, A p → B p) (c N : ℕ) :
    ETwo B c N ≤ ETwo A c N := by
  unfold ETwo
  refine card_le_card ?_
  intro m hm
  simp only [mem_filter] at hm ⊢
  refine ⟨hm.1, hm.2.1, ?_⟩
  rintro ⟨p, q, hp, hq, hpq⟩
  exact hm.2.2 ⟨p, q, h p hp, h q hq, hpq⟩

/-- restricting one prime is weaker than restricting both -/
theorem EOne_le_ETwo {A : ℕ → Prop} (hA : ∀ p, A p → p.Prime) (c N : ℕ) :
    EOne A c N ≤ ETwo A c N := by
  unfold EOne ETwo
  refine card_le_card ?_
  intro m hm
  simp only [mem_filter] at hm ⊢
  refine ⟨hm.1, hm.2.1, ?_⟩
  rintro ⟨p, q, hp, hq, hpq⟩
  exact hm.2.2 ⟨p, q, hp, hA q hq, hpq⟩

/-- the lab's two-Chen count of P0039 is `ETwo IsChenPrime 4` -/
theorem ETwo_chen_four (N : ℕ) : ETwo IsChenPrime 4 N = EChen N := rfl

theorem chen_prime {p : ℕ} (hp : IsChenPrime p) : p.Prime := hp.1

/-- **inclusion into the counting framework**: binary Goldbach exceptions up to `N` are at most
the three restricted class counts, for any set of primes `A` -/
theorem E_le_classes {A : ℕ → Prop} (hA : ∀ p, A p → p.Prime) (N : ℕ) :
    E N ≤ EOne A 0 N + EOne A 2 N + EOne A 4 N := by
  have hsub : ((Icc 4 N).filter (fun n => Even n ∧ ¬ IsGoldbachSum n)) ⊆
      ({m ∈ Icc 1 N | m % 6 = 0 ∧ ¬ ∃ p q, A p ∧ q.Prime ∧ p + q = m} ∪
        {m ∈ Icc 1 N | m % 6 = 2 ∧ ¬ ∃ p q, A p ∧ q.Prime ∧ p + q = m}) ∪
        {m ∈ Icc 1 N | m % 6 = 4 ∧ ¬ ∃ p q, A p ∧ q.Prime ∧ p + q = m} := by
    intro m hm
    simp only [mem_filter, mem_Icc] at hm
    obtain ⟨⟨h4, hN⟩, he, hng⟩ := hm
    have hrep : ¬ ∃ p q, A p ∧ q.Prime ∧ p + q = m := by
      rintro ⟨p, q, hp, hq, hpq⟩
      exact hng ⟨p, q, hA p hp, hq, hpq⟩
    have hmod : m % 6 = 0 ∨ m % 6 = 2 ∨ m % 6 = 4 := by
      obtain ⟨k, hk⟩ := he; omega
    simp only [mem_union, mem_filter, mem_Icc]
    rcases hmod with h | h | h
    · exact Or.inl (Or.inl ⟨⟨by omega, hN⟩, h, hrep⟩)
    · exact Or.inl (Or.inr ⟨⟨by omega, hN⟩, h, hrep⟩)
    · exact Or.inr ⟨⟨by omega, hN⟩, h, hrep⟩
  unfold E EOne
  refine (card_le_card hsub).trans ?_
  refine (card_union_le _ _).trans ?_
  exact Nat.add_le_add_right (card_union_le _ _) _

/-! ### Class 4 mod 6: KNOWN, CONDITIONAL ON GT11 -/

/-- **one Chen prime, class 4 mod 6, power saving.** CONDITIONAL ON `GT11`, P0039
Grimmelt-Teräväinen 2025 Theorem 1.1; also implied by their arXiv 2207.08805 Theorem 1.1. -/
theorem oneChen_class4_of_GT11 (h : GT11) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      (EOne IsChenPrime 4 N : ℝ) ≤ C * (N : ℝ) ^ (1 - δ) := by
  obtain ⟨δ, hδ, C, hC⟩ := h
  refine ⟨δ, hδ, C, fun N hN => le_trans ?_ (hC N hN)⟩
  rw [← ETwo_chen_four]
  exact_mod_cast EOne_le_ETwo (fun p (hp : IsChenPrime p) => hp.1) 4 N

/-! ### Class 0 mod 6: TARGET, stated only -/

/-- TARGET, not proved and not found stated: one Chen prime, class 0 mod 6, power saving. -/
def TargetClass0 : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    (EOne IsChenPrime 0 N : ℝ) ≤ C * (N : ℝ) ^ (1 - δ)

/-- With the target, the one-Chen exceptions in the classes 0 and 4 together save a power.
CONDITIONAL ON GT11 and TargetClass0. -/
theorem oneChen_classes04 (h4 : GT11) (h0 : TargetClass0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ((EOne IsChenPrime 0 N + EOne IsChenPrime 4 N : ℕ) : ℝ) ≤ C * (N : ℝ) ^ (1 - δ) := by
  obtain ⟨δ₄, hδ₄, C₄, hC₄⟩ := oneChen_class4_of_GT11 h4
  obtain ⟨δ₀, hδ₀, C₀, hC₀⟩ := h0
  refine ⟨min δ₀ δ₄, lt_min hδ₀ hδ₄, |C₀| + |C₄|, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : ∀ δ, min δ₀ δ₄ ≤ δ → (N : ℝ) ^ (1 - δ) ≤ (N : ℝ) ^ (1 - min δ₀ δ₄) :=
    fun δ hδ => Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have a := hC₀ N hN
  have b := hC₄ N hN
  have p0 := hpow δ₀ (min_le_left _ _)
  have p4 := hpow δ₄ (min_le_right _ _)
  have hnn : 0 ≤ (N : ℝ) ^ (1 - min δ₀ δ₄) := Real.rpow_nonneg (by linarith) _
  have hnn0 : 0 ≤ (N : ℝ) ^ (1 - δ₀) := Real.rpow_nonneg (by linarith) _
  have hnn4 : 0 ≤ (N : ℝ) ^ (1 - δ₄) := Real.rpow_nonneg (by linarith) _
  have a' : C₀ * (N : ℝ) ^ (1 - δ₀) ≤ |C₀| * (N : ℝ) ^ (1 - min δ₀ δ₄) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hnn0).trans
      (mul_le_mul_of_nonneg_left p0 (abs_nonneg _))
  have b' : C₄ * (N : ℝ) ^ (1 - δ₄) ≤ |C₄| * (N : ℝ) ^ (1 - min δ₀ δ₄) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hnn4).trans
      (mul_le_mul_of_nonneg_left p4 (abs_nonneg _))
  push_cast
  nlinarith

/-! ### Class 2 mod 6: BARRIER, PROVED -/

/-- at most `π(N)` of the `m ∈ [1, N]` have `a ≤ m` and `m - a` prime -/
theorem card_sub_prime (a N : ℕ) :
    #{m ∈ Icc 1 N | a ≤ m ∧ (m - a).Prime} ≤ Nat.primeCounting N := by
  have hmap : ∀ m ∈ ({m ∈ Icc 1 N | a ≤ m ∧ (m - a).Prime} : Finset ℕ),
      (fun m => m - a) m ∈ Nat.primesBelow (N + 1) := by
    intro m hm
    simp only [mem_filter, mem_Icc] at hm
    rw [Nat.mem_primesBelow]
    exact ⟨show m - a < N + 1 by omega, hm.2.2⟩
  have hinj : Set.InjOn (fun m => m - a) ({m ∈ Icc 1 N | a ≤ m ∧ (m - a).Prime} : Finset ℕ) := by
    intro x hx y hy h
    simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at hx hy
    simp only at h
    omega
  calc _ ≤ (Nat.primesBelow (N + 1)).card := card_le_card_of_injOn _ hmap hinj
    _ = Nat.primeCounting N := Nat.primesBelow_card_eq_primeCounting' (N + 1)

/-- with every Dickson pair below `B`, a one-Chen representation of `m ≡ 2 mod 6` uses a prime
`a ≤ 3 B + 3` with `m - a` prime -/
theorem small_summand {B m : ℕ} (hB : ∀ r, DicksonPair r → r ≤ B) (h2 : m % 6 = 2)
    (hrep : ∃ p q, IsChenPrime p ∧ q.Prime ∧ p + q = m) :
    ∃ a, a < 3 * B + 4 ∧ a ≤ m ∧ (m - a).Prime := by
  obtain ⟨p, q, hp, hq, hpq⟩ := hrep
  by_cases hps : p < 3 * B + 4
  · exact ⟨p, hps, by omega, by rw [show m - p = q by omega]; exact hq⟩
  have hp3 : 3 < p := by omega
  have hq2 := hq.two_le
  by_cases hq3 : 3 < q
  · obtain ⟨r, hr, hpr⟩ := chen_pair_of_class2 hp hq hp3 hq3 (by omega)
    have := hB r hr
    omega
  · -- q is 2 or 3; q = 2 makes p even, so q = 3 and m - 3 = p is prime
    have hq23 : q = 2 ∨ q = 3 := by omega
    rcases hq23 with rfl | rfl
    · exfalso
      have := hp.1.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega))
      omega
    · exact ⟨3, by omega, by omega, by rw [show m - 3 = p by omega]; exact hp.1⟩

/-- the counting inequality for the class 2 mod 6 -/
theorem class2_le_one {B : ℕ} (hB : ∀ r, DicksonPair r → r ≤ B) (N : ℕ) :
    #{m ∈ Icc 1 N | m % 6 = 2} ≤
      EOne IsChenPrime 2 N + (3 * B + 4) * Nat.primeCounting N := by
  have hsub : ({m ∈ Icc 1 N | m % 6 = 2} : Finset ℕ) ⊆
      {m ∈ Icc 1 N | m % 6 = 2 ∧ ¬ ∃ p q, IsChenPrime p ∧ q.Prime ∧ p + q = m} ∪
      (range (3 * B + 4)).biUnion (fun a => {m ∈ Icc 1 N | a ≤ m ∧ (m - a).Prime}) := by
    intro m hm
    simp only [mem_filter] at hm
    by_cases hrep : ∃ p q, IsChenPrime p ∧ q.Prime ∧ p + q = m
    · apply mem_union_right
      obtain ⟨a, ha, ham, hpr⟩ := small_summand hB hm.2 hrep
      simp only [mem_biUnion, mem_range, mem_filter]
      exact ⟨a, ha, hm.1, ham, hpr⟩
    · exact mem_union_left _ (by simp only [mem_filter]; exact ⟨hm.1, hm.2, hrep⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  unfold EOne
  refine Nat.add_le_add_left ?_ _
  refine card_biUnion_le.trans ?_
  calc ∑ a ∈ range (3 * B + 4), #{m ∈ Icc 1 N | a ≤ m ∧ (m - a).Prime}
      ≤ ∑ _a ∈ range (3 * B + 4), Nat.primeCounting N :=
        sum_le_sum (fun a _ => card_sub_prime a N)
    _ = (3 * B + 4) * Nat.primeCounting N := by simp

/-- **the one-Chen density barrier.** If the `m ≤ N`, `m ≡ 2 mod 6`, that are not `p + q` with
`p` a Chen prime and `q` any prime are `o(N)`, there are Dickson pairs `(r, 3 r - 2)` with `r`
arbitrarily large. -/
theorem dickson_of_oneChen_class2_density
    (h : Tendsto (fun N : ℕ => (EOne IsChenPrime 2 N : ℝ) / N) atTop (𝓝 0)) :
    ∀ B, ∃ r, B < r ∧ DicksonPair r := by
  intro B
  by_contra hno
  push Not at hno
  have hB : ∀ r, DicksonPair r → r ≤ B := fun r hr => by
    by_contra h'; exact hno r (by omega) hr
  have hπ := (LeanLab.Routes.R0011.primes_density_zero).const_mul ((3 * B + 4 : ℕ) : ℝ)
  have hc : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hsum := (h.add hπ).add hc
  simp only [mul_zero, add_zero] at hsum
  have ev := hsum.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6))
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp ev
  set N := max N0 1
  have hN := hN0 N (le_max_left _ _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have key : N ≤ 6 * (EOne IsChenPrime 2 N + (3 * B + 4) * Nat.primeCounting N + 1) := by
    have a := ChenClass2Density.card_class2 N
    have b := class2_le_one hB N
    omega
  have key' : (N : ℝ) ≤ 6 * ((EOne IsChenPrime 2 N : ℝ) +
      ((3 * B + 4 : ℕ) : ℝ) * Nat.primeCounting N + 1) := by
    exact_mod_cast key
  have : (EOne IsChenPrime 2 N : ℝ) / N + ((3 * B + 4 : ℕ) : ℝ) * ((Nat.primeCounting N : ℝ) / N)
      + 1 / N = ((EOne IsChenPrime 2 N : ℝ) + ((3 * B + 4 : ℕ) : ℝ) * Nat.primeCounting N + 1) / N := by
    field_simp
  rw [this, div_lt_iff₀ hNpos] at hN
  linarith

/-- the earlier two-Chen barrier hypothesis implies the one-Chen hypothesis, so U-1073's
`dickson_of_class2_density` is a corollary of the theorem above -/
theorem oneChen_class2_of_twoChen
    (h : Tendsto (fun N : ℕ => (ChenClass2Density.EChen2 N : ℝ) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (EOne IsChenPrime 2 N : ℝ) / N) atTop (𝓝 0) := by
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) h
  have : EOne IsChenPrime 2 N ≤ ChenClass2Density.EChen2 N :=
    EOne_le_ETwo (fun p (hp : IsChenPrime p) => hp.1) 2 N
  exact div_le_div_of_nonneg_right (by exact_mod_cast this) (by positivity)

/-! ### Vacuity tests -/

/-- `3` and `5` are Chen primes, `5 = 5`, `7 = 7` -/
example : IsChenPrime 3 := ⟨by norm_num, by
  rw [LeanLab.AlmostPrimes.bigOmega_eq_cardFactors,
    ArithmeticFunction.cardFactors_apply_prime (by norm_num)]; norm_num⟩

/-- the hypothesis of `small_summand` is not empty: `8 = 3 + 5`, `8 ≡ 2 mod 6` -/
example : ∃ p q, IsChenPrime p ∧ q.Prime ∧ p + q = 8 := ⟨3, 5, ⟨by norm_num, by
  rw [LeanLab.AlmostPrimes.bigOmega_eq_cardFactors,
    ArithmeticFunction.cardFactors_apply_prime (by norm_num)]; norm_num⟩, by norm_num, rfl⟩

end LeanLab.ChenPrimeExceptional
