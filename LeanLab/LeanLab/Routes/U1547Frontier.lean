import LeanLab.ExceptionalSet.ChenClass2Density

/-!
# T2 FRONTIER: Goldbach with ONE Chen prime, the class map mod 6

Unit U-1547, PC run 20261026T0808Z-17522. AI wrote this Lean code, Claude, checked only by the
Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

Question. P0039 Grimmelt-Teräväinen 2025, Theorem 1.1 on p. 2, gives a power saving exceptional
set for `m = p + q` with BOTH `p, q` Chen primes, only for `m ≡ 4 mod 6`. The lab's
ChenClass2Barrier and ChenClass2Density show the classes `0` and `2 mod 6` are blocked for two
Chen primes by a Dickson pair statement `r, 3 r - 2` both prime. What happens with ONE Chen prime,
`m = p + q`, `p` a Chen prime and `q` any prime?

Answer in this file.
* Class `2 mod 6` stays blocked: `dickson_of_mix_class2_density`, PROVED with no hypothesis
  beyond the density assumption itself: if the class `2 mod 6` exceptions for one Chen prime are
  `o(N)`, there are infinitely many Dickson pairs. This strengthens the lab's
  `dickson_of_class2_density`, since `EMix 2 N ≤ EChen2 N`, proved as `emix2_le_echen2`.
  Reason: with `p, q > 3` and `p + q ≡ 2 mod 6` both are `1 mod 6`, and a Chen prime `1 mod 6`
  is `3 r - 2` with `r` prime.
* Class `4 mod 6` follows from Theorem 1.1: `mix4_of_GT`, CONDITIONAL ON the lab's `GT11`.
* Class `0 mod 6` is NOT blocked: a representation `p ≡ 5`, `q ≡ 1 mod 6` uses an ordinary
  Chen prime. `MixClass0Target` is the frontier statement, a power saving for one Chen prime in
  the class `0 mod 6`; `mix04_of` assembles classes `0` and `4` from it and `GT11`.
So with one Chen prime the barrier class is exactly `2 mod 6`, against `0` and `2` for two.

Numerics, Routes/numerics/U1547/mixed_chen.py to `N = 2·10^7`: no exception in any even class
from `6` on for one Chen prime; in class `2 mod 6` every representation counted has
`p = 3 r - 2`, share 1.000, against about 0.18 in class `0` and 0 in class `4`; two Chen primes
have 27 exceptions in class `2`, the largest 35912.
-/

open Finset Filter Topology

namespace LeanLab.Routes.U1547

open LeanLab.ExceptionalSet LeanLab.ExceptionalSet.ChenClass2Barrier
  LeanLab.ExceptionalSet.ChenClass2Density

attribute [local instance] Classical.propDecidable

/-- `m = p + q` with `p` a Chen prime and `q` any prime -/
def IsChenMixSum (m : ℕ) : Prop := ∃ p q, IsChenPrime p ∧ q.Prime ∧ p + q = m

/-- the number of `m ∈ [1, N]`, `m ≡ c mod 6`, that are not a Chen prime plus a prime -/
noncomputable def EMix (c N : ℕ) : ℕ := #{m ∈ Icc 1 N | m % 6 = c ∧ ¬ IsChenMixSum m}

/-- a power saving bound `E N ≤ C N^{1-δ}` for all `N ≥ 1`, some `δ > 0` -/
def PowerSaving (E : ℕ → ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → (E N : ℝ) ≤ C * (N : ℝ) ^ (1 - δ)

/-- the frontier statement: a power saving for one Chen prime in the class `0 mod 6`. -/
def MixClass0Target : Prop := PowerSaving (EMix 0)

/-- vacuity of `PowerSaving`: the zero count satisfies it -/
theorem powerSaving_zero : PowerSaving (fun _ => 0) :=
  ⟨1 / 2, by norm_num, 0, fun N _ => by simp⟩

/-- a sum of two Chen primes is a Chen prime plus a prime -/
theorem mix_of_two_chen {m : ℕ} (h : ∃ p q, IsChenPrime p ∧ IsChenPrime q ∧ p + q = m) :
    IsChenMixSum m := by
  obtain ⟨p, q, hp, hq, h⟩ := h
  exact ⟨p, q, hp, hq.1, h⟩

/-- one Chen prime has at most as many class `2 mod 6` exceptions as two -/
theorem emix2_le_echen2 (N : ℕ) : EMix 2 N ≤ EChen2 N := by
  unfold EMix EChen2
  refine card_le_card (fun m hm => ?_)
  simp only [mem_filter] at hm ⊢
  exact ⟨hm.1, hm.2.1, fun h => hm.2.2 (mix_of_two_chen h)⟩

/-- one Chen prime has at most as many class `4 mod 6` exceptions as two -/
theorem emix4_le_echen (N : ℕ) : EMix 4 N ≤ EChen N := by
  unfold EMix EChen
  refine card_le_card (fun m hm => ?_)
  simp only [mem_filter] at hm ⊢
  exact ⟨hm.1, hm.2.1, fun h => hm.2.2 (mix_of_two_chen h)⟩

/-- **class 4 mod 6**, CONDITIONAL ON `GT11`, the lab's form of P0039 Theorem 1.1, p. 2 -/
theorem mix4_of_GT (hGT : GT11) : PowerSaving (EMix 4) := by
  obtain ⟨δ, hδ, C, hC⟩ := hGT
  exact ⟨δ, hδ, C, fun N hN => le_trans (by exact_mod_cast emix4_le_echen N) (hC N hN)⟩

/-- the sum of two power saving counts is power saving -/
theorem powerSaving_add {E F : ℕ → ℕ} (hE : PowerSaving E) (hF : PowerSaving F) :
    PowerSaving (fun N => E N + F N) := by
  obtain ⟨δ₁, h₁, C₁, hC₁⟩ := hE
  obtain ⟨δ₂, h₂, C₂, hC₂⟩ := hF
  refine ⟨min δ₁ δ₂, lt_min h₁ h₂, |C₁| + |C₂|, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmono : ∀ δ, min δ₁ δ₂ ≤ δ → (N : ℝ) ^ (1 - δ) ≤ (N : ℝ) ^ (1 - min δ₁ δ₂) :=
    fun δ hδ => Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hpos : 0 ≤ (N : ℝ) ^ (1 - min δ₁ δ₂) := Real.rpow_nonneg (by linarith) _
  have e1 : (E N : ℝ) ≤ |C₁| * (N : ℝ) ^ (1 - min δ₁ δ₂) := by
    have := hC₁ N hN
    have hp1 : 0 ≤ (N : ℝ) ^ (1 - δ₁) := Real.rpow_nonneg (by linarith) _
    calc (E N : ℝ) ≤ C₁ * (N : ℝ) ^ (1 - δ₁) := this
      _ ≤ |C₁| * (N : ℝ) ^ (1 - δ₁) := mul_le_mul_of_nonneg_right (le_abs_self _) hp1
      _ ≤ |C₁| * (N : ℝ) ^ (1 - min δ₁ δ₂) :=
          mul_le_mul_of_nonneg_left (hmono δ₁ (min_le_left _ _)) (abs_nonneg _)
  have e2 : (F N : ℝ) ≤ |C₂| * (N : ℝ) ^ (1 - min δ₁ δ₂) := by
    have := hC₂ N hN
    have hp2 : 0 ≤ (N : ℝ) ^ (1 - δ₂) := Real.rpow_nonneg (by linarith) _
    calc (F N : ℝ) ≤ C₂ * (N : ℝ) ^ (1 - δ₂) := this
      _ ≤ |C₂| * (N : ℝ) ^ (1 - δ₂) := mul_le_mul_of_nonneg_right (le_abs_self _) hp2
      _ ≤ |C₂| * (N : ℝ) ^ (1 - min δ₁ δ₂) :=
          mul_le_mul_of_nonneg_left (hmono δ₂ (min_le_right _ _)) (abs_nonneg _)
  push_cast
  linarith

/-- **ASSEMBLY, classes 0 and 4 mod 6.** CONDITIONAL ON `GT11` and on the frontier statement
`MixClass0Target`: the `m ≤ N` in the classes `0` and `4 mod 6` that are not a Chen prime plus a
prime number `O(N^{1-δ})`. -/
theorem mix04_of (hGT : GT11) (hC0 : MixClass0Target) :
    PowerSaving (fun N => EMix 0 N + EMix 4 N) :=
  powerSaving_add hC0 (mix4_of_GT hGT)

/-- at most `π(N)` of the `m ∈ [1, N]` have `m - a` prime with `a < m` -/
theorem card_shift_prime (a N : ℕ) :
    #{m ∈ Icc 1 N | a < m ∧ (m - a).Prime} ≤ Nat.primeCounting N := by
  have hmap : ∀ m ∈ ({m ∈ Icc 1 N | a < m ∧ (m - a).Prime} : Finset ℕ),
      (fun m => m - a) m ∈ Nat.primesBelow (N + 1) := by
    intro m hm
    simp only [mem_filter, mem_Icc] at hm
    rw [Nat.mem_primesBelow]
    exact ⟨show m - a < N + 1 by omega, hm.2.2⟩
  have hinj : Set.InjOn (fun m => m - a) ({m ∈ Icc 1 N | a < m ∧ (m - a).Prime} : Finset ℕ) := by
    intro x hx y hy h
    simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at hx hy
    simp only at h
    omega
  calc _ ≤ (Nat.primesBelow (N + 1)).card := card_le_card_of_injOn _ hmap hinj
    _ = Nat.primeCounting N := Nat.primesBelow_card_eq_primeCounting' (N + 1)

/-- at most `A π(N)` of the `m ∈ [1, N]` have `m - a` prime for some `a ∈ [1, A]` -/
theorem card_some_shift_prime (A N : ℕ) :
    #{m ∈ Icc 1 N | ∃ a ∈ Icc 1 A, a < m ∧ (m - a).Prime} ≤ A * Nat.primeCounting N := by
  have hsub : ({m ∈ Icc 1 N | ∃ a ∈ Icc 1 A, a < m ∧ (m - a).Prime} : Finset ℕ) ⊆
      (Icc 1 A).biUnion (fun a => ({m ∈ Icc 1 N | a < m ∧ (m - a).Prime} : Finset ℕ)) := by
    intro m hm
    simp only [mem_filter] at hm
    obtain ⟨a, ha, h⟩ := hm.2
    exact mem_biUnion.2 ⟨a, ha, mem_filter.2 ⟨hm.1, h⟩⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ a ∈ Icc 1 A, #{m ∈ Icc 1 N | a < m ∧ (m - a).Prime} := card_biUnion_le
    _ ≤ ∑ _a ∈ Icc 1 A, Nat.primeCounting N := sum_le_sum (fun a _ => card_shift_prime a N)
    _ = A * Nat.primeCounting N := by simp

/-- **the class 2 split.** A representation of `m ≡ 2 mod 6` as a Chen prime plus a prime has
`m - a` prime for some `a ≤ 3 B + 3`, or uses a Dickson pair `r > B` through `p = 3 r - 2`. -/
theorem mix_class2_split (B : ℕ) {m : ℕ} (h2 : m % 6 = 2) (hrep : IsChenMixSum m) :
    (∃ a ∈ Icc 1 (3 * B + 3), a < m ∧ (m - a).Prime) ∨
    ∃ r, B < r ∧ DicksonPair r ∧ 3 * r - 2 < m ∧ (m - (3 * r - 2)).Prime := by
  obtain ⟨p, q, hp, hq, hpq⟩ := hrep
  have hp2 := hp.1.two_le
  have hq2 := hq.two_le
  have hpne2 : p ≠ 2 := by
    rintro rfl
    have := hq.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega)); omega
  have hqne2 : q ≠ 2 := by
    rintro rfl
    have := hp.1.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega)); omega
  by_cases hp3 : p = 3
  · subst hp3
    left
    exact ⟨3, mem_Icc.2 ⟨by norm_num, by omega⟩, by omega,
      by rw [show m - 3 = q by omega]; exact hq⟩
  by_cases hq3 : q = 3
  · subst hq3
    left
    exact ⟨3, mem_Icc.2 ⟨by norm_num, by omega⟩, by omega,
      by rw [show m - 3 = p by omega]; exact hp.1⟩
  obtain ⟨r, hr, hpr⟩ := chen_pair_of_class2 hp hq (by omega) (by omega) (by omega)
  by_cases hrB : r ≤ B
  · left
    exact ⟨p, mem_Icc.2 ⟨by omega, by omega⟩, by omega,
      by rw [show m - p = q by omega]; exact hq⟩
  · right
    exact ⟨r, by omega, hr, by omega, by rw [show m - (3 * r - 2) = q by omega]; exact hq⟩

/-- **the counting inequality, unconditional.** For every `B` and `N`, the class `2 mod 6` in
`[1, N]` has at most `EMix 2 N + (3 B + 3) π(N)` members, plus those using a Dickson pair above
`B`. -/
theorem class2_mix_le (B N : ℕ) :
    #{m ∈ Icc 1 N | m % 6 = 2} ≤ EMix 2 N + (3 * B + 3) * Nat.primeCounting N +
      #{m ∈ Icc 1 N | ∃ r, B < r ∧ DicksonPair r ∧ 3 * r - 2 < m ∧ (m - (3 * r - 2)).Prime} := by
  have hsub : ({m ∈ Icc 1 N | m % 6 = 2} : Finset ℕ) ⊆
      ({m ∈ Icc 1 N | m % 6 = 2 ∧ ¬ IsChenMixSum m} ∪
        {m ∈ Icc 1 N | ∃ a ∈ Icc 1 (3 * B + 3), a < m ∧ (m - a).Prime}) ∪
      {m ∈ Icc 1 N | ∃ r, B < r ∧ DicksonPair r ∧ 3 * r - 2 < m ∧ (m - (3 * r - 2)).Prime} := by
    intro m hm
    simp only [mem_filter] at hm
    by_cases hrep : IsChenMixSum m
    · rcases mix_class2_split B hm.2 hrep with h | h
      · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hm.1, h⟩))
      · exact mem_union_right _ (mem_filter.2 ⟨hm.1, h⟩)
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hm.1, hm.2, hrep⟩))
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have h1 := card_union_le ({m ∈ Icc 1 N | m % 6 = 2 ∧ ¬ IsChenMixSum m} : Finset ℕ)
    {m ∈ Icc 1 N | ∃ a ∈ Icc 1 (3 * B + 3), a < m ∧ (m - a).Prime}
  have h2 := card_some_shift_prime (3 * B + 3) N
  unfold EMix
  omega

/-- **the class 2 mod 6 barrier for ONE Chen prime.** If the `m ≤ N`, `m ≡ 2 mod 6`, that are not
a Chen prime plus a prime number `o(N)`, there are Dickson pairs `(r, 3 r - 2)` with `r`
arbitrarily large. Strengthens `dickson_of_class2_density` through `emix2_le_echen2`. -/
theorem dickson_of_mix_class2_density
    (h : Tendsto (fun N : ℕ => (EMix 2 N : ℝ) / N) atTop (𝓝 0)) :
    ∀ B, ∃ r, B < r ∧ DicksonPair r := by
  intro B
  by_contra hno
  push Not at hno
  have hempty : ∀ N : ℕ, #{m ∈ Icc 1 N | ∃ r, B < r ∧ DicksonPair r ∧ 3 * r - 2 < m ∧
      (m - (3 * r - 2)).Prime} = 0 := by
    intro N
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro m - ⟨r, hr, hd, -⟩
    exact absurd hd (hno r hr)
  have hπ := LeanLab.Routes.R0011.primes_density_zero
  have hπ' : Tendsto (fun N : ℕ => ((3 * B + 3 : ℕ) : ℝ) * ((Nat.primeCounting N : ℝ) / N))
      atTop (𝓝 0) := by
    simpa using hπ.const_mul ((3 * B + 3 : ℕ) : ℝ)
  have hc : Tendsto (fun N : ℕ => ((6 : ℕ) : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hsum := (h.add hπ').add hc
  simp only [add_zero] at hsum
  have ev := hsum.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6))
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp ev
  set N := max N0 1
  have hN := hN0 N (le_max_left _ _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have key : N ≤ 6 * (EMix 2 N + (3 * B + 3) * Nat.primeCounting N + 6) := by
    have a := card_class2 N
    have b := class2_mix_le B N
    rw [hempty N] at b
    omega
  have key' : (N : ℝ) ≤ 6 * ((EMix 2 N : ℝ) + ((3 * B + 3 : ℕ) : ℝ) * Nat.primeCounting N +
      ((6 : ℕ) : ℝ)) := by
    exact_mod_cast key
  have : (EMix 2 N : ℝ) / N + ((3 * B + 3 : ℕ) : ℝ) * ((Nat.primeCounting N : ℝ) / N) +
      ((6 : ℕ) : ℝ) / N = ((EMix 2 N : ℝ) + ((3 * B + 3 : ℕ) : ℝ) * Nat.primeCounting N +
      ((6 : ℕ) : ℝ)) / N := by
    field_simp
  rw [this, div_lt_iff₀ hNpos] at hN
  push_cast at hN key'
  nlinarith

/-- vacuity instances: `12 = 5 + 7` in class `0`, `20 = 7 + 13` in class `2` with `p = 7 =
3 · 3 - 2`, `10 = 5 + 5` in class `4`; each is a Chen prime plus a prime. -/
theorem vacuity_mix : IsChenMixSum 12 ∧ IsChenMixSum 20 ∧ IsChenMixSum 10 := by
  have h5 : IsChenPrime 5 := by
    refine ⟨by norm_num, ?_⟩
    rw [LeanLab.AlmostPrimes.bigOmega_eq_cardFactors,
      ArithmeticFunction.cardFactors_apply_prime (by norm_num : Nat.Prime (5 + 2))]
    norm_num
  obtain ⟨h7, -, -, -⟩ := vacuity_20
  exact ⟨⟨5, 7, h5, by norm_num, rfl⟩, ⟨7, 13, h7, by norm_num, rfl⟩,
    ⟨5, 5, h5, by norm_num, rfl⟩⟩

/-- LEAF. Unit U-1547. Every `m ≡ 0 mod 6` with `6 ≤ m ≤ 10000` is a Chen prime plus a prime,
`m = p + q`, `p` prime with `p + 2` having at most two prime factors with multiplicity, `q` prime.
Finite check; Routes/numerics/U1547/mixed_chen.py finds no exception in class 0 below `2·10^7`. -/
theorem mix_class0_upto : ∀ m, 6 ≤ m → m ≤ 10000 → m % 6 = 0 → IsChenMixSum m := by
  intro m hm hm' hmod
  have hm_range : m ∈ Finset.Icc 6 10000 := Finset.mem_Icc.mpr ⟨hm, hm'⟩
  revert m hm hm' hmod hm_range
  letI (p : ℕ) : Decidable (IsChenPrime p) := by
    haveI : Decidable (Nat.Prime p) := Nat.decidablePrime p
    haveI : Decidable (LeanLab.AlmostPrimes.bigOmega (p + 2) ≤ 2) := inferInstance
    exact decidable_of_iff (Nat.Prime p ∧ LeanLab.AlmostPrimes.bigOmega (p + 2) ≤ 2) Iff.rfl
  letI (m : ℕ) : Decidable (IsChenMixSum m) := decidable_of_iff (∃ p ∈ Finset.Ico 2 (m + 1), IsChenPrime p ∧ Nat.Prime (m - p)) <| by
    constructor
    · rintro ⟨p, hp, hp', hq⟩
      exact ⟨p, m - p, hp', hq, by
        have : p ≤ m := by
          rw [Finset.mem_Ico] at hp
          omega
        exact Nat.add_sub_of_le this⟩
    · rintro ⟨p, q, hp, hq, hpq⟩
      have hp2 : 2 ≤ p := hp.1.two_le
      subst hpq
      have hp_le : p < p + q + 1 := by omega
      exact ⟨p, Finset.mem_Ico.mpr ⟨hp2, hp_le⟩, hp, by
        have : p + q - p = q := by omega
        rwa [this]⟩
  have hd : ∀ m ∈ Finset.Icc 6 10000, m % 6 = 0 → IsChenMixSum m := of_decide_eq_true (by native_decide)
  intro m hm hm' hmod hm_range
  exact hd m hm_range hmod

/-- LEAF. Unit U-1547. Every `m ≡ 2 mod 6` with `8 ≤ m ≤ 10000` is a Chen prime plus a prime.
Finite check; every such representation with `p, q > 3` has `p = 3 r - 2`, `r` prime, by
`mix_class2_split`; Routes/numerics/U1547/mixed_chen.py finds no exception below `2·10^7`. -/
theorem mix_class2_upto : ∀ m, 8 ≤ m → m ≤ 10000 → m % 6 = 2 → IsChenMixSum m := by
  intro m hm hm' hmod
  have hm_range : m ∈ Finset.Icc 8 10000 := Finset.mem_Icc.mpr ⟨hm, hm'⟩
  revert m hm hm' hmod hm_range
  letI (p : ℕ) : Decidable (IsChenPrime p) := by
    haveI : Decidable (Nat.Prime p) := Nat.decidablePrime p
    haveI : Decidable (LeanLab.AlmostPrimes.bigOmega (p + 2) ≤ 2) := inferInstance
    exact decidable_of_iff (Nat.Prime p ∧ LeanLab.AlmostPrimes.bigOmega (p + 2) ≤ 2) Iff.rfl
  letI (m : ℕ) : Decidable (IsChenMixSum m) := decidable_of_iff (∃ p ∈ Finset.Ico 2 (m + 1), IsChenPrime p ∧ Nat.Prime (m - p)) <| by
    constructor
    · rintro ⟨p, hp, hp', hq⟩
      exact ⟨p, m - p, hp', hq, by
        have : p ≤ m := by
          rw [Finset.mem_Ico] at hp
          omega
        exact Nat.add_sub_of_le this⟩
    · rintro ⟨p, q, hp, hq, hpq⟩
      have hp2 : 2 ≤ p := hp.1.two_le
      subst hpq
      have hp_le : p < p + q + 1 := by omega
      exact ⟨p, Finset.mem_Ico.mpr ⟨hp2, hp_le⟩, hp, by
        have : p + q - p = q := by omega
        rwa [this]⟩
  have hd : ∀ m ∈ Finset.Icc 8 10000, m % 6 = 2 → IsChenMixSum m := of_decide_eq_true (by native_decide)
  intro m hm hm' hmod hm_range
  exact hd m hm_range hmod

end LeanLab.Routes.U1547
