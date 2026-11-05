import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.OpenProblems.Lemoine

/-!
# Five OPEN problems near Goldbach, sealed statements with small true cases

Unit U-1621, run 20261105T0803Z-23816, 2026-11-05. AI wrote the Lean code. Targets for the network,
no claim of progress. Binary Goldbach is OPEN. Nothing here counts as progress on it. Nothing is
tagged ORIGINAL. Every proved item is KNOWN, an elementary remark, or a reading test of a statement.
Records: out/U1621/POOL-LINES.txt and out/U1621/LITSEARCH-U1621-20261105.md.

No GOLDBACH IDEA FUNNEL survivor exists at step g on 2026-11-05: the funnel folder holds only step a
files, so all five come from POOL.md.

1. `PStarStatement`: least prime `p` of `n = m₁ p + m₂ q` is `o(n^ε)`. POOL line 476.
   The printed form, `PStarLiteral`, is FALSE, `not_pStarLiteral`. Repaired by Conditions 1a, 1b.
2. `GranvilleStatement`: the least prime of a Goldbach partition is `≪ log² n log log n`. POOL 478.
3. `JuhaszLastExceptionStatement`: the printed last exceptions of twelve pairs are the true last
   exceptions. POOL line 475. Row `(1, 1)` is Goldbach, row `(1, 2)` is Lemoine.
4. `LeeOClareyStatement`: every `n > 24` is a prime plus a positive non-square-free integer.
   POOL line 467. `LeeOClareyResidual` is the open part left by Campbell.
5. `MarnellStatement`: every even `n > 10` is an odd prime plus an odd semiprime. POOL line 155.

Every reading choice is stated in the docstring of the statement it affects.
-/

namespace LeanLab.OpenProblems.State1621

open Filter Asymptotics

/-- Primality check through `OpenProblems.primeB`, correct below `4096`. -/
def pr (n : ℕ) : Bool := OpenProblems.primeB 64 n

theorem pr_iff {n : ℕ} (h : n < 4096) : pr n = true ↔ n.Prime :=
  OpenProblems.primeB_iff (by omega)

/-! ### 0. Generalised Goldbach partitions, shared by statements 1 to 3 -/

/-- `n = m₁ p + m₂ q` for primes `p, q`, the `(m₁, m₂)`-partition of Juhász, Bartalos, Magyar,
Farkas, arXiv:2304.00024 Definition 2.1. The primes may be equal, the source does not exclude it, and
`(1, 1)` at `n = 4` needs `2 + 2`. -/
def Partitionable (m₁ m₂ n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = m₁ * p + m₂ * q

/-- Conditions 1a and 1b of GGC: `gcd(n, m₁) = gcd(n, m₂) = gcd(m₁, m₂)`, and
`n ≡ m₁ + m₂ mod 2^(s + 1)` where `2^s` is the largest power of 2 dividing both `m₁` and `m₂`.
Here `s` is `padicValNat 2 (gcd m₁ m₂)`, which is that exponent when `m₁, m₂` are positive. -/
def Admissible (m₁ m₂ n : ℕ) : Prop :=
  Nat.gcd n m₁ = Nat.gcd m₁ m₂ ∧ Nat.gcd n m₂ = Nat.gcd m₁ m₂ ∧
    n ≡ m₁ + m₂ [MOD 2 ^ (padicValNat 2 (Nat.gcd m₁ m₂) + 1)]

/-- For a coprime pair the conditions are the reduced form RGGC of the source. -/
theorem admissible_coprime {m₁ m₂ n : ℕ} (h : Nat.gcd m₁ m₂ = 1) :
    Admissible m₁ m₂ n ↔ Nat.gcd n m₁ = 1 ∧ Nat.gcd n m₂ = 1 ∧ (n + m₁ + m₂) % 2 = 0 := by
  unfold Admissible
  have hv : padicValNat 2 1 = 0 := by
    first
      | simp
      | exact padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [h, hv]
  have e : n ≡ m₁ + m₂ [MOD 2 ^ (0 + 1)] ↔ (n + m₁ + m₂) % 2 = 0 := by
    simp only [Nat.ModEq, zero_add, pow_one]
    omega
  rw [e]

/-- `(1, 1)` admissible means even. -/
theorem admissible_one_one {n : ℕ} : Admissible 1 1 n ↔ Even n := by
  rw [admissible_coprime (m₁ := 1) (m₂ := 1) (by norm_num), Nat.even_iff]
  constructor
  · rintro ⟨_, _, h⟩
    omega
  · intro h
    exact ⟨Nat.gcd_one_right n, Nat.gcd_one_right n, by omega⟩

/-- `(1, 2)` admissible means odd. -/
theorem admissible_one_two {n : ℕ} : Admissible 1 2 n ↔ Odd n := by
  rw [admissible_coprime (m₁ := 1) (m₂ := 2) (by norm_num), Nat.odd_iff]
  constructor
  · rintro ⟨_, _, h⟩
    omega
  · intro h
    have h2 : Nat.Coprime 2 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
    exact ⟨Nat.gcd_one_right n, h2.symm, by omega⟩

/-- **OPEN, sealed.** The conjecture GGC for one pair: every large admissible `n` is partitionable.
Source: Juhász, Bartalos, Magyar, Farkas, Empirical verification of a generalization of Goldbach's
conjecture, J. Integer Seq. 27 (2024), Article 24.4.3, Conjecture 1 in Section 2, p. 4;
arXiv:2304.00024 Section 2. No claim for non positive `m₁, m₂`, see `GGCStatement`. -/
def GGC (m₁ m₂ : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → Admissible m₁ m₂ n → Partitionable m₁ m₂ n

/-- **OPEN, sealed.** GGC for all positive `m₁, m₂`. Plain math: for all positive integers `m₁, m₂`,
every sufficiently large integer `n` with `gcd(n, m₁) = gcd(n, m₂) = gcd(m₁, m₂)` and
`n ≡ m₁ + m₂ mod 2^(s+1)` is `m₁ p + m₂ q` with `p, q` prime. Stronger than Goldbach for large `n`,
since `GGC 1 1` is Goldbach above some bound. -/
def GGCStatement : Prop := ∀ m₁ m₂ : ℕ, 0 < m₁ → 0 < m₂ → GGC m₁ m₂

/-! ### 1. The least prime of a generalised partition -/

/-- The least `p` over all partitions `n = m₁ p + m₂ q`, the `p*` of J. Integer Seq. 24.4.3
Definition 4, p. 5, arXiv:2304.00024 Definition 2.2. The source
defines it only when a partition exists. Here it is `0` otherwise, junk value of `sInf`; every
statement below assumes `Partitionable`, so the junk value is never used. -/
noncomputable def pStar (m₁ m₂ n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ n = m₁ * p + m₂ * q}

/-- The conjecture as printed, unrestricted `n`. J. Integer Seq. 24.4.3 Section 5.3.1, p. 12: for
all `m₁` and `m₂` and `ε > 0`, `p*(n) = o(n^ε)`. arXiv:2304.00024 Section 5.3.1 has the same content.
**FALSE**, `not_pStarLiteral`: it needs a condition on `n` that the source does not print. -/
def PStarLiteral : Prop :=
  ∀ m₁ m₂ : ℕ, 0 < m₁ → 0 < m₂ → ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ N : ℕ, ∀ n, N ≤ n →
    Partitionable m₁ m₂ n → (pStar m₁ m₂ n : ℝ) ≤ c * (n : ℝ) ^ ε

/-- **OPEN, sealed.** Plain math: for all positive `m₁, m₂` and all `ε > 0`,
`p*_{m₁,m₂}(n) = o(n^ε)` as `n → ∞` through integers that satisfy Conditions 1a, 1b and have a
partition.

Source: J. Integer Seq. 27 (2024), Article 24.4.3, Section 5.3.1, p. 12; arXiv:2304.00024
Section 5.3.1, read 2026-11-05.

REPAIR, DISCLOSED. The source prints no restriction on `n`. The hypothesis `Admissible` is added by
this unit, because the printed form fails, `not_pStarLiteral`. The source's data covers only
admissible `n`, and a reader taking the conjecture in that sense reads it as sealed here, but the
restriction is ours and not printed. `Partitionable` is the source's own condition from the
definition of `p*`, so this statement does not imply GGC. The explicit `c` spells out little o. -/
def PStarStatement : Prop :=
  ∀ m₁ m₂ : ℕ, 0 < m₁ → 0 < m₂ → ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ N : ℕ, ∀ n, N ≤ n →
    Admissible m₁ m₂ n → Partitionable m₁ m₂ n → (pStar m₁ m₂ n : ℝ) ≤ c * (n : ℝ) ^ ε

theorem pStar_le {m₁ m₂ n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (e : n = m₁ * p + m₂ * q) :
    pStar m₁ m₂ n ≤ p :=
  Nat.sInf_le ⟨hp, q, hq, e⟩

/-- If `2` occurs as `p` it is the least. -/
theorem pStar_eq_two {m₁ m₂ n q : ℕ} (hq : q.Prime) (e : n = m₁ * 2 + m₂ * q) :
    pStar m₁ m₂ n = 2 := by
  refine le_antisymm (pStar_le Nat.prime_two hq e) ?_
  refine le_csInf ⟨2, Nat.prime_two, q, hq, e⟩ fun x hx => hx.1.two_le

/-- For `(2, 3)` and `n = 2 p + 6` the partition is unique: `q` must be even, so `q = 2`. -/
theorem pStar_two_three {p : ℕ} (hp : p.Prime) : pStar 2 3 (2 * p + 6) = p := by
  have hmem : p ∈ {x : ℕ | x.Prime ∧ ∃ q : ℕ, q.Prime ∧ 2 * p + 6 = 2 * x + 3 * q} :=
    ⟨hp, 2, Nat.prime_two, by ring⟩
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_csInf ⟨p, hmem⟩ ?_
  rintro x ⟨_, q, hq, e⟩
  have h2 : 2 ∣ q := by omega
  have hq2 : q = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2).symm
  subst hq2
  omega

/-- Such `n` are not admissible for `(2, 3)`: they fail Condition 1a. -/
theorem not_admissible_two_three (p : ℕ) : ¬ Admissible 2 3 (2 * p + 6) := by
  rw [admissible_coprime (m₁ := 2) (m₂ := 3) (by norm_num)]
  rintro ⟨h, _⟩
  have : 2 ∣ Nat.gcd (2 * p + 6) 2 := Nat.dvd_gcd (by omega) (dvd_refl 2)
  omega

/-- **FALSE as printed.** REFUTATION of the unrestricted conjecture of Section 5.3.1, an elementary
reading failure at `(m₁, m₂) = (2, 3)`, `n = 2 p + 6`, `ε = 1/2`, `c = 1`: then `p* = p ≥ √n`.
The conjecture is meant for admissible `n`, and this `n` is not admissible. No claim of an error in
the mathematics of the paper, whose data is on admissible `n`. FILED, NO OUTREACH. -/
theorem not_pStarLiteral : ¬ PStarLiteral := by
  intro h
  obtain ⟨N, hN⟩ := h 2 3 (by norm_num) (by norm_num) (1 / 2) (by norm_num) 1 (by norm_num)
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 10)
  have hb := hN (2 * p + 6) (by omega) ⟨p, 2, hp, Nat.prime_two, by ring⟩
  rw [pStar_two_three hp, one_mul, ← Real.sqrt_eq_rpow] at hb
  have hp10 : (10 : ℝ) ≤ p := by
    have : 10 ≤ p := by omega
    exact_mod_cast this
  have hsq := (Real.le_sqrt (Nat.cast_nonneg p) (Nat.cast_nonneg _)).mp hb
  push_cast at hsq
  nlinarith

/-- Vacuity of the hypotheses of `PStarStatement`: a positive pair and an admissible `n` with a
partition, with `p*` computed. -/
theorem pStar_instance :
    Admissible 2 3 13 ∧ Partitionable 2 3 13 ∧ pStar 2 3 13 = 2 := by
  refine ⟨?_, ⟨2, 3, Nat.prime_two, Nat.prime_three, by norm_num⟩, ?_⟩
  · rw [admissible_coprime (m₁ := 2) (m₂ := 3) (by norm_num)]
    norm_num
  · exact pStar_eq_two Nat.prime_three (by norm_num)

/-- A second instance on the Goldbach pair. -/
theorem pStar_goldbach_instance : pStar 1 1 4 = 2 :=
  pStar_eq_two Nat.prime_two (by norm_num)

/-! ### 2. Granville, the least prime of a Goldbach partition -/

/-- **OPEN, sealed.** Plain math: there is `C` with: every even `n ≥ 10` has a prime `p` with
`n - p` prime and `p ≤ C log² n log log n`.

Source, primary, page image read 2026-11-05: Granville, van de Lune, te Riele, Checking the Goldbach
conjecture on a vector computer, in Number Theory and Applications, Kluwer 1989, pp. 423 to 433,
p. 432: "On probabilistic grounds we conjecture that ∀n≥10, p(n) << log²n loglog n." Lab copy
P0042, printed page 432, PDF page 10. The minimal partition and `p(n)` are defined on p. 423. Same
statement restated in arXiv:2510.21870 Sections 1 and 5 and J. Integer Seq. 24.4.3.

READING, DISCLOSED. The source's `n` is even, tacit in its context. `n ≥ 10` is the source's range,
and it makes `log log n > 0`. The source's `p(n)` presupposes that a partition exists. The total
form sealed here therefore contains Goldbach, see `granville_iff`; the part with no Goldbach content
is `GranvilleBound`. `n - p` is natural subtraction, harmless since it is prime, so `p < n`. The two
sharp forms with constants 1.51478 and 1.70098 are NOT sealed: the lab has them only from a
secondary source, and they were not found in Granville 2007, P0098. -/
def GranvilleStatement : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, Even n → 10 ≤ n →
    ∃ p : ℕ, p.Prime ∧ (n - p).Prime ∧ (p : ℝ) ≤ C * Real.log n ^ 2 * Real.log (Real.log n)

/-- **OPEN, sealed.** The bound alone: for even `n ≥ 10` that have a partition, the least prime
obeys the bound. No Goldbach content. -/
def GranvilleBound : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, Even n → 10 ≤ n → IsGoldbachSum n →
    ∃ p : ℕ, p.Prime ∧ (n - p).Prime ∧ (p : ℝ) ≤ C * Real.log n ^ 2 * Real.log (Real.log n)

/-- Vacuity of the hypotheses of `GranvilleBound`. -/
theorem granvilleBound_hyp_instance : Even 10 ∧ 10 ≤ 10 ∧ IsGoldbachSum 10 :=
  ⟨by decide, le_refl 10, 3, 7, by norm_num, by norm_num, by norm_num⟩

/-- The total form is Goldbach together with the bound. -/
theorem granville_iff : GranvilleStatement ↔ BinaryGoldbach ∧ GranvilleBound := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨?_, C, fun n he h10 _ => hC n he h10⟩
    intro n he h4
    by_cases h10 : 10 ≤ n
    · obtain ⟨p, hp, hq, _⟩ := hC n he h10
      exact ⟨p, n - p, hp, hq, by have := hq.two_le; omega⟩
    · obtain ⟨k, rfl⟩ := he
      have hk : k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases hk with rfl | rfl | rfl
      · exact ⟨2, 2, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨3, 3, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨3, 5, by norm_num, by norm_num, by norm_num⟩
  · rintro ⟨hG, C, hC⟩
    exact ⟨C, fun n he h10 => hC n he h10 (hG n he (by omega))⟩

/-- Granville's bound gives repaired statement 1 at `(1, 1)`, as Section 5.3.1 of the source says:
`log² n log log n = o(n^ε)`. Elementary, KNOWN. -/
theorem pStar_one_one_of_granville (h : GranvilleStatement) :
    ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ N : ℕ, ∀ n, N ≤ n →
      Admissible 1 1 n → Partitionable 1 1 n → (pStar 1 1 n : ℝ) ≤ c * (n : ℝ) ^ ε := by
  intro ε hε c hc
  obtain ⟨C, hC⟩ := h
  have hD : 0 < |C| + 1 := by positivity
  have key := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) hε).bound
    (show 0 < c / (|C| + 1) by positivity)
  have hL : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hx : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have hall := (key.and (hL.and hx))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hall)
  refine ⟨max N 10, fun n hn ha _ => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn10 : 10 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hk, hL1, _⟩ := hN n hnN
  obtain ⟨p, hp, hq, hb⟩ := hC n (admissible_one_one.mp ha) hn10
  have hs : pStar 1 1 n ≤ p :=
    pStar_le hp hq (by have := hq.two_le; omega)
  have hs' : (pStar 1 1 n : ℝ) ≤ p := by exact_mod_cast hs
  set L := Real.log (n : ℝ) with hLdef
  have hLL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hLLle : Real.log L ≤ L := Real.log_le_self (by linarith)
  have hL0 : 0 ≤ L := by linarith
  have hpow : L ^ (3 : ℝ) = L ^ 3 := by norm_cast
  have hk' : L ^ 3 ≤ c / (|C| + 1) * (n : ℝ) ^ ε := by
    rw [hpow, Real.norm_of_nonneg (pow_nonneg hL0 3),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) ε)] at hk
    exact hk
  have h1 : C * L ^ 2 * Real.log L ≤ (|C| + 1) * L ^ 3 := by
    have hA : C ≤ |C| + 1 := by linarith [le_abs_self C]
    have hB : 0 ≤ L ^ 2 * Real.log L := mul_nonneg (sq_nonneg L) hLL0
    have hC' : L ^ 2 * Real.log L ≤ L ^ 2 * L :=
      mul_le_mul_of_nonneg_left hLLle (sq_nonneg L)
    calc C * L ^ 2 * Real.log L = C * (L ^ 2 * Real.log L) := by ring
      _ ≤ (|C| + 1) * (L ^ 2 * Real.log L) := mul_le_mul_of_nonneg_right hA hB
      _ ≤ (|C| + 1) * (L ^ 2 * L) := mul_le_mul_of_nonneg_left hC' hD.le
      _ = (|C| + 1) * L ^ 3 := by ring
  have hne : |C| + 1 ≠ 0 := hD.ne'
  have h2 : (|C| + 1) * L ^ 3 ≤ c * (n : ℝ) ^ ε := by
    calc (|C| + 1) * L ^ 3 ≤ (|C| + 1) * (c / (|C| + 1) * (n : ℝ) ^ ε) :=
          mul_le_mul_of_nonneg_left hk' hD.le
      _ = c * (n : ℝ) ^ ε := by field_simp
  linarith

/-! ### 3. Last exceptions -/

/-- `k` is the true last exception of the pair: admissible, no partition, and every larger
admissible integer has one. This is `k_{m₁,m₂}` of the source, as a relation, since the source
assumes GGC to define it. -/
def LastException (m₁ m₂ k : ℕ) : Prop :=
  Admissible m₁ m₂ k ∧ ¬ Partitionable m₁ m₂ k ∧
    ∀ n, k < n → Admissible m₁ m₂ n → Partitionable m₁ m₂ n

/-- The rows sealed, `(m₁, m₂, k̂)`. Printed in J. Integer Seq. 24.4.3, Table 4, pp. 16 to 18, The
value of `k̂` for all relatively prime `m₁ ≤ m₂ ≤ 40`. Each row was recomputed for `n ≤ 10⁸`, a sanity check, script numeric.py. -/
def printedRows : List (ℕ × ℕ × ℕ) :=
  [(1, 1, 2), (1, 2, 5), (1, 3, 10), (1, 4, 77), (1, 5, 24), (2, 3, 17), (2, 5, 163), (3, 4, 55),
    (3, 5, 62), (4, 9, 629), (5, 6, 191), (7, 8, 2711)]

/-- **OPEN, sealed.** Plain math: for each row `(m₁, m₂, k̂)` of the list, `k̂` is the largest integer
satisfying Conditions 1a, 1b with no `(m₁, m₂)`-partition.

Source: J. Integer Seq. 24.4.3 Section 2, p. 5: "We conjecture that k̂_{m₁,m₂} = k_{m₁,m₂} for every pair
m₁, m₂ tested." Same sentence in arXiv:2304.00024 Section 2.

SCOPE, DISCLOSED. The source's claim covers all pairs tested. The sealed form covers twelve rows
only, so it is weaker than the source. It is the part this unit read and recomputed; the rest of
Table 4 was not transcribed. It still contains Goldbach and Lemoine, `lastException_one_one_iff`,
`lastException_one_two_iff`. `k̂` is defined with `n ≤ 10¹²`; the sealed form says nothing on that
cap, it asserts the true last exception, which is the content of the sentence. -/
def JuhaszLastExceptionStatement : Prop :=
  ∀ r ∈ printedRows, LastException r.1 r.2.1 r.2.2

theorem not_partitionable_one_one_two : ¬ Partitionable 1 1 2 := by
  rintro ⟨p, q, hp, hq, e⟩
  have := hp.two_le
  have := hq.two_le
  omega

theorem not_partitionable_one_two_five : ¬ Partitionable 1 2 5 := by
  rintro ⟨p, q, hp, hq, e⟩
  have h2 := hp.two_le
  have h3 := hq.two_le
  omega

/-- Row `(1, 1)` is exactly binary Goldbach. -/
theorem lastException_one_one_iff : LastException 1 1 2 ↔ BinaryGoldbach := by
  constructor
  · rintro ⟨_, _, h⟩ n he h4
    obtain ⟨p, q, hp, hq, e⟩ := h n (by omega) (admissible_one_one.mpr he)
    exact ⟨p, q, hp, hq, by omega⟩
  · intro h
    refine ⟨admissible_one_one.mpr (by decide), not_partitionable_one_one_two, ?_⟩
    intro n hn ha
    have he := admissible_one_one.mp ha
    have h4 : 4 ≤ n := by
      obtain ⟨k, rfl⟩ := he
      omega
    obtain ⟨p, q, hp, hq, e⟩ := h n he h4
    exact ⟨p, q, hp, hq, by omega⟩

/-- Row `(1, 2)` is exactly Lemoine's conjecture, as sealed in `OpenProblems/Lemoine.lean`. -/
theorem lastException_one_two_iff : LastException 1 2 5 ↔ Lemoine.LemoineConjecture := by
  constructor
  · rintro ⟨_, _, h⟩ n ho h5
    obtain ⟨p, q, hp, hq, e⟩ := h n h5 (admissible_one_two.mpr ho)
    exact ⟨p, q, hp, hq, by omega⟩
  · intro h
    refine ⟨admissible_one_two.mpr (by decide), not_partitionable_one_two_five, ?_⟩
    intro n hn ha
    obtain ⟨p, q, hp, hq, e⟩ := h n (admissible_one_two.mp ha) hn
    exact ⟨p, q, hp, hq, by omega⟩

/-- The sealed table contains Goldbach and Lemoine. -/
theorem juhasz_implies (h : JuhaszLastExceptionStatement) :
    BinaryGoldbach ∧ Lemoine.LemoineConjecture :=
  ⟨lastException_one_one_iff.mp (h (1, 1, 2) (by simp [printedRows])),
    lastException_one_two_iff.mp (h (1, 2, 5) (by simp [printedRows]))⟩

theorem LastException.unique {m₁ m₂ a b : ℕ} (ha : LastException m₁ m₂ a)
    (hb : LastException m₁ m₂ b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact absurd (ha.2.2 b h hb.1) hb.2.1
  · exact h
  · exact absurd (hb.2.2 a h ha.1) ha.2.1

/-- A last exception gives GGC for the pair. -/
theorem LastException.ggc {m₁ m₂ k : ℕ} (h : LastException m₁ m₂ k) : GGC m₁ m₂ :=
  ⟨k + 1, fun n hn ha => h.2.2 n (by omega) ha⟩

/-- Exhaustive search for a partition. -/
def repB (m₁ m₂ n : ℕ) : Bool :=
  (List.range (n + 1)).any fun q =>
    decide (m₂ * q ≤ n) && decide ((n - m₂ * q) % m₁ = 0) && pr q && pr ((n - m₂ * q) / m₁)

theorem repB_iff {m₁ m₂ n : ℕ} (h1 : 0 < m₁) (h2 : 0 < m₂) (hn : n < 4096) :
    repB m₁ m₂ n = true ↔ Partitionable m₁ m₂ n := by
  simp only [repB, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨q, hqn, ⟨⟨hle, hdvd⟩, hq⟩, hp⟩
    have hm := Nat.le_of_lt_succ hqn
    have hd : n - m₂ * q < 4096 := by omega
    have hdiv : (n - m₂ * q) / m₁ ≤ n - m₂ * q := Nat.div_le_self _ _
    refine ⟨(n - m₂ * q) / m₁, q, (pr_iff (by omega)).mp hp, (pr_iff (by omega)).mp hq, ?_⟩
    have := Nat.div_add_mod (n - m₂ * q) m₁
    rw [hdvd] at this
    omega
  · rintro ⟨p, q, hp, hq, rfl⟩
    have hq1 : q ≤ m₂ * q := Nat.le_mul_of_pos_left q h2
    have hp1 : p ≤ m₁ * p := Nat.le_mul_of_pos_left p h1
    have hsub : m₁ * p + m₂ * q - m₂ * q = m₁ * p := by omega
    refine ⟨q, by omega, ⟨⟨by omega, ?_⟩, (pr_iff (by omega)).mpr hq⟩, ?_⟩
    · rw [hsub]
      exact Nat.mul_mod_right m₁ p
    · rw [hsub, Nat.mul_div_cancel_left _ h1]
      exact (pr_iff (by omega)).mpr hp

/-- Boolean form of the conditions for a coprime pair. -/
def admB (m₁ m₂ n : ℕ) : Bool :=
  decide (Nat.gcd n m₁ = 1) && decide (Nat.gcd n m₂ = 1) && decide ((n + m₁ + m₂) % 2 = 0)

theorem admB_iff {m₁ m₂ n : ℕ} (h : Nat.gcd m₁ m₂ = 1) :
    admB m₁ m₂ n = true ↔ Admissible m₁ m₂ n := by
  rw [admissible_coprime h]
  simp only [admB, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- The finite part of `LastException`: first half exact, tail checked up to `B`. -/
def LastExceptionUpTo (m₁ m₂ k B : ℕ) : Prop :=
  Admissible m₁ m₂ k ∧ ¬ Partitionable m₁ m₂ k ∧
    ∀ n, k < n → n ≤ B → Admissible m₁ m₂ n → Partitionable m₁ m₂ n

/-- Check one row up to `k + 500`. -/
def checkRow (r : ℕ × ℕ × ℕ) : Bool :=
  let m₁ := r.1; let m₂ := r.2.1; let k := r.2.2
  decide (0 < m₁) && decide (0 < m₂) && decide (Nat.gcd m₁ m₂ = 1) && decide (k + 500 < 4096) &&
    admB m₁ m₂ k && !repB m₁ m₂ k &&
    (List.range (k + 501)).all fun n => decide (n ≤ k) || !admB m₁ m₂ n || repB m₁ m₂ n

theorem checkRow_sound {r : ℕ × ℕ × ℕ} (h : checkRow r = true) :
    LastExceptionUpTo r.1 r.2.1 r.2.2 (r.2.2 + 500) := by
  obtain ⟨m₁, m₂, k⟩ := r
  show LastExceptionUpTo m₁ m₂ k (k + 500)
  simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, hg⟩, hb⟩, ha⟩, hr⟩, hall⟩ := h
  refine ⟨(admB_iff hg).mp ha, ?_, ?_⟩
  · intro hp
    have hk := (repB_iff h1 h2 (show k < 4096 by omega)).mpr hp
    rw [hr] at hk
    exact absurd hk (by simp)
  · intro n hkn hnB han
    rcases hall n (by omega) with (h0 | h0) | h0
    · omega
    · rw [(admB_iff hg).mpr han] at h0
      exact absurd h0 (by simp)
    · exact (repB_iff h1 h2 (by omega)).mp h0

/-- Small true case of statement 3: each printed `k̂` is admissible with no partition, and no later
exception up to `k̂ + 500`. Far below the source's `10¹²`. KNOWN, a smoke test only. -/
theorem printedRows_upTo : ∀ r ∈ printedRows, LastExceptionUpTo r.1 r.2.1 r.2.2 (r.2.2 + 500) := by
  have h : printedRows.all checkRow = true := by decide +kernel
  exact fun r hr => checkRow_sound (List.all_eq_true.mp h r hr)

/-! ### 4. Prime plus a positive non-square-free integer -/

/-- `n` is a prime plus a positive integer that is not square-free. -/
def RepNSF (n : ℕ) : Prop := ∃ p r : ℕ, p.Prime ∧ 0 < r ∧ ¬ Squarefree r ∧ n = p + r

/-- **OPEN, sealed.** Plain math: every integer `n > 24` is `p + r` with `p` prime and `r` a positive
integer that is not square-free.

Source: Lee and O'Clarey, On the sum of a prime and a number that is not square-free,
arXiv:2605.02426v1, journal DOI 10.1007/s00013-026-02275-6, Section 1, "we expect this result holds
for every n > 24", and "An unconditional analogue for all n > 24 appears out of reach with the
present method." The same authors, arXiv:2506.11814v3, call the unconditional case an open problem.

READING, DISCLOSED. `0 < r` is in Campbell's Theorem 1.2 and in Lemma 2.1 of the first source. The
first source's theorems say only an integer that is not square-free, and `¬ Squarefree 0` is true in
Mathlib, so without `0 < r` every prime would be represented, `rep_of_prime_of_zero_allowed`.
`n > 24` is sharp, `not_repNSF_24`.

KNOWN PARTS: all `n > 24` under GRH, all odd `n > 24` unconditionally, 2605.02426; every `n > 24`
not divisible by `997#`, Campbell, arXiv:2609.14714, Theorem 1.2. All unrefereed by this lab. -/
def LeeOClareyStatement : Prop := ∀ n : ℕ, 24 < n → RepNSF n

/-- The statement of Campbell, arXiv:2609.14714, Theorem 1.2, entered as a Prop, not proved here. -/
def CampbellTheorem12 : Prop := ∀ n : ℕ, 24 < n → ¬ primorial 997 ∣ n → RepNSF n

/-- **OPEN, sealed.** The part left open by Campbell's Theorem 1.2: integers above 24 divisible by
`997#`, the product of the primes up to 997. Plain math: every `n > 24` with `997# ∣ n` is a prime
plus a positive non-square-free integer. Campbell states any counterexample exceeds `10^415`. -/
def LeeOClareyResidual : Prop := ∀ n : ℕ, 24 < n → primorial 997 ∣ n → RepNSF n

/-- Vacuity of the hypotheses of `LeeOClareyResidual`. -/
theorem residual_hyp_instance : ∃ n : ℕ, 24 < n ∧ primorial 997 ∣ n := by
  have h := primorial_pos 997
  exact ⟨25 * primorial 997, by omega, dvd_mul_left _ _⟩

/-- CONDITIONAL on Campbell's theorem, a hypothesis here: the statement equals its residual. -/
theorem leeOClarey_iff_residual (h : CampbellTheorem12) :
    LeeOClareyStatement ↔ LeeOClareyResidual := by
  constructor
  · exact fun hs n hn _ => hs n hn
  · intro hr n hn
    by_cases hd : primorial 997 ∣ n
    · exact hr n hn hd
    · exact h n hn hd

/-- Reading test: with `r = 0` allowed every prime has a representation. -/
theorem rep_of_prime_of_zero_allowed {n : ℕ} (hn : n.Prime) :
    ∃ p r : ℕ, p.Prime ∧ ¬ Squarefree r ∧ n = p + r :=
  ⟨n, 0, hn, not_squarefree_zero, rfl⟩

/-- `n > 24` is sharp. -/
theorem not_repNSF_24 : ¬ RepNSF 24 := by
  rintro ⟨p, r, hp, hr, hs, e⟩
  have hp2 := hp.two_le
  have hpr : p = 24 - r := by omega
  subst hpr
  have hr24 : r ≤ 22 := by omega
  interval_cases r <;> revert hp hs <;> first | (norm_num; done) | decide +kernel

/-- Square witness search, sound. -/
def nsfB (r : ℕ) : Bool := (List.range 60).any fun d => decide (2 ≤ d) && decide (r % (d * d) = 0)

theorem nsfB_sound {r : ℕ} (h : nsfB r = true) : ¬ Squarefree r := by
  simp only [nsfB, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨d, _, hd, hm⟩ := h
  intro hs
  have hu := hs d (Nat.dvd_of_mod_eq_zero hm)
  have := Nat.isUnit_iff.mp hu
  omega

/-- Search for a representation of `n` by a small `r`. -/
def leeB (n : ℕ) : Bool :=
  (List.range n).any fun r => decide (0 < r) && nsfB r && decide (r < n) && pr (n - r)

theorem leeB_sound {n : ℕ} (hn : n < 4096) (h : leeB n = true) : RepNSF n := by
  simp only [leeB, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨r, _, ⟨⟨hr, hs⟩, hrn⟩, hp⟩ := h
  exact ⟨n - r, r, (pr_iff (by omega)).mp hp, hr, nsfB_sound hs, by omega⟩

/-- Small true case, far below the `8 · 10⁹` of the source. KNOWN, a smoke test only. -/
theorem repNSF_small : ∀ n, 24 < n → n ≤ 1000 → RepNSF n := by
  have h : (List.range 1001).all (fun n => decide (n ≤ 24) || leeB n) = true := by decide +kernel
  intro n h1 h2
  have := List.all_eq_true.mp h n (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h0 | h0
  · omega
  · exact leeB_sound (by omega) h0

/-! ### 5. Odd prime plus odd semiprime -/

/-- `s` is a product of two primes, not necessarily distinct, the usual meaning of semiprime. -/
def IsSemiprime (s : ℕ) : Prop := ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ s = a * b

/-- `n` is an odd prime plus an odd semiprime. -/
def RepMarnell (n : ℕ) : Prop := ∃ p s : ℕ, p.Prime ∧ Odd p ∧ IsSemiprime s ∧ Odd s ∧ n = p + s

/-- **OPEN, sealed.** Plain math: every even integer greater than 10 is an odd prime plus an odd
semiprime.

Source: Open Problem Garden, Sum of prime and semiprime conjecture, read 2026-11-05: "Every even
number greater than 10 can be represented as the sum of an odd prime number and an odd semiprime."
Credited there to G. R. Marnell, Ten Prime Conjectures, J. Recreational Math. 33:3, 2004 to 2005,
pp. 193 to 196. That article was not read, so this statement rests on the Garden wording. The page
prints no status field and lists no proof or counterexample.

READING, DISCLOSED. Semiprime allows squares. It must: with distinct primes the statement fails at
12, `not_repDistinct_twelve`, and numerically also at 14, 16 and 30. `10 < n` is sharp, `not_repMarnell_ten`. Chen's theorem
gives `p + q` or `p + q r` for large even `n`, which does not separate the two cases: a comment on
the Garden page names the parity problem as the obstacle, so neither this statement nor Goldbach is
known to imply the other. -/
def MarnellStatement : Prop := ∀ n : ℕ, Even n → 10 < n → RepMarnell n

/-- The stricter reading with distinct primes, for the reading test only. -/
def RepDistinct (n : ℕ) : Prop :=
  ∃ p a b : ℕ, p.Prime ∧ Odd p ∧ a.Prime ∧ b.Prime ∧ a ≠ b ∧ Odd (a * b) ∧ n = p + a * b

theorem not_prime_of_isSemiprime {s : ℕ} (h : IsSemiprime s) : ¬ s.Prime := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  exact Nat.not_prime_mul ha.one_lt.ne' hb.one_lt.ne'

/-- `10 < n` is sharp. -/
theorem not_repMarnell_ten : ¬ RepMarnell 10 := by
  rintro ⟨p, s, hp, ho, hs, _, e⟩
  have hns := not_prime_of_isSemiprime hs
  have hs0 : s = 10 - p := by omega
  subst hs0
  have h2 := hp.two_le
  have hle : p ≤ 10 := by omega
  have ho' := Nat.odd_iff.mp ho
  have h3 : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 9 := by omega
  rcases h3 with rfl | rfl | rfl | rfl
  · exact hns (by norm_num)
  · exact hns (by norm_num)
  · exact hns (by norm_num)
  · exact absurd hp (by norm_num)

/-- The source's own reading works at `12`: `3 + 9`. -/
theorem repMarnell_twelve : RepMarnell 12 :=
  ⟨3, 9, Nat.prime_three, by decide, ⟨3, 3, Nat.prime_three, Nat.prime_three, by norm_num⟩,
    by decide, by norm_num⟩

/-- Reading test: distinct primes fail at `12`, so semiprime must include `9`: an odd product of two
distinct primes is at least `15`. -/
theorem not_repDistinct_twelve : ¬ RepDistinct 12 := by
  rintro ⟨p, a, b, hp, _, ha, hb, hne, hodd, e⟩
  obtain ⟨hao, hbo⟩ := Nat.odd_mul.mp hodd
  have hao' := Nat.odd_iff.mp hao
  have hbo' := Nat.odd_iff.mp hbo
  have ha2 := ha.two_le
  have hb2 := hb.two_le
  have h15 : 15 ≤ a * b := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact Nat.mul_le_mul (show 3 ≤ a by omega) (show 5 ≤ b by omega)
    · have := Nat.mul_le_mul (show 5 ≤ a by omega) (show 3 ≤ b by omega)
      omega
  omega

/-- Search for a semiprime factorisation. -/
def semiB (s : ℕ) : Bool :=
  (List.range 64).any fun a => decide (a ≠ 0) && decide (s % a = 0) && pr a && pr (s / a)

theorem semiB_sound {s : ℕ} (hs : s < 4096) (h : semiB s = true) : IsSemiprime s := by
  simp only [semiB, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨a, ha64, ⟨⟨_, hm⟩, ha⟩, hq⟩ := h
  have hdiv : s / a ≤ s := Nat.div_le_self _ _
  refine ⟨a, s / a, (pr_iff (by omega)).mp ha, (pr_iff (by omega)).mp hq, ?_⟩
  exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)).symm

/-- Search for a representation of `n`. -/
def marB (n : ℕ) : Bool :=
  (List.range n).any fun p =>
    decide (p % 2 = 1) && pr p && decide ((n - p) % 2 = 1) && decide (p < n) && semiB (n - p)

theorem marB_sound {n : ℕ} (hn : n < 4096) (h : marB n = true) : RepMarnell n := by
  simp only [marB, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨p, _, ⟨⟨⟨hodd, hp⟩, hso⟩, hpn⟩, hs⟩ := h
  exact ⟨p, n - p, (pr_iff (by omega)).mp hp, Nat.odd_iff.mpr hodd,
    semiB_sound (by omega) hs, Nat.odd_iff.mpr hso, by omega⟩

/-- Small true case, a smoke test only. -/
theorem marnell_small : ∀ n, Even n → 10 < n → n ≤ 1000 → RepMarnell n := by
  have h : (List.range 1001).all
      (fun n => decide (n ≤ 10) || decide (n % 2 = 1) || marB n) = true := by decide +kernel
  intro n he h1 h2
  have := List.all_eq_true.mp h n (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  have he' := Nat.even_iff.mp he
  rcases this with (h0 | h0) | h0
  · omega
  · omega
  · exact marB_sound (by omega) h0

end LeanLab.OpenProblems.State1621

#print axioms LeanLab.OpenProblems.State1621.not_pStarLiteral
#print axioms LeanLab.OpenProblems.State1621.pStar_instance
#print axioms LeanLab.OpenProblems.State1621.granville_iff
#print axioms LeanLab.OpenProblems.State1621.pStar_one_one_of_granville
#print axioms LeanLab.OpenProblems.State1621.lastException_one_one_iff
#print axioms LeanLab.OpenProblems.State1621.lastException_one_two_iff
#print axioms LeanLab.OpenProblems.State1621.juhasz_implies
#print axioms LeanLab.OpenProblems.State1621.printedRows_upTo
#print axioms LeanLab.OpenProblems.State1621.residual_hyp_instance
#print axioms LeanLab.OpenProblems.State1621.leeOClarey_iff_residual
#print axioms LeanLab.OpenProblems.State1621.not_repNSF_24
#print axioms LeanLab.OpenProblems.State1621.repNSF_small
#print axioms LeanLab.OpenProblems.State1621.not_repMarnell_ten
#print axioms LeanLab.OpenProblems.State1621.not_repDistinct_twelve
#print axioms LeanLab.OpenProblems.State1621.marnell_small
