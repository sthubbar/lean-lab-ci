import Mathlib
import LeanLab.OpenProblems.Erdos9
import LeanLab.OpenProblems.PrimeCheck

/-!
# Four OPEN problems, sealed statements with small true cases

Unit U-1616, run 20261104T0803Z-26516, 2026-11-04. AI wrote the Lean code. Targets for the network,
no claim of progress. Nothing here counts as progress on Goldbach. Nothing is tagged ORIGINAL. Every
proved item is KNOWN or an elementary remark. The screening record is out/U-1616/POOLSTATUS.txt and
the search record out/U-1616/LITSEARCH-U1616-20261104.md.

1. `Erdos10Statement`: for some `k` every large integer is a prime plus at most `k` powers of 2.
2. `Erdos1055Statement`: infinitely many primes in each Erdős-Selfridge `p + 1` class, exclusive
   reading. `Erdos1055Limit`, `Selfridge1055Bounded`: the two guesses on the least prime of a class.
3. `Erdos852PartOne`, `Erdos852PartTwo`: runs of distinct prime gaps.
4. `Erdos238Statement`: long runs of consecutive primes with all gaps above a constant.

Page wording was tested against first cases before sealing. See each section.
-/

namespace LeanLab.OpenProblems.State1616

open Filter

/-! ### 1. Erdős 10, a prime plus at most `k` powers of 2 -/

/-- Integers `p + 2^e₁ + ... + 2^eⱼ` with `j ≤ k` and repeats allowed, `2^0 = 1` included. Same set
as `sumPrimeAndTwoPows k` of FormalConjectures/ErdosProblems/10.lean. -/
def SumPrimePows (k : ℕ) : Set ℕ :=
  {n | ∃ (p : ℕ) (E : Multiset ℕ), p.Prime ∧ E.card ≤ k ∧ n = p + (E.map (2 ^ ·)).sum}

/-- **OPEN, sealed.** Plain math: there is `k` such that every large integer is a prime plus at most
`k` powers of 2. Source: Erdős problem 10, erdosproblems.com/10, read 2026-11-04, page edit
11 April 2026, status open, no finite computation settles it. Same as `erdos_10` in Formal
Conjectures, tagged research open. Page words `powers of 2` must include `1`, see
`not_statement_of_one_excluded`. Vacuity `one_mem_two`, `three_mem`, with `grechuk_not_mem`. -/
def Erdos10Statement : Prop := ∃ k N : ℕ, ∀ n, N ≤ n → n ∈ SumPrimePows k

/-- Binary digit sum. -/
def popc (n : ℕ) : ℕ := (Nat.digits 2 n).sum

theorem popc_zero : popc 0 = 0 := by simp [popc]

theorem popc_step (n : ℕ) : popc n = n % 2 + popc (n / 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp [popc]
  · rw [popc, Nat.digits_def' (by norm_num) h]
    simp [popc]

theorem popc_two_mul (n : ℕ) : popc (2 * n) = popc n := by
  rw [popc_step (2 * n)]
  simp

theorem popc_two_mul_add_one (n : ℕ) : popc (2 * n + 1) = popc n + 1 := by
  rw [popc_step (2 * n + 1)]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]
  omega

theorem popc_two_pow (e : ℕ) : popc (2 ^ e) = 1 := by
  induction e with
  | zero => rw [pow_zero, popc_step]; simp [popc_zero]
  | succ e ih => rw [pow_succ, mul_comm, popc_two_mul, ih]

/-- The digit sum is subadditive. -/
theorem popc_add (a b : ℕ) : popc (a + b) ≤ popc a + popc b := by
  induction h : a + b using Nat.strong_induction_on generalizing a b with
  | _ s ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · subst h; simp [popc_zero]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · subst h; simp [popc_zero]
    obtain ⟨x, hx⟩ : ∃ x, a = 2 * x ∨ a = 2 * x + 1 := ⟨a / 2, by omega⟩
    obtain ⟨y, hy⟩ : ∃ y, b = 2 * y ∨ b = 2 * y + 1 := ⟨b / 2, by omega⟩
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · have e : 2 * x + 2 * y = 2 * (x + y) := by ring
      subst h
      rw [e, popc_two_mul, popc_two_mul, popc_two_mul]
      exact ih (x + y) (by omega) x y rfl
    · have e : 2 * x + (2 * y + 1) = 2 * (x + y) + 1 := by ring
      subst h
      rw [e, popc_two_mul_add_one, popc_two_mul, popc_two_mul_add_one]
      have := ih (x + y) (by omega) x y rfl
      omega
    · have e : 2 * x + 1 + 2 * y = 2 * (x + y) + 1 := by ring
      subst h
      rw [e, popc_two_mul_add_one, popc_two_mul, popc_two_mul_add_one]
      have := ih (x + y) (by omega) x y rfl
      omega
    · have e : 2 * x + 1 + (2 * y + 1) = 2 * (x + y + 1) := by ring
      subst h
      rw [e, popc_two_mul, popc_two_mul_add_one, popc_two_mul_add_one]
      have h1 := ih (x + y + 1) (by omega) (x + y) 1 rfl
      have h2 := ih (x + y) (by omega) x y rfl
      have h3 : popc 1 = 1 := by simpa using popc_two_pow 0
      omega

theorem popc_sum_le (E : Multiset ℕ) : popc (E.map (2 ^ ·)).sum ≤ E.card := by
  induction E using Multiset.induction_on with
  | empty => simp [popc_zero]
  | cons e E ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have := popc_add (2 ^ e) (E.map (2 ^ ·)).sum
    rw [popc_two_pow] at this
    omega

/-- The carrying step: every `m` is a sum of exactly `popc m` powers of 2. -/
theorem exists_multiset (m : ℕ) : ∃ E : Multiset ℕ, E.card = popc m ∧ (E.map (2 ^ ·)).sum = m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, by simp [popc_zero]⟩
    obtain ⟨E, h1, h2⟩ := ih (m / 2) (by omega)
    have hd : ∀ F : Multiset ℕ, ((F.map (· + 1)).map (2 ^ ·)).sum = 2 * (F.map (2 ^ ·)).sum := by
      intro F
      induction F using Multiset.induction_on with
      | empty => simp
      | cons e F ih' =>
        simp only [Multiset.map_cons, Multiset.sum_cons, ih']
        ring
    have hm2 : m = 2 * (m / 2) ∨ m = 2 * (m / 2) + 1 := by omega
    rcases hm2 with h | h
    · refine ⟨E.map (· + 1), ?_, ?_⟩
      · rw [Multiset.card_map, h1, h, popc_two_mul]
        congr 1
        omega
      · rw [hd, h2]
        omega
    · refine ⟨0 ::ₘ E.map (· + 1), ?_, ?_⟩
      · rw [Multiset.card_cons, Multiset.card_map, h1, h, popc_two_mul_add_one]
        have : (2 * (m / 2) + 1) / 2 = m / 2 := by omega
        rw [this]
      · rw [Multiset.map_cons, Multiset.sum_cons, hd, h2]
        simp only [pow_zero]
        omega

/-- Decidable form: `n` lies in `S_k` exactly when `n - p` has at most `k` binary ones for some
prime `p ≤ n`. This is the check any finite certificate uses. PROVED, elementary. -/
theorem mem_iff (k n : ℕ) :
    n ∈ SumPrimePows k ↔ ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ popc (n - p) ≤ k := by
  constructor
  · rintro ⟨p, E, hp, hE, rfl⟩
    refine ⟨p, hp, by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    exact (popc_sum_le E).trans hE
  · rintro ⟨p, hp, hle, hk⟩
    obtain ⟨E, h1, h2⟩ := exists_multiset (n - p)
    exact ⟨p, E, hp, by omega, by omega⟩

theorem sumPrimePows_mono {j k : ℕ} (h : j ≤ k) : SumPrimePows j ⊆ SumPrimePows k := by
  rintro n ⟨p, E, hp, hE, e⟩
  exact ⟨p, E, hp, hE.trans h, e⟩

/-- Existence for one `n` is free: `n ≥ 2` lies in `S_{popc (n - 2)}`. Uniformity is the problem. -/
theorem mem_popc_sub_two {n : ℕ} (hn : 2 ≤ n) : n ∈ SumPrimePows (popc (n - 2)) :=
  (mem_iff _ _).2 ⟨2, Nat.prime_two, hn, le_rfl⟩

theorem one_not_mem (k : ℕ) : 1 ∉ SumPrimePows k := by
  rintro ⟨p, E, hp, -, e⟩
  have := hp.two_le
  omega

/-- Vacuity, with `three_mem`: the set is not empty. -/
theorem two_mem (k : ℕ) : 2 ∈ SumPrimePows k :=
  ⟨2, 0, Nat.prime_two, by simp, by simp⟩

theorem three_mem : 3 ∈ SumPrimePows 1 := (mem_iff _ _).2 ⟨3, Nat.prime_three, le_rfl, by
  simp [popc_zero]⟩

/-- `k ≤ 1` fails, by parity alone: `n = 30 j + 22` has `n - 1` divisible by 3 and `n - 2` by 5.
PROVED, elementary. -/
theorem not_mem_one (j : ℕ) : 30 * j + 22 ∉ SumPrimePows 1 := by
  rw [mem_iff]
  rintro ⟨p, hp, hle, hk⟩
  obtain ⟨E, h1, h2⟩ := exists_multiset (30 * j + 22 - p)
  have hc : E.card = 0 ∨ E.card = 1 := by omega
  rcases hc with hc | hc
  · rw [Multiset.card_eq_zero] at hc
    subst hc
    have hpe : p = 30 * j + 22 := by simp at h2; omega
    have : 2 ∣ p := ⟨15 * j + 11, by omega⟩
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this
    omega
  · obtain ⟨e, rfl⟩ := Multiset.card_eq_one.1 hc
    have h2' : 30 * j + 22 - p = 2 ^ e := by simpa using h2.symm
    rcases hp.eq_two_or_odd with rfl | hodd
    · have h5 : 5 ∣ 2 ^ e := ⟨6 * j + 4, by omega⟩
      have := (Nat.prime_five).dvd_of_dvd_pow h5
      omega
    · rcases e with _ | e
      · have h3 : 3 ∣ p := ⟨10 * j + 7, by simp at h2'; omega⟩
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3
        have : p = 3 := this.symm
        simp at h2'
        omega
      · have : 2 ^ (e + 1) = 2 * 2 ^ e := by ring
        omega

/-- `k ≤ 1` cannot work. PROVED, elementary. -/
theorem not_tail_one (N : ℕ) : ∃ n, N ≤ n ∧ n ∉ SumPrimePows 1 :=
  ⟨30 * N + 22, by omega, not_mem_one N⟩

/-- Reading test. With `1` not counted as a power of 2, the statement is false at once: an even `n`
forces `p = 2`, so `n - 2` would need bounded digit sum. So `1` must count. PROVED, elementary. -/
theorem not_statement_of_one_excluded :
    ¬ ∃ k N : ℕ, ∀ n, N ≤ n → ∃ (p : ℕ) (E : Multiset ℕ), p.Prime ∧ E.card ≤ k ∧
      n = p + (E.map fun e => 2 ^ (e + 1)).sum := by
  rintro ⟨k, N, h⟩
  have hsum : ∀ F : Multiset ℕ, 2 ∣ (F.map fun e => 2 ^ (e + 1)).sum := by
    intro F
    refine Multiset.dvd_sum fun x hx => ?_
    obtain ⟨e, -, rfl⟩ := Multiset.mem_map.1 hx
    exact ⟨2 ^ e, by ring⟩
  have hones : ∀ M : ℕ, popc (2 ^ M - 1) = M := by
    intro M
    induction M with
    | zero => simp [popc_zero]
    | succ M ih =>
      have hpos : 0 < 2 ^ M := by positivity
      have : 2 ^ (M + 1) - 1 = 2 * (2 ^ M - 1) + 1 := by rw [pow_succ]; omega
      rw [this, popc_two_mul_add_one, ih]
  set M := k + N + 1 with hM
  have hbig : N ≤ 2 ^ (M + 1) := by
    have := Nat.lt_two_pow_self (n := M + 1)
    omega
  obtain ⟨p, E, hp, hE, e⟩ := h _ hbig
  have heven : 2 ∣ p := by
    have h1 : 2 ∣ 2 ^ (M + 1) := ⟨2 ^ M, by ring⟩
    have h2 := hsum E
    rw [e] at h1
    exact (Nat.dvd_add_left h2).1 h1
  have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 heven).symm
  subst hp2
  have hmap : (E.map fun e => 2 ^ (e + 1)).sum = ((E.map (· + 1)).map (2 ^ ·)).sum := by
    rw [Multiset.map_map]; rfl
  have hle := popc_sum_le (E.map (· + 1))
  rw [← hmap, Multiset.card_map] at hle
  have hval : (E.map fun e => 2 ^ (e + 1)).sum = 2 * (2 ^ M - 1) := by
    have hpos : 0 < 2 ^ M := by positivity
    rw [pow_succ] at e
    omega
  rw [hval, popc_two_mul, hones] at hle
  omega

/-- Parity bridge from `Erdos9A`. An odd `t` in `Erdos9A`, not prime, with `popc (t - 1) > 3` gives
an even `t + 1` outside `S_3`. PROVED, elementary. -/
theorem not_mem_three_of_erdos9 {t : ℕ} (ht : t ∈ Erdos9.Erdos9A) (hnp : ¬ t.Prime)
    (hpc : 3 < popc (t - 1)) : t + 1 ∉ SumPrimePows 3 := by
  obtain ⟨hodd, hno⟩ := ht
  rw [mem_iff]
  rintro ⟨p, hp, hle, hk⟩
  obtain ⟨u, rfl⟩ := hodd
  rcases hp.eq_two_or_odd with rfl | hpo
  · have : 2 * u + 1 + 1 - 2 = 2 * u + 1 - 1 := by omega
    rw [this] at hk
    omega
  have hm : 2 * u + 1 + 1 - p = 2 * ((2 * u + 1 + 1 - p) / 2) + 1 := by omega
  set w := (2 * u + 1 + 1 - p) / 2 with hw
  rw [hm, popc_two_mul_add_one] at hk
  obtain ⟨E, h1, h2⟩ := exists_multiset w
  have hc : E.card = 0 ∨ E.card = 1 ∨ E.card = 2 := by omega
  rcases hc with hc | hc | hc
  · rw [Multiset.card_eq_zero] at hc
    subst hc
    have : w = 0 := by simpa using h2.symm
    apply hnp
    have : 2 * u + 1 = p := by omega
    rwa [this]
  · obtain ⟨e, rfl⟩ := Multiset.card_eq_one.1 hc
    have : w = 2 ^ e := by simpa using h2.symm
    exact hno ⟨p, e, e, hp, by omega⟩
  · obtain ⟨e, f, rfl⟩ := Multiset.card_eq_two.1 hc
    have : w = 2 ^ e + 2 ^ f := by simpa using h2.symm
    refine hno ⟨p, e + 1, f + 1, hp, ?_⟩
    rw [pow_succ, pow_succ]
    omega

/-- Grechuk's example, from the lab's `Erdos9.mem_1117175145`. PROVED, KNOWN, on the page. -/
theorem grechuk_not_mem : 1117175146 ∉ SumPrimePows 3 := by
  have h := not_mem_three_of_erdos9 (t := 1117175145) Erdos9.mem_1117175145 (by norm_num)
    (by simp [popc])
  simpa using h

/-! ### 2. Erdős 1055, the `p + 1` classes -/

/-- `ClassLE r p`: `p` is a prime of class at most `r`, `r ≥ 1`. Class at most 1 means `p + 1` has
only the prime factors 2 and 3. Class at most `r + 1` means every prime factor of `p + 1` is 2, 3 or
of class at most `r`. -/
def ClassLE : ℕ → ℕ → Prop
  | 0, _ => False
  | r + 1, p => p.Prime ∧ ∀ q : ℕ, q.Prime → q ∣ p + 1 → q = 2 ∨ q = 3 ∨ ClassLE r q

/-- `p` is in class exactly `r`. This is the exclusive reading, the classes partition the primes,
see `isClass_unique`, `exists_isClass`. It agrees with the page wording plus `p` in no lower class,
see `isClass_succ_iff`. -/
abbrev IsClass (r p : ℕ) : Prop := ClassLE r p ∧ ¬ ClassLE (r - 1) p

/-- **OPEN, sealed.** Plain math: for each `r ≥ 1` there are infinitely many primes of class exactly
`r`, where class 1 means `p + 1 = 2^a 3^b` and class `r` means every prime factor of `p + 1` is of
class at most `r - 1`, with equality for at least one, and `p` is of no lower class. Source: Erdős
problem 1055, erdosproblems.com/1055, read 2026-11-04, status open; Erdős, Problems in number theory
and combinatorics, Manitoba 1977, p. 53, seen only as quoted in OMOS-POOL11; Guy A18. Same as
`erdos_1055` in Formal Conjectures, tagged research open. The clause `no lower class` is not on the
page; without it `lit_statement_iff` shows the question is only class 1. Vacuity `isClass_two_13`
and `exists_isClass_of_pos`. -/
def Erdos1055Statement : Prop := ∀ r : ℕ, 1 ≤ r → {p | IsClass r p}.Infinite

/-- The least prime of class `r`, `sInf` of a nonempty set by `exists_isClass_of_pos`. -/
noncomputable def leastPrime (r : ℕ) : ℕ := sInf {p | IsClass r p}

/-- **OPEN, sealed.** Plain math: `p_r^(1/r) → ∞`, the guess of Erdős on erdosproblems.com/1055,
read 2026-11-04. `erdos_1055.variants.erdos_limit` in Formal Conjectures. Vacuity as above; it
contradicts `Selfridge1055Bounded`, so at most one of the two holds. -/
def Erdos1055Limit : Prop :=
  Tendsto (fun r : ℕ => (leastPrime r : ℝ) ^ (1 / (r : ℝ))) atTop atTop

/-- **OPEN, sealed.** Plain math: `p_r^(1/r)` is bounded, the guess of Selfridge on the same page.
`erdos_1055.variants.selfridge_limit` in Formal Conjectures. Vacuity as above. -/
def Selfridge1055Bounded : Prop :=
  ∃ M : ℝ, ∀ r : ℕ, 1 ≤ r → (leastPrime r : ℝ) ^ (1 / (r : ℝ)) ≤ M

theorem not_classLE_zero (p : ℕ) : ¬ ClassLE 0 p := by
  rw [ClassLE]
  exact id

theorem classLE_succ_iff {r p : ℕ} : ClassLE (r + 1) p ↔
    p.Prime ∧ ∀ q : ℕ, q.Prime → q ∣ p + 1 → q = 2 ∨ q = 3 ∨ ClassLE r q := by
  rw [ClassLE]

theorem mkLE {r p : ℕ} (hp : p.Prime)
    (h : ∀ q : ℕ, q.Prime → q ∣ p + 1 → q = 2 ∨ q = 3 ∨ ClassLE r q) : ClassLE (r + 1) p :=
  classLE_succ_iff.2 ⟨hp, h⟩

theorem ClassLE.fac {r p : ℕ} (h : ClassLE (r + 1) p) (q : ℕ) (hq : q.Prime) (hd : q ∣ p + 1) :
    q = 2 ∨ q = 3 ∨ ClassLE r q :=
  (classLE_succ_iff.1 h).2 q hq hd

theorem ClassLE.prime {r p : ℕ} (h : ClassLE r p) : p.Prime := by
  cases r with
  | zero => exact (not_classLE_zero p h).elim
  | succ r => exact (classLE_succ_iff.1 h).1

theorem classLE_one_two : ClassLE 1 2 := by
  refine mkLE Nat.prime_two fun q hq hd => Or.inr (Or.inl ?_)
  exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (by simpa using hd)

theorem classLE_one_three : ClassLE 1 3 := by
  refine mkLE Nat.prime_three fun q hq hd => Or.inl ?_
  have h4 : q ∣ 2 ^ 2 := by simpa using hd
  exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h4)

theorem classLE_succ {r p : ℕ} (h : ClassLE r p) : ClassLE (r + 1) p := by
  induction r generalizing p with
  | zero => exact (not_classLE_zero p h).elim
  | succ r ih =>
    refine mkLE h.prime fun q hq hd => ?_
    rcases h.fac q hq hd with h2 | h3 | hr
    · exact Or.inl h2
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (ih hr))

theorem classLE_mono {r s p : ℕ} (hrs : r ≤ s) (h : ClassLE r p) : ClassLE s p := by
  induction hrs with
  | refl => exact h
  | step _ ih => exact classLE_succ ih

/-- 2 and 3 have class at most `r` for each `r ≥ 1`. -/
theorem classLE_of_two_or_three {r q : ℕ} (hr : 1 ≤ r) (h : q = 2 ∨ q = 3) : ClassLE r q := by
  rcases h with rfl | rfl
  · exact classLE_mono hr classLE_one_two
  · exact classLE_mono hr classLE_one_three

/-- A prime factor of `p + 1` other than 3 is at most `(p + 1) / 2`, and 3 divides it only when
`p + 1 ≠ 3` or `p = 2`. -/
theorem two_mul_le_of_dvd {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hd : q ∣ p + 1) (hne : p ≠ 2) :
    2 * q ≤ p + 1 := by
  obtain ⟨m, hm⟩ := hd
  have hodd : Odd p := hp.odd_of_ne_two hne
  rcases m with _ | _ | m
  · simp at hm
  · simp at hm
    subst hm
    have h2 := hp.two_le
    obtain ⟨u, rfl⟩ := hodd
    have : 2 ∣ 2 * u + 1 + 1 := ⟨u + 1, by ring⟩
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 this
    omega
  · rw [hm]
    nlinarith [Nat.zero_le (q * m)]

/-- Every prime has a class. PROVED, elementary. -/
theorem exists_classLE {p : ℕ} (hp : p.Prime) : ∃ r, ClassLE r p := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    by_cases h2 : p = 2
    · exact ⟨1, h2 ▸ classLE_one_two⟩
    have hb : ∀ q, ∃ r, q ∈ (p + 1).primeFactors → ClassLE r q := by
      intro q
      by_cases hq : q ∈ (p + 1).primeFactors
      · have hqp := Nat.prime_of_mem_primeFactors hq
        have hqd := Nat.dvd_of_mem_primeFactors hq
        have := two_mul_le_of_dvd hp hqp hqd h2
        have h3 := hqp.two_le
        obtain ⟨r, hr⟩ := ih q (by omega) hqp
        exact ⟨r, fun _ => hr⟩
      · exact ⟨0, fun h => absurd h hq⟩
    choose f hf using hb
    refine ⟨(p + 1).primeFactors.sup f + 1, mkLE hp fun q hq hd => Or.inr (Or.inr ?_)⟩
    have hm : q ∈ (p + 1).primeFactors :=
      Nat.mem_primeFactors.2 ⟨hq, hd, by omega⟩
    exact classLE_mono (Finset.le_sup (f := f) hm) (hf q hm)

/-- Each prime has an exact class, at least 1. -/
theorem exists_isClass {p : ℕ} (hp : p.Prime) : ∃ r, 1 ≤ r ∧ IsClass r p := by
  classical
  have h := exists_classLE hp
  refine ⟨Nat.find h, ?_, Nat.find_spec h, ?_⟩
  · by_contra hc
    have h0 : Nat.find h = 0 := by omega
    have := Nat.find_spec h
    rw [h0] at this
    exact this
  · rcases hz : Nat.find h with _ | k
    · exact not_classLE_zero p
    · exact Nat.find_min h (by omega)

/-- The class is unique, so the classes partition the primes. -/
theorem isClass_unique {r s p : ℕ} (hr : IsClass r p) (hs : IsClass s p) : r = s := by
  have key : ∀ {a b : ℕ}, IsClass a p → IsClass b p → a ≤ b := by
    intro a b ha hb
    by_contra hc
    have hab : b ≤ a - 1 := by omega
    exact ha.2 (classLE_mono hab hb.1)
  exact le_antisymm (key hr hs) (key hs hr)

/-- Class 1 is exactly the page's first clause. -/
theorem isClass_one_iff {p : ℕ} :
    IsClass 1 p ↔ p.Prime ∧ ∀ q : ℕ, q.Prime → q ∣ p + 1 → q = 2 ∨ q = 3 := by
  constructor
  · rintro ⟨h, -⟩
    refine ⟨h.prime, fun q hq hd => ?_⟩
    rcases h.fac q hq hd with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (not_classLE_zero q h).elim
  · rintro ⟨hp, h⟩
    refine ⟨mkLE hp fun q hq hd => ?_, not_classLE_zero p⟩
    rcases h q hq hd with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem isClass_of_le {r q : ℕ} (hr : 1 ≤ r) (h : ClassLE r q) : ∃ m, 1 ≤ m ∧ m ≤ r ∧ IsClass m q := by
  classical
  have he : ∃ m, ClassLE m q := ⟨r, h⟩
  obtain ⟨m, hm, hc⟩ := exists_isClass h.prime
  refine ⟨m, hm, ?_, hc⟩
  by_contra hlt
  exact hc.2 (classLE_mono (by omega) h)

/-- Agreement with the page. Class `r + 1`, `r ≥ 1`, means: every prime factor of `p + 1` is of some
class at most `r`, one is of class exactly `r`, and `p` is of no class at most `r`. -/
theorem isClass_succ_iff {r p : ℕ} (hr : 1 ≤ r) :
    IsClass (r + 1) p ↔ p.Prime ∧
      (∀ q : ℕ, q.Prime → q ∣ p + 1 → ∃ m, 1 ≤ m ∧ m ≤ r ∧ IsClass m q) ∧
      (∃ q : ℕ, q.Prime ∧ q ∣ p + 1 ∧ IsClass r q) ∧ ¬ ClassLE r p := by
  constructor
  · rintro ⟨hL, hn⟩
    have hp := hL.prime
    have h := hL.fac
    simp only [Nat.add_sub_cancel] at hn
    refine ⟨hp, fun q hq hd => ?_, ?_, hn⟩
    · rcases h q hq hd with h' | h' | h'
      · exact isClass_of_le hr (classLE_of_two_or_three hr (Or.inl h'))
      · exact isClass_of_le hr (classLE_of_two_or_three hr (Or.inr h'))
      · exact isClass_of_le hr h'
    · by_contra hno
      apply hn
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      refine mkLE hp fun q hq hd => ?_
      rcases h q hq hd with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · by_cases hq2 : q = 2 ∨ q = 3
        · exact hq2.elim Or.inl (fun x => Or.inr (Or.inl x))
        · refine Or.inr (Or.inr ?_)
          by_contra hlow
          exact hno ⟨q, hq, hd, h', by simpa using hlow⟩
  · rintro ⟨hp, h1, -, hn⟩
    refine ⟨mkLE hp fun q hq hd => Or.inr (Or.inr ?_), by simpa using hn⟩
    obtain ⟨m, -, hm, hc⟩ := h1 q hq hd
    exact classLE_mono hm hc.1

/-- Descent: a prime of class `r + 1`, `r ≥ 1`, has a factor of class `r` at most half of `p + 1`. -/
theorem exists_factor_of_succ {r p : ℕ} (hr : 1 ≤ r) (h : IsClass (r + 1) p) :
    ∃ q, IsClass r q ∧ 2 * q ≤ p + 1 := by
  obtain ⟨hp, -, ⟨q, hq, hd, hc⟩, hn⟩ := (isClass_succ_iff hr).1 h
  refine ⟨q, hc, two_mul_le_of_dvd hp hq hd ?_⟩
  rintro rfl
  exact hn (classLE_mono hr classLE_one_two)

/-- If some prime has class `s`, then every class `1 ≤ t ≤ s` has one. -/
theorem exists_isClass_down {s t p : ℕ} (ht : 1 ≤ t) (hts : t ≤ s) (h : IsClass s p) :
    ∃ q, IsClass t q := by
  induction s, hts using Nat.le_induction generalizing p with
  | base => exact ⟨p, h⟩
  | succ s hs ih =>
    obtain ⟨q, hq, -⟩ := exists_factor_of_succ (by omega) h
    exact ih hq

/-- A prime `a` other than 2, 3 and class at least `r` forces class above `r` on `P` with
`a ∣ P + 1`. -/
theorem lt_class_of_dvd {a P r s : ℕ} (ha : a ≠ 2 ∧ a ≠ 3) (haq : a.Prime) (hd : a ∣ P + 1)
    (hc : ¬ ClassLE (r - 1) a) (hr : 1 ≤ r) (hP : ClassLE s P) : r < s := by
  by_contra hle
  have hs : ClassLE (r) P := classLE_mono (by omega) hP
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rcases hs.fac a haq hd with h | h | h
  · exact ha.1 h
  · exact ha.2 h
  · exact hc (by simpa using h)

/-- Dirichlet in Mathlib: for a prime `a` there are primes `P > n` with `a ∣ P + 1`. -/
theorem exists_prime_dvd_succ {a : ℕ} (ha : a.Prime) (n : ℕ) :
    ∃ P > n, P.Prime ∧ a ∣ P + 1 := by
  obtain ⟨P, h1, h2, h3⟩ := Nat.forall_exists_prime_gt_and_zmodEq n (q := a) (a := -1)
    ha.ne_zero ((IsCoprime.neg_left_iff (1 : ℤ) (a : ℤ)).2 isCoprime_one_left)
  refine ⟨P, h1, h2, ?_⟩
  have : (a : ℤ) ∣ (P : ℤ) + 1 := by
    have := h3.symm.dvd
    simpa [sub_neg_eq_add] using this
  exact_mod_cast this

theorem isClass_one_five : IsClass 1 5 := by
  refine isClass_one_iff.2 ⟨by norm_num, fun q hq hd => ?_⟩
  have h6 : q ∣ 2 * 3 := by simpa using hd
  rcases (Nat.Prime.dvd_mul hq).1 h6 with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h)

/-- For each `r ≥ 1` there is a prime of class `r` other than 2 and 3, and class `r + 1` is
nonempty. Every class is nonempty, the textbook `exists_p` of Formal Conjectures, unproved in that file.
Rests on Dirichlet in Mathlib. PROVED, KNOWN folklore. -/
theorem exists_isClass_ne {r : ℕ} (hr : 1 ≤ r) : ∃ a, IsClass r a ∧ a ≠ 2 ∧ a ≠ 3 := by
  induction r, hr using Nat.le_induction with
  | base => exact ⟨5, isClass_one_five, by norm_num, by norm_num⟩
  | succ r hr ih =>
    obtain ⟨a, hc, h2, h3⟩ := ih
    obtain ⟨P, -, hP, hd⟩ := exists_prime_dvd_succ hc.1.prime 0
    obtain ⟨s, hs1, hs⟩ := exists_isClass hP
    have hlt := lt_class_of_dvd ⟨h2, h3⟩ hc.1.prime hd hc.2 hr hs.1
    obtain ⟨q, hq⟩ := exists_isClass_down (t := r + 1) (by omega) (by omega) hs
    refine ⟨q, hq, ?_, ?_⟩
    · rintro rfl
      have := isClass_unique hq ⟨classLE_one_two, not_classLE_zero 2⟩
      omega
    · rintro rfl
      have := isClass_unique hq ⟨classLE_one_three, not_classLE_zero 3⟩
      omega

/-- Every class is nonempty, the vacuity instance for all three sealed Props of this section. -/
theorem exists_isClass_of_pos {r : ℕ} (hr : 1 ≤ r) : ∃ p, IsClass r p :=
  (exists_isClass_ne hr).imp fun _ h => h.1

/-- Infinitely many primes of class above `r`. This is the most Dirichlet gives; class exactly `r`
stays out of reach since `(P + 1) / a` is not controlled. PROVED, KNOWN folklore. -/
theorem infinite_class_gt (r : ℕ) (hr : 1 ≤ r) : {p | p.Prime ∧ ¬ ClassLE r p}.Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨B, hB⟩ => ?_
  obtain ⟨a, hc, h2, h3⟩ := exists_isClass_ne (r := r + 1) (by omega)
  obtain ⟨P, hgt, hP, hd⟩ := exists_prime_dvd_succ hc.1.prime B
  have : P ∈ {p | p.Prime ∧ ¬ ClassLE r p} := by
    refine ⟨hP, fun hle => ?_⟩
    have := lt_class_of_dvd (r := r + 1) ⟨h2, h3⟩ hc.1.prime hd hc.2 (by omega) hle
    omega
  have := hB this
  omega

/-- A prime of class `r ≥ 1` is at least `2^(r-1) + 1`. PROVED, elementary, OEIS A005113 comment as
quoted in OMOS-POOL11. So `p_r^(1/r)` has lower limit at least 2. -/
theorem two_pow_add_one_le {r p : ℕ} (hr : 1 ≤ r) (h : IsClass r p) : 2 ^ (r - 1) + 1 ≤ p := by
  induction r, hr using Nat.le_induction generalizing p with
  | base => simpa using h.1.prime.two_le
  | succ r hr ih =>
    obtain ⟨q, hq, hle⟩ := exists_factor_of_succ hr h
    have := ih hq
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at this ⊢
    rw [pow_succ]
    omega

theorem two_pow_add_one_le_leastPrime {r : ℕ} (hr : 1 ≤ r) : 2 ^ (r - 1) + 1 ≤ leastPrime r :=
  two_pow_add_one_le hr (Nat.sInf_mem (exists_isClass_of_pos hr))

/-- `leastPrime` is itself of class `r`. -/
theorem isClass_leastPrime {r : ℕ} (hr : 1 ≤ r) : IsClass r (leastPrime r) :=
  Nat.sInf_mem (exists_isClass_of_pos hr)

/-- The step behind the bound: `p_(r+1) ≥ 2 p_r - 1`, `r ≥ 1`. PROVED, elementary. -/
theorem two_mul_leastPrime_le {r : ℕ} (hr : 1 ≤ r) :
    2 * leastPrime r ≤ leastPrime (r + 1) + 1 := by
  obtain ⟨q, hq, hle⟩ := exists_factor_of_succ hr (isClass_leastPrime (r := r + 1) (by omega))
  have : leastPrime r ≤ q := Nat.sInf_le hq
  omega

theorem factor_two_mul {q n : ℕ} (hq : q.Prime) (hn : n.Prime) (hd : q ∣ 2 * n) : q = 2 ∨ q = n := by
  rcases (Nat.Prime.dvd_mul hq).1 hd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq hn).1 h)

theorem classLE_one_seven : ClassLE 1 7 := by
  refine mkLE (by norm_num) fun q hq hd => Or.inl ?_
  have h : q ∣ 2 ^ 3 := by simpa using hd
  exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h)

/-- Table check, the printed `2, 13, 37, 73, 1021` are of the stated classes. Leastness for the
first terms is checked in out/U-1616/scripts/cls.c only, to class 13. -/
theorem isClass_two_13 : IsClass 2 13 := by
  refine ⟨mkLE (by norm_num) fun q hq hd => ?_, fun h => ?_⟩
  · rcases factor_two_mul hq (n := 7) (by norm_num) (by simpa using hd) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr classLE_one_seven)
  · have h' : ClassLE 1 13 := by simpa using h
    rcases h'.fac 7 (by norm_num) (by norm_num) with h | h | h
    · omega
    · omega
    · exact h

theorem classLE_two_19 : ClassLE 2 19 := by
  refine mkLE (by norm_num) fun q hq hd => ?_
  have h : q ∣ 2 ^ 2 * 5 := by simpa using hd
  rcases (Nat.Prime.dvd_mul hq).1 h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  · have := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h
    subst this
    exact Or.inr (Or.inr isClass_one_five.1)

theorem not_classLE_one_19 : ¬ ClassLE 1 19 := fun h => by
  rcases h.fac 5 (by norm_num) (by norm_num) with h | h | h
  · omega
  · omega
  · exact h

theorem isClass_three_37 : IsClass 3 37 := by
  refine ⟨mkLE (by norm_num) fun q hq hd => ?_, fun h => ?_⟩
  · rcases factor_two_mul hq (n := 19) (by norm_num) (by simpa using hd) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr classLE_two_19)
  · have h' : ClassLE 2 37 := by simpa using h
    rcases h'.fac 19 (by norm_num) (by norm_num) with h | h | h
    · omega
    · omega
    · exact not_classLE_one_19 h

theorem isClass_four_73 : IsClass 4 73 := by
  refine ⟨mkLE (by norm_num) fun q hq hd => ?_, fun h => ?_⟩
  · rcases factor_two_mul hq (n := 37) (by norm_num) (by simpa using hd) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr isClass_three_37.1)
  · have h' : ClassLE 3 73 := by simpa using h
    rcases h'.fac 37 (by norm_num) (by norm_num) with h | h | h
    · omega
    · omega
    · exact isClass_three_37.2 (by simpa using h)

/-! #### The literal wording -/

/-- The page wording taken literally: no `no lower class` clause. -/
def Lit : ℕ → ℕ → Prop
  | 0, _ => False
  | 1, p => p.Prime ∧ ∀ q : ℕ, q.Prime → q ∣ p + 1 → q = 2 ∨ q = 3
  | r + 2, p => p.Prime ∧
      (∀ q : ℕ, q.Prime → q ∣ p + 1 → ∃ m, ∃ _ : m < r + 2, 1 ≤ m ∧ Lit m q) ∧
      ∃ q : ℕ, q.Prime ∧ q ∣ p + 1 ∧ Lit (r + 1) q
termination_by r _ => r
decreasing_by all_goals omega

/-- Literal class `r` is exactly class at most `r`, for `r ≥ 1`, so literal classes are nested. -/
theorem lit_iff {r p : ℕ} (hr : 1 ≤ r) : Lit r p ↔ ClassLE r p := by
  induction r using Nat.strong_induction_on generalizing p with
  | _ r ih =>
    obtain _ | _ | r := r
    · omega
    · rw [Lit]
      constructor
      · rintro ⟨hp, h⟩
        exact mkLE hp fun q hq hd => (h q hq hd).elim Or.inl (fun x => Or.inr (Or.inl x))
      · intro h
        refine ⟨h.prime, fun q hq hd => ?_⟩
        rcases h.fac q hq hd with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact (not_classLE_zero q h).elim
    · rw [Lit]
      constructor
      · rintro ⟨hp, h, -⟩
        refine mkLE hp fun q hq hd => Or.inr (Or.inr ?_)
        obtain ⟨m, hm, h1, hl⟩ := h q hq hd
        exact classLE_mono (by omega) ((ih m hm h1).1 hl)
      · intro h
        have hle : ∀ q, q.Prime → q ∣ p + 1 → ClassLE (r + 1) q := by
          intro q hq hd
          rcases h.fac q hq hd with h' | h' | h'
          · exact classLE_of_two_or_three (by omega) (Or.inl h')
          · exact classLE_of_two_or_three (by omega) (Or.inr h')
          · exact h'
        refine ⟨h.prime, fun q hq hd => ⟨r + 1, by omega, by omega,
          (ih (r + 1) (by omega) (by omega)).2 (hle q hq hd)⟩, ?_⟩
        obtain ⟨q, hq, hd⟩ := Nat.exists_prime_and_dvd (n := p + 1) (by have := h.prime.two_le; omega)
        exact ⟨q, hq, hd, (ih (r + 1) (by omega) (by omega)).2 (hle q hq hd)⟩

/-- Defect, literal reading: 2 is in every class, so the least prime of each class is 2 and the
growth question is empty. PROVED. Matches OMOS-POOL11 and the Formal Conjectures docstring. -/
theorem lit_two {r : ℕ} (hr : 1 ≤ r) : Lit r 2 :=
  (lit_iff hr).2 (classLE_mono hr classLE_one_two)

/-- Defect, literal reading: the question is only class 1, primes `2^a 3^b - 1`. PROVED. -/
theorem lit_statement_iff :
    (∀ r, 1 ≤ r → {p | Lit r p}.Infinite) ↔ {p | IsClass 1 p}.Infinite := by
  have h1 : {p | Lit 1 p} = {p | IsClass 1 p} := by
    ext p
    simp only [Set.mem_setOf_eq, lit_iff le_rfl]
    exact ⟨fun h => ⟨h, not_classLE_zero p⟩, fun h => h.1⟩
  constructor
  · intro h
    rw [← h1]
    exact h 1 le_rfl
  · intro h r hr
    refine h.mono fun p hp => (lit_iff hr).2 (classLE_mono hr hp.1)

/-- The sealed statement implies the literal one. -/
theorem lit_of_statement (h : Erdos1055Statement) : ∀ r, 1 ≤ r → {p | Lit r p}.Infinite :=
  lit_statement_iff.2 (h 1 le_rfl)

/-- The two guesses exclude each other once stated, so the pair is not vacuous on one side. -/
theorem not_limit_and_bounded : ¬ (Erdos1055Limit ∧ Selfridge1055Bounded) := by
  rintro ⟨h1, M, hM⟩
  obtain ⟨r, hr⟩ := ((h1.eventually_gt_atTop M).and (eventually_ge_atTop 1)).exists
  exact absurd (hM r hr.2) (not_le.2 hr.1)

/-! ### 3. Erdős 852, runs of distinct prime gaps -/

/-- The prime gap `d_n = p_(n+1) - p_n`, indexed from `n = 0`, so `gap 0 = 1`. -/
noncomputable def gap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- The gaps `d_n, ..., d_(n+H-1)` are all distinct. As `DistinctGapRun` in Formal Conjectures. -/
def DistinctRun (n H : ℕ) : Prop := Set.InjOn gap (Set.Ico n (n + H))

/-- **OPEN on the page, sealed.** Plain math: with `h(x)` the largest `H` such that for some `n < x`
the gaps `d_n, ..., d_(n+H-1)` are distinct, `h(x) > (log x)^c` for some `c > 0` and all large `x`.
Source: Erdős problem 852, erdosproblems.com/852, read 2026-11-04, status open, the page reports
claims of partial results in comments; Erdős, LNM 1122, 1985, pp. 79-80, not read here. Same as
`erdos_852.parts.i`. OMOS-POOL9 reports unrefereed notes giving `c < 1/3`, not checked here, so this
one may fall. Vacuity `distinctRun_zero_two`, `exists_distinctRun_15`. -/
def Erdos852PartOne : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ X : ℝ, ∀ x, X ≤ x → ∃ n H : ℕ, (n : ℝ) < x ∧ Real.log x ^ c < H ∧ DistinctRun n H

/-- **OPEN, sealed.** Plain math: `h(x) = o(log x)`. Same source as `Erdos852PartOne`, same as
`erdos_852.parts.ii`. Vacuity `distinctRun_zero_two`, and `not_distinctRun_zero_three` shows the
hypothesis of the implication can fail. -/
def Erdos852PartTwo : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x, X ≤ x → ∀ n H : ℕ, (n : ℝ) < x → DistinctRun n H →
    (H : ℝ) ≤ ε * Real.log x

theorem nth_lt_succ (n : ℕ) : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self n)

/-- Gaps are positive and, away from `n = 0`, even and at least 2. -/
theorem gap_cases (n : ℕ) : (n = 0 ∧ gap n = 1) ∨ (2 ∣ gap n ∧ 2 ≤ gap n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · left
    refine ⟨rfl, ?_⟩
    simp [gap, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  · right
    have hlt := nth_lt_succ n
    have h0 : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime n :=
      Nat.nth_strictMono Nat.infinite_setOfPred_prime hn
    rw [Nat.nth_prime_zero_eq_two] at h0
    have ho : Odd (Nat.nth Nat.Prime n) :=
      (Nat.prime_nth_prime n).odd_of_ne_two (by omega)
    have ho' : Odd (Nat.nth Nat.Prime (n + 1)) :=
      (Nat.prime_nth_prime (n + 1)).odd_of_ne_two (by omega)
    obtain ⟨a, ha⟩ := ho
    obtain ⟨b, hb⟩ := ho'
    unfold gap
    rw [ha, hb] at hlt ⊢
    constructor
    · exact ⟨b - a, by omega⟩
    · omega

/-- `H` distinct naturals sum to at least `0 + 1 + ... + (H - 1)`. -/
theorem sum_range_le_sum_finset (s : Finset ℕ) : ∑ i ∈ Finset.range s.card, i ≤ ∑ x ∈ s, x := by
  induction h : s.card generalizing s with
  | zero => simp
  | succ H ih =>
    have hne : s.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨m, hm, hmax⟩ : ∃ m ∈ s, ∀ x ∈ s, x ≤ m :=
      ⟨s.max' hne, Finset.max'_mem s hne, fun x hx => Finset.le_max' s x hx⟩
    have hsub : s ⊆ Finset.range (m + 1) := fun x hx =>
      Finset.mem_range.2 (Nat.lt_succ_of_le (hmax x hx))
    have hc := Finset.card_le_card hsub
    rw [Finset.card_range] at hc
    have e : m + ∑ x ∈ s.erase m, x = ∑ x ∈ s, x := Finset.add_sum_erase s (fun x => x) hm
    rw [Finset.sum_range_succ]
    have := ih (s.erase m) (by rw [Finset.card_erase_of_mem hm]; omega)
    omega

theorem sum_gap (n H : ℕ) :
    ∑ j ∈ Finset.range H, gap (n + j) = Nat.nth Nat.Prime (n + H) - Nat.nth Nat.Prime n := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime (n + H) :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (by omega)
    have h2 := nth_lt_succ (n + H)
    unfold gap
    rw [← add_assoc]
    omega

/-- A distinct run of length `H` spans at least `H (H - 1)`. PROVED, elementary. The form in
OMOS-POOL9, `H * H - H + 1 ≤ ...`, fails at `H = 0`, where the run is empty; this form holds for all
`H`. It gives the elementary bound `h(x) ≪ x^(1/2 + o(1))` once paired with a prime upper bound. -/
theorem run_span {n H : ℕ} (h : DistinctRun n H) :
    H * (H - 1) ≤ Nat.nth Nat.Prime (n + H) - Nat.nth Nat.Prime n := by
  classical
  set φ : ℕ → ℕ := fun k => gap k / 2 with hφ
  have hinj : Set.InjOn φ (Finset.Ico n (n + H) : Set ℕ) := by
    intro k hk l hl e
    have hk' : k ∈ Set.Ico n (n + H) := by simpa using hk
    have hl' : l ∈ Set.Ico n (n + H) := by simpa using hl
    simp only [hφ] at e
    rcases gap_cases k with ⟨rfl, h1⟩ | ⟨h1, h2⟩ <;> rcases gap_cases l with ⟨rfl, h3⟩ | ⟨h3, h4⟩
    · rfl
    · omega
    · omega
    · exact h hk' hl' (by omega)
  have hcard : ((Finset.Ico n (n + H)).image φ).card = H := by
    rw [Finset.card_image_of_injOn hinj]
    simp
  have h1 := sum_range_le_sum_finset ((Finset.Ico n (n + H)).image φ)
  rw [hcard, Finset.sum_image hinj] at h1
  have h2 : 2 * ∑ k ∈ Finset.Ico n (n + H), φ k ≤ ∑ k ∈ Finset.Ico n (n + H), gap k := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by simp only [hφ]; omega
  have h3 : ∑ k ∈ Finset.Ico n (n + H), gap k = ∑ j ∈ Finset.range H, gap (n + j) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp
  rw [h3, sum_gap] at h2
  have h4 := Finset.sum_range_id_mul_two H
  omega

/-- If `a < b` are consecutive primes and `a` is the `k`th prime, `b` is the next one. -/
theorem nth_succ_of_consec {k a b : ℕ} (ha : Nat.nth Nat.Prime k = a) (hab : a < b) (hb : b.Prime)
    (hno : ∀ m, a < m → m < b → ¬ m.Prime) : Nat.nth Nat.Prime (k + 1) = b := by
  have ht := Nat.nth_count hb
  set t := Nat.count Nat.Prime b
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hkt : k < t := hmono.lt_iff_lt.1 (by rw [ha, ht]; exact hab)
  rcases Nat.lt_or_ge (k + 1) t with h | h
  · exfalso
    have h1 : Nat.nth Nat.Prime (k + 1) < b := by rw [← ht]; exact hmono h
    have h2 : a < Nat.nth Nat.Prime (k + 1) := by rw [← ha]; exact hmono (Nat.lt_succ_self k)
    exact hno _ h2 h1 (Nat.prime_nth_prime _)
  · have : t = k + 1 := by omega
    rw [← this, ht]

/-- Checks that a list is a run of consecutive primes after its head. Primes up to `250000`. -/
def chk : List ℕ → Bool
  | a :: b :: t => decide (a < b) && primeB 500 b &&
      (List.range (b - a - 1)).all (fun i => !primeB 500 (a + 1 + i)) && decide (b < 250000) &&
      decide (a < 250000) && chk (b :: t)
  | _ => true

theorem chk_nth : ∀ (L : List ℕ) (k a : ℕ), Nat.nth Nat.Prime k = a → chk (a :: L) = true →
    ∀ i, i ≤ L.length → Nat.nth Nat.Prime (k + i) = (a :: L).getD i 0 := by
  intro L
  induction L with
  | nil =>
    intro k a ha _ i hi
    obtain rfl : i = 0 := by simpa using hi
    simpa using ha
  | cons b t ih =>
    intro k a ha hc i hi
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
    have hb : b.Prime := (primeB_iff (by omega)).1 h2
    have hno : ∀ m, a < m → m < b → ¬ m.Prime := by
      intro m h7 h8 hm
      have := h3 (m - a - 1) (by omega)
      have e : a + 1 + (m - a - 1) = m := by omega
      rw [e] at this
      have hm' := (primeB_iff (B := 500) (n := m) (by omega)).2 hm
      simp [hm'] at this
    have hnext := nth_succ_of_consec ha h1 hb hno
    rcases i with _ | i
    · simpa using ha
    · have := ih (k + 1) b hnext h6 i (by simpa using hi)
      rw [show k + (i + 1) = k + 1 + i by ring, this]
      simp

/-- The first run of length 15, from the prime 214867, as reproduced in out/U-1616/big.out. -/
def run15 : List ℕ :=
  [214867, 214883, 214891, 214913, 214939, 214943, 214967, 214987, 214993, 215051, 215063, 215077,
    215087, 215123, 215141, 215143]

/-- The gap values of a list. -/
def diffAt (L : List ℕ) (i : ℕ) : ℕ := L.getD (i + 1) 0 - L.getD i 0

theorem gap_of_chk {a : ℕ} {L : List ℕ} {k : ℕ} (ha : Nat.nth Nat.Prime k = a)
    (hc : chk (a :: L) = true) {i : ℕ} (hi : i + 1 ≤ L.length) :
    gap (k + i) = diffAt (a :: L) i := by
  unfold gap diffAt
  rw [show k + i + 1 = k + (i + 1) by ring, chk_nth L k a ha hc _ hi,
    chk_nth L k a ha hc i (by omega)]

/-- Sanity: a distinct run of length 15 exists. Table check for OMOS-POOL9. PROVED, KNOWN. -/
theorem exists_distinctRun_15 : ∃ s, DistinctRun s 15 := by
  have hp : Nat.Prime 214867 := (primeB_iff (B := 500) (by norm_num)).1 (by decide +kernel)
  have hc : chk run15 = true := by decide +kernel
  have hk := Nat.nth_count hp
  refine ⟨Nat.count Nat.Prime 214867, ?_⟩
  set s := Nat.count Nat.Prime 214867
  have hg : ∀ i, i < 15 → gap (s + i) = diffAt run15 i := fun i hi =>
    gap_of_chk hk hc (by show i + 1 ≤ 15; omega)
  have hd : ∀ i, i < 15 → ∀ j, j < 15 → diffAt run15 i = diffAt run15 j → i = j := by decide +kernel
  intro x hx y hy e
  simp only [Set.mem_Ico] at hx hy
  have hxg := hg (x - s) (by omega)
  have hyg := hg (y - s) (by omega)
  rw [show s + (x - s) = x by omega] at hxg
  rw [show s + (y - s) = y by omega] at hyg
  have := hd (x - s) (by omega) (y - s) (by omega) (by rw [← hxg, ← hyg]; exact e)
  omega

/-- Vacuity: `d_0 = 1, d_1 = 2` are distinct. -/
theorem distinctRun_zero_two : DistinctRun 0 2 := by
  have hc : chk [2, 3, 5] = true := by decide +kernel
  have hk := Nat.nth_prime_zero_eq_two
  have h0 := gap_of_chk (i := 0) hk hc (by simp)
  have h1 := gap_of_chk (i := 1) hk hc (by simp)
  intro x hx y hy e
  simp only [Set.mem_Ico] at hx hy
  have hx' : x = 0 ∨ x = 1 := by omega
  have hy' : y = 0 ∨ y = 1 := by omega
  simp only [zero_add] at h0 h1
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;> first
    | rfl
    | (exfalso; rw [h0, h1] at e; revert e; decide)

/-- `d_1 = d_2 = 2`, so the run from 0 stops at length 2. -/
theorem not_distinctRun_zero_three : ¬ DistinctRun 0 3 := by
  intro h
  have hc : chk [2, 3, 5, 7] = true := by decide +kernel
  have hk := Nat.nth_prime_zero_eq_two
  have h1 := gap_of_chk (i := 1) hk hc (by simp)
  have h2 := gap_of_chk (i := 2) hk hc (by simp)
  simp only [zero_add] at h1 h2
  have := @h 1 (by simp) 2 (by simp) (by rw [h1, h2]; decide)
  omega

/-! ### 4. Erdős 238, long runs of consecutive primes with large gaps -/

/-- **OPEN, sealed.** Plain math: for all `c₁, c₂ > 0` and all large `x` there are more than
`c₁ log x` consecutive primes at most `x` with the difference of any two above `c₂`. Source: Erdős
problem 238, erdosproblems.com/238, read 2026-11-04, page edit 13 January 2026, status open, no
proof claims. Same as `erdos_238`, adjacent gaps there and here, see `pairwise_of_adjacent`. The
page says Erdős 1949 has small `c₁` depending on `c₁`, a slip for `c₂`, as the Formal Conjectures
variant has it. FILED, NO OUTREACH. Only `c₂ ≥ 2` has content, see `gap_gt_of_lt_two`. Vacuity
`exists_run_31`. -/
def Erdos238Statement : Prop :=
  ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ → ∃ X : ℝ, ∀ x, X ≤ x → ∃ k m : ℕ, c₁ * Real.log x < k ∧
    (∀ i, i < k → (Nat.nth Nat.Prime (m + i) : ℝ) ≤ x) ∧
    ∀ i, i + 1 < k → c₂ < (gap (m + i) : ℝ)

/-- Adjacent gaps above `c`, `c ≥ 0`, give all differences above `c`. PROVED, elementary. -/
theorem pairwise_of_adjacent {m k : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, i + 1 < k → c < (gap (m + i) : ℝ)) {i j : ℕ} (hij : i < j) (hj : j < k) :
    c < (Nat.nth Nat.Prime (m + j) : ℝ) - Nat.nth Nat.Prime (m + i) := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - i - 1, by omega⟩
  clear hij
  induction d with
  | zero =>
    have h1 := h i (by omega)
    have h2 := nth_lt_succ (m + i)
    unfold gap at h1
    rw [Nat.cast_sub h2.le] at h1
    have e : m + (i + 1 + 0) = m + i + 1 := by ring
    rw [e]
    exact h1
  | succ d ih =>
    have h1 := h (i + 1 + d) (by omega)
    have h2 := nth_lt_succ (m + (i + 1 + d))
    have h3 := ih (by omega)
    unfold gap at h1
    rw [Nat.cast_sub h2.le] at h1
    have e : m + (i + 1 + (d + 1)) = m + (i + 1 + d) + 1 := by ring
    rw [e]
    linarith

/-- For `c₂ < 2` every gap from index 1 on qualifies, so only `c₂ ≥ 2` has content. PROVED. -/
theorem gap_gt_of_lt_two {c : ℝ} (hc : c < 2) {n : ℕ} (hn : 1 ≤ n) : c < (gap n : ℝ) := by
  rcases gap_cases n with ⟨rfl, -⟩ | ⟨-, h⟩
  · omega
  · have : (2 : ℝ) ≤ gap n := by exact_mod_cast h
    linarith

/-- Vacuity: 31, 37, 41 are consecutive primes with both gaps above 2. -/
theorem exists_run_31 : ∃ m, (∀ i, i < 3 → Nat.nth Nat.Prime (m + i) ≤ 41) ∧
    ∀ i, i + 1 < 3 → 2 < gap (m + i) := by
  have hp : Nat.Prime 31 := by norm_num
  have hc : chk [31, 37, 41] = true := by decide +kernel
  have hk := Nat.nth_count hp
  refine ⟨Nat.count Nat.Prime 31, ?_, ?_⟩
  · intro i hi
    have := chk_nth [37, 41] _ 31 hk hc i (by show i ≤ 2; omega)
    rw [this]
    interval_cases i <;> decide
  · intro i hi
    have hi' : i < 2 := by omega
    rw [gap_of_chk hk hc (by show i + 1 ≤ 2; omega)]
    interval_cases i <;> decide

end LeanLab.OpenProblems.State1616

#print axioms LeanLab.OpenProblems.State1616.grechuk_not_mem
#print axioms LeanLab.OpenProblems.State1616.mem_iff
#print axioms LeanLab.OpenProblems.State1616.not_tail_one
#print axioms LeanLab.OpenProblems.State1616.not_statement_of_one_excluded
#print axioms LeanLab.OpenProblems.State1616.not_mem_three_of_erdos9
#print axioms LeanLab.OpenProblems.State1616.isClass_succ_iff
#print axioms LeanLab.OpenProblems.State1616.exists_isClass_of_pos
#print axioms LeanLab.OpenProblems.State1616.infinite_class_gt
#print axioms LeanLab.OpenProblems.State1616.two_pow_add_one_le_leastPrime
#print axioms LeanLab.OpenProblems.State1616.two_mul_leastPrime_le
#print axioms LeanLab.OpenProblems.State1616.isClass_four_73
#print axioms LeanLab.OpenProblems.State1616.lit_two
#print axioms LeanLab.OpenProblems.State1616.lit_statement_iff
#print axioms LeanLab.OpenProblems.State1616.not_limit_and_bounded
#print axioms LeanLab.OpenProblems.State1616.run_span
#print axioms LeanLab.OpenProblems.State1616.exists_distinctRun_15
#print axioms LeanLab.OpenProblems.State1616.distinctRun_zero_two
#print axioms LeanLab.OpenProblems.State1616.not_distinctRun_zero_three
#print axioms LeanLab.OpenProblems.State1616.pairwise_of_adjacent
#print axioms LeanLab.OpenProblems.State1616.exists_run_31
