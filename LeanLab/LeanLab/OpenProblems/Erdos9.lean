import Mathlib

/-!
# Erdős Problem 9, OPEN, sealed statement and closable sub-claims

Unit U-1603, 2026-11-02. AI wrote the Lean code. An OPEN problem, a target for the network, no
claim of progress on it.

Plain math: let `A` be the set of odd integers not of the form `p + 2^k + 2^l` with `p` prime and
`k, l ≥ 0`. Is the upper density of `A` positive?

Source: T. F. Bloom, Erdős Problem #9, https://www.erdosproblems.com/9, fetched 2026-11-02, page
status OPEN, footer latest edit 28 September 2025, while /history/9 read 2026-11-05 has a newest
entry of 7 April 2026, marked as not resolvable by a finite computation.
Also Guy, Unsolved Problems in Number Theory, A19.

Definition reused from google-deepmind/formal-conjectures, file
`FormalConjectures/ErdosProblems/9.lean`, `Erdos9.Erdos9A`, Copyright 2025 The Formal Conjectures
Authors, Apache-2.0, fetched 2026-11-02. `Erdos9A` below is that definition word for word. FC states
`erdos_9 : 0 < Erdos9A.upperDensity` with its own `upperDensity`, which is not in Mathlib, so
`PosUpperDensity` restates positivity with no limsup. That restatement is not machine checked
against FC here, since FC is not a dependency of this project.

Status of the sub-claims: all KNOWN, none ORIGINAL. `mem_1117175145` is an instance of OEIS A156695
data. Formal Conjectures proves only `1, 3 ∈ Erdos9A` and `5 ∉ Erdos9A` in its own file, so the
Lean theorem here is a formal instance beyond those, not new mathematics.
-/

namespace LeanLab.OpenProblems.Erdos9

/-- Word for word `Erdos9.Erdos9A` of formal-conjectures, Apache-2.0. Odd numbers that are not a
prime plus two powers of 2, exponents allowed to be 0. -/
def Erdos9A : Set ℕ := { n | Odd n ∧ ¬ ∃ (p k l : ℕ), (Nat.Prime p) ∧ n = p + 2 ^ k + 2 ^ l }

/-- Positive upper density, with no limsup: `|A ∩ [0, N]| ≥ c N` for arbitrarily large `N`. -/
def PosUpperDensity (A : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N₀ : ℕ, ∃ N ≥ N₀, c * N ≤ ((A ∩ Set.Iic N).ncard : ℝ)

/-- **Erdős 9, OPEN, sealed.** The upper density of `Erdos9A` is positive. A proof or a disproof
of this Prop is new knowledge. -/
def Erdos9Statement : Prop := PosUpperDensity Erdos9A

/-! ### Vacuity: the density predicate separates sets, and `Erdos9A` is a proper nonempty set -/

theorem posUpperDensity_univ : PosUpperDensity Set.univ := by
  refine ⟨1, one_pos, fun N₀ => ⟨N₀, le_rfl, ?_⟩⟩
  have : ((Set.univ ∩ Set.Iic N₀ : Set ℕ).ncard : ℝ) = N₀ + 1 := by
    rw [Set.univ_inter, Set.ncard_eq_toFinset_card']
    simp
  rw [this]
  linarith

theorem not_posUpperDensity_empty : ¬ PosUpperDensity ∅ := by
  rintro ⟨c, hc, h⟩
  obtain ⟨N, hN, hle⟩ := h 1
  simp only [Set.empty_inter, Set.ncard_empty, Nat.cast_zero] at hle
  have : (0 : ℝ) < c * N := mul_pos hc (by exact_mod_cast hN)
  linarith

theorem one_mem : 1 ∈ Erdos9A := by
  refine ⟨by decide, ?_⟩
  rintro ⟨p, k, l, hp, h⟩
  have := hp.two_le
  have := Nat.one_le_two_pow (n := k)
  have := Nat.one_le_two_pow (n := l)
  omega

theorem three_mem : 3 ∈ Erdos9A := by
  refine ⟨by decide, ?_⟩
  rintro ⟨p, k, l, hp, h⟩
  have := hp.two_le
  have := Nat.one_le_two_pow (n := k)
  have := Nat.one_le_two_pow (n := l)
  omega

theorem five_not_mem : 5 ∉ Erdos9A := fun h =>
  h.2 ⟨3, 0, 0, Nat.prime_three, by norm_num⟩

/-! ### The certificate for `1117175145` -/

/-- A factor of `m` strictly between 1 and `m`, by trial division up to 19391, the largest least
prime factor that occurs in the certificate. -/
def hasFac (m : ℕ) : Bool :=
  (List.range 19392).any fun d => decide (2 ≤ d) && decide (d < m) && decide (m % d = 0)

theorem not_prime_of_hasFac {m : ℕ} (h : hasFac m = true) : ¬ m.Prime := by
  simp only [hasFac, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨d, -, ⟨h2, hlt⟩, h0⟩ := h
  intro hp
  rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h0) with h1 | h1 <;> omega

/-- The decidable statement: every `n - 2^k - 2^l` with `k, l ≤ 30` is below 2 or has a factor. -/
def checkAll (n : ℕ) : Bool :=
  (List.range 31).all fun k => (List.range 31).all fun l =>
    decide (n < 2 ^ k + 2 ^ l + 2) || hasFac (n - 2 ^ k - 2 ^ l)

theorem checkAll_1117175145 : checkAll 1117175145 = true := by decide +kernel

/-- If `n < 2^31` is odd and passes `checkAll`, then `n` is in `Erdos9A`. -/
theorem mem_of_checkAll {n : ℕ} (hodd : Odd n) (hn : n < 2 ^ 31) (hc : checkAll n = true) :
    n ∈ Erdos9A := by
  refine ⟨hodd, ?_⟩
  rintro ⟨p, k, l, hp, h⟩
  have hp2 := hp.two_le
  have hk : k < 31 := by
    by_contra hc'
    have : 2 ^ 31 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hc')
    have := Nat.one_le_two_pow (n := l)
    omega
  have hl : l < 31 := by
    by_contra hc'
    have : 2 ^ 31 ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hc')
    have := Nat.one_le_two_pow (n := k)
    omega
  simp only [checkAll, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hc
  rcases hc k hk l hl with h1 | h1
  · omega
  · have hm : n - 2 ^ k - 2 ^ l = p := by omega
    rw [hm] at h1
    exact not_prime_of_hasFac h1 hp

/-- **Closable sub-claim, PROVED, KNOWN.** `1117175145` is odd and not a prime plus two powers of
2. It is the third term above 5 of OEIS A156695, and the first of those still excluded once
exponent 0 is allowed, since the two smaller terms minus 2 are prime. It is one less than Grechuk's
even example in Erdős 10. Instance of known data. -/
theorem mem_1117175145 : 1117175145 ∈ Erdos9A :=
  mem_of_checkAll (by decide) (by norm_num) checkAll_1117175145

/-- `Erdos9A` is a proper subset of the odd numbers with a member above 3. -/
theorem vacuity : (1117175145 : ℕ) ∈ Erdos9A ∧ 5 ∉ Erdos9A ∧ Odd 5 :=
  ⟨mem_1117175145, five_not_mem, by decide⟩

/-! ### Bridge to the lab's Romanov line -/

/-- A member of `Erdos9A` is not `p + 2^j` with `j ≥ 1`, since `2^j = 2^(j-1) + 2^(j-1)`. So
`Erdos9A` lies in the odd numbers left out by the lab's `Romanov` theorem, and that theorem bounds
its density away from all odd numbers. Elementary, KNOWN. -/
theorem not_polignac_of_mem {n : ℕ} (hn : n ∈ Erdos9A) (p j : ℕ) (hp : p.Prime) :
    n ≠ p + 2 ^ (j + 1) := by
  intro h
  exact hn.2 ⟨p, j, j, hp, by rw [h, pow_succ]; ring⟩

end LeanLab.OpenProblems.Erdos9

#print axioms LeanLab.OpenProblems.Erdos9.mem_1117175145
#print axioms LeanLab.OpenProblems.Erdos9.vacuity
#print axioms LeanLab.OpenProblems.Erdos9.posUpperDensity_univ
#print axioms LeanLab.OpenProblems.Erdos9.not_posUpperDensity_empty
#print axioms LeanLab.OpenProblems.Erdos9.not_polignac_of_mem
