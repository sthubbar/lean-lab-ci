import Mathlib

/-!
# R-0007, the parity barrier made exact on rough numbers

T3 MOONSHOT route, unit U-1033. AI wrote this Lean code. KNOWN mathematics, Selberg's parity
example in its simplest form.

Call `n` `N`-rough when every prime factor `p` of `n` has `p³ > N`. For `1 < n ≤ N` rough,
`n` has at most two prime factors with multiplicity, so `n` is prime exactly when `Ω(n)` is odd,
that is when `λ(n) = -1`. Hence for even `N`, with `a + b = N` and `a, b` rough,
`r(N) = Σ (1 - λ(a))(1 - λ(b))/4`: binary Goldbach for `N` is a sign statement about the
Liouville correlation `Σ λ(a)λ(b)` over rough pairs. A sieve of level `D` sees only the counts
of rough numbers in progressions `d ≤ D`, the same for `Ω` odd and `Ω` even up to small error;
this is Selberg's parity barrier, and the identity shows where it bites.
-/

namespace LeanLab.Routes.R0007

/-- every prime factor `p` of `n` has `N < p³` -/
def Rough (N n : ℕ) : Prop := ∀ p ∈ n.primeFactorsList, N < p ^ 3

/-- a rough `n ≤ N` has at most two prime factors with multiplicity -/
theorem length_le_two {N n : ℕ} (hn : 1 < n) (hnN : n ≤ N) (hr : Rough N n) :
    n.primeFactorsList.length ≤ 2 := by
  by_contra h
  push Not at h
  have hn0 : n ≠ 0 := by omega
  have hmem : n.minFac ∈ n.primeFactorsList :=
    Nat.mem_primeFactorsList_iff_dvd hn0 (Nat.minFac_prime (by omega)) |>.mpr (Nat.minFac_dvd n)
  have hlow : ∀ x ∈ n.primeFactorsList, n.minFac ≤ x := by
    intro x hx
    exact Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactorsList hx).two_le
      (Nat.dvd_of_mem_primeFactorsList hx)
  have h1 := List.pow_card_le_prod n.primeFactorsList n.minFac hlow
  rw [Nat.prod_primeFactorsList hn0] at h1
  have hm1 : 1 ≤ n.minFac := (Nat.minFac_prime (by omega)).one_lt.le
  have h3 : n.minFac ^ 3 ≤ n.minFac ^ n.primeFactorsList.length :=
    Nat.pow_le_pow_right hm1 h
  have := hr _ hmem
  omega

/-- **On rough numbers, prime means `Ω` odd.** PROVED. -/
theorem prime_iff_odd_card {N n : ℕ} (hn : 1 < n) (hnN : n ≤ N) (hr : Rough N n) :
    n.Prime ↔ Odd n.primeFactorsList.length := by
  have h2 := length_le_two hn hnN hr
  have hn0 : n ≠ 0 := by omega
  have hpos : 0 < n.primeFactorsList.length := by
    rcases Nat.eq_zero_or_pos n.primeFactorsList.length with h | h
    · have : n.primeFactorsList = [] := List.length_eq_zero_iff.mp h
      rw [Nat.primeFactorsList_eq_nil] at this; omega
    · exact h
  constructor
  · intro hp; rw [Nat.primeFactorsList_prime hp]; exact ⟨0, rfl⟩
  · intro hodd
    have hlen : n.primeFactorsList.length = 1 := by
      rcases hodd with ⟨k, hk⟩; omega
    obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hlen
    have := Nat.prod_primeFactorsList hn0
    rw [hp, List.prod_singleton] at this
    have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList (by rw [hp]; simp)
    rw [← this]; exact hpp

/-- every prime `p` with `p³ > N` is rough, so the primes in `(N^{1/3}, N]` are all counted -/
theorem rough_of_prime {N p : ℕ} (hp : p.Prime) (h : N < p ^ 3) : Rough N p := by
  intro q hq
  rw [Nat.primeFactorsList_prime hp, List.mem_singleton] at hq
  rw [hq]; exact h

/-- vacuity: `N = 100`, `n = 35 = 5 · 7` is rough with two factors, not prime;
`n = 97` is rough and prime -/
example : Rough 100 35 ∧ ¬ (35).Prime := by
  refine ⟨?_, by norm_num⟩
  intro p hp
  have : (35 : ℕ).primeFactorsList = [5, 7] := by norm_num
  rw [this] at hp; simp at hp; rcases hp with rfl | rfl <;> norm_num
example : Rough 100 97 := rough_of_prime (by norm_num) (by norm_num)

end LeanLab.Routes.R0007
