import LeanLab.Common.Goldbach
import LeanLab.Routes.R0007RoughParity

/-!
# R-0060, the reflected Jacobsthal covering route

T3 MOONSHOT, unit U-1586, PC run 20261029T0804Z-25466. AI wrote this Lean code, Claude,
checked only by the Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

Route. For even `N` let the sieving primes be the primes `p` with `p * p ≤ N`. A residue
system `a` picks one class `a p mod p` for each of them, and it covers `n` when
`n ≡ a p` or `N - n ≡ a p` mod some sieving prime `p`: two classes per prime, placed
symmetrically about `N / 2`. `NoCover N` says that no residue system covers every `n` in
`[2, N - 2]`. The real primes are the one system `a p = 0`, whose survivors are exactly the
`n` with `n` and `N - n` both prime and above `√N`; so `NoCover N` implies binary Goldbach at `N`.
This is a Jacobsthal type covering question for an interval of length `z²` by two classes per
prime `p ≤ z`; the one class analogue at length `z²` is Iwaniec's 1978 Jacobsthal bound,
`z² log² z`, and sieve theory alone reaches the two class version only at length about
`z^{4.27}`, the dimension two sieving limit.

What this file proves.
* `prime_of_no_small_factor`: `2 ≤ m ≤ N` with no prime factor `p`, `p * p ≤ N`, is prime. PROVED.
* `goldbach_of_noCover`: `NoCover N` implies `IsGoldbachSum N`. PROVED, the bridge.
* `uncovered_zero_of_primes`: a Goldbach pair with both primes above `√N` survives `a = 0`.
  PROVED.
* `covered_reflect`: `n` is covered iff `N - n` is. PROVED.
* `two_one_class`: at `p = 2` the two classes coincide for even `N`. PROVED.
* `goldbach_of_reflectedJacobsthal`: the open input `ReflectedJacobsthal`, never asserted,
  implies binary Goldbach for all large even `N`. PROVED.
* Vacuity: `noCover_eight`, `noCover_thirty`, `noCover_fifty` PROVED, the last by kernel
  evaluation over all `210` residue systems for the primes `2, 3, 5, 7`; and
  `not_noCover_four`: at `N = 4` the system `a = 0` covers `[2, 2]`, so `NoCover` is strictly
  stronger than Goldbach at a given `N`.
-/

namespace LeanLab.Routes.U1586

/-- Plain math: `n` is covered by the residue system `a` at `N` when some prime `p` with
`p² ≤ N` has `n ≡ a(p)` or `N - n ≡ a(p)` mod `p`. -/
def Covered (N : ℕ) (a : ℕ → ℕ) (n : ℕ) : Prop :=
  ∃ p, p.Prime ∧ p * p ≤ N ∧ (n % p = a p % p ∨ (N - n) % p = a p % p)

/-- Plain math: no residue system, one class `a(p)` per prime `p ≤ √N`, used with its
reflection `N - a(p)`, covers every integer `n` with `2 ≤ n ≤ N - 2`. -/
def NoCover (N : ℕ) : Prop :=
  ∀ a : ℕ → ℕ, ∃ n, 2 ≤ n ∧ n + 2 ≤ N ∧ ¬ Covered N a n

/-- Plain math, the OPEN input, the reflected Jacobsthal statement: for every large even `N`,
two symmetric classes per prime `p ≤ √N` never cover `[2, N - 2]`. Stronger than binary
Goldbach; a named hypothesis, never asserted in this file. -/
def ReflectedJacobsthal : Prop :=
  ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → Even N → NoCover N

/-- Plain math: if `2 ≤ m ≤ N` and no prime `p` with `p² ≤ N` divides `m`, then `m` is prime.
PROVED. -/
theorem prime_of_no_small_factor {N m : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N)
    (h : ∀ p, p.Prime → p * p ≤ N → ¬ p ∣ m) : m.Prime := by
  by_contra hnp
  have hq : (Nat.minFac m).Prime := Nat.minFac_prime (by omega)
  have hsq : Nat.minFac m ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hnp
  exact h _ hq (by nlinarith) (Nat.minFac_dvd m)

/-- Plain math, the bridge: if no residue system covers `[2, N - 2]`, then `N = p + q` with
`p, q` prime. Take `a = 0`: a survivor `n` has `n` and `N - n` free of prime factors
`p ≤ √N`, so both are prime. PROVED. -/
theorem goldbach_of_noCover {N : ℕ} (h : NoCover N) : IsGoldbachSum N := by
  obtain ⟨n, hn2, hnN, hnc⟩ := h (fun _ => 0)
  have key : ∀ p, p.Prime → p * p ≤ N → ¬ p ∣ n ∧ ¬ p ∣ (N - n) := by
    intro p hp hpp
    constructor
    · intro hd
      exact hnc ⟨p, hp, hpp, Or.inl (by simpa using Nat.mod_eq_zero_of_dvd hd)⟩
    · intro hd
      exact hnc ⟨p, hp, hpp, Or.inr (by simpa using Nat.mod_eq_zero_of_dvd hd)⟩
  refine ⟨n, N - n, ?_, ?_, by omega⟩
  · exact prime_of_no_small_factor hn2 (by omega) (fun p hp hpp => (key p hp hpp).1)
  · exact prime_of_no_small_factor (by omega) (by omega) (fun p hp hpp => (key p hp hpp).2)

/-- Plain math: if `n` and `N - n` are primes with `n² > N` and `(N - n)² > N`, then `n`
survives the real system `a = 0`; the survivors of `a = 0` are exactly these Goldbach pairs.
PROVED. -/
theorem uncovered_zero_of_primes {N n : ℕ} (hn : n.Prime) (hm : (N - n).Prime)
    (h1 : N < n * n) (h2 : N < (N - n) * (N - n)) : ¬ Covered N (fun _ => 0) n := by
  rintro ⟨p, hp, hpp, h | h⟩
  · have hd : p ∣ n := Nat.dvd_of_mod_eq_zero (by simpa using h)
    have := (Nat.prime_dvd_prime_iff_eq hp hn).1 hd
    subst this; omega
  · have hd : p ∣ N - n := Nat.dvd_of_mod_eq_zero (by simpa using h)
    have := (Nat.prime_dvd_prime_iff_eq hp hm).1 hd
    rw [this] at hpp; omega

/-- Plain math: for `n ≤ N`, `n` is covered by `a` iff `N - n` is, since the two classes
`a(p)` and `N - a(p)` are swapped by `n ↦ N - n`. PROVED. -/
theorem covered_reflect {N n : ℕ} (a : ℕ → ℕ) (hn : n ≤ N) :
    Covered N a n ↔ Covered N a (N - n) := by
  have hNN : N - (N - n) = n := by omega
  constructor
  · rintro ⟨p, hp, hpp, h⟩
    exact ⟨p, hp, hpp, by rw [hNN]; exact h.symm⟩
  · rintro ⟨p, hp, hpp, h⟩
    exact ⟨p, hp, hpp, by rw [hNN] at h; exact h.symm⟩

/-- Plain math: for even `N` and `n ≤ N`, `N - n ≡ n mod 2`, so the prime `2` contributes one
class, not two; every odd prime contributes two unless `2a(p) ≡ N mod p`. PROVED. -/
theorem two_one_class {N n : ℕ} (hN : Even N) (hn : n ≤ N) : (N - n) % 2 = n % 2 := by
  rcases hN with ⟨k, rfl⟩
  omega

/-- Plain math: the open input implies binary Goldbach for every even `N ≥ N₀`. PROVED,
CONDITIONAL ON `ReflectedJacobsthal`, which is not asserted. -/
theorem goldbach_of_reflectedJacobsthal (h : ReflectedJacobsthal) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → Even N → IsGoldbachSum N := by
  obtain ⟨N₀, hN₀⟩ := h
  exact ⟨N₀, fun N hN hev => goldbach_of_noCover (hN₀ N hN hev)⟩

/-! ## Vacuity instances -/

/-- Plain math: the primes `p` with `p² ≤ 50` are `2, 3, 5, 7`. PROVED. -/
theorem sieve_primes_le {p B : ℕ} (hp : p.Prime) (hpp : p * p ≤ B) (hB : B < 121) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have : p ≤ 10 := by nlinarith
  interval_cases p <;> simp_all <;> norm_num at hp

/-- Plain math, finite form at `N = 50`: for every choice of classes `b₂ < 2, b₃ < 3,
b₅ < 5, b₇ < 7` some `n` with `2 ≤ n ≤ 48` avoids `b_p` and `50 - b_p` mod each `p`.
PROVED by kernel evaluation, `210` systems. -/
theorem fifty_fin : ∀ b2 ∈ Finset.range 2, ∀ b3 ∈ Finset.range 3, ∀ b5 ∈ Finset.range 5, ∀ b7 ∈ Finset.range 7, ∃ n ∈ Finset.range 49, 2 ≤ n ∧
    ¬ (n % 2 = b2 ∨ (50 - n) % 2 = b2) ∧ ¬ (n % 3 = b3 ∨ (50 - n) % 3 = b3) ∧
    ¬ (n % 5 = b5 ∨ (50 - n) % 5 = b5) ∧ ¬ (n % 7 = b7 ∨ (50 - n) % 7 = b7) := by
  decide

/-- Plain math: `NoCover 50`, no residue system for `2, 3, 5, 7` covers `[2, 48]`; the
exact minimum number of survivors is `1`, the point `25`, found by the script. PROVED. -/
theorem noCover_fifty : NoCover 50 := by
  intro a
  obtain ⟨n, hn, hn2, h2, h3, h5, h7⟩ := fifty_fin (a 2 % 2) (Finset.mem_range.2 (Nat.mod_lt _ (by norm_num)))
    (a 3 % 3) (Finset.mem_range.2 (Nat.mod_lt _ (by norm_num))) (a 5 % 5) (Finset.mem_range.2 (Nat.mod_lt _ (by norm_num)))
    (a 7 % 7) (Finset.mem_range.2 (Nat.mod_lt _ (by norm_num)))
  have hn' := Finset.mem_range.1 hn
  refine ⟨n, hn2, by omega, ?_⟩
  rintro ⟨p, hp, hpp, h⟩
  rcases sieve_primes_le hp hpp (by norm_num) with rfl | rfl | rfl | rfl
  · exact h2 h
  · exact h3 h
  · exact h5 h
  · exact h7 h

/-- Plain math, finite form at `N = 30`, primes `2, 3, 5`. PROVED by kernel evaluation. -/
theorem thirty_fin : ∀ b2 ∈ Finset.range 2, ∀ b3 ∈ Finset.range 3, ∀ b5 ∈ Finset.range 5, ∃ n ∈ Finset.range 29, 2 ≤ n ∧
    ¬ (n % 2 = b2 ∨ (30 - n) % 2 = b2) ∧ ¬ (n % 3 = b3 ∨ (30 - n) % 3 = b3) ∧
    ¬ (n % 5 = b5 ∨ (30 - n) % 5 = b5) := by
  decide

/-- Plain math: `NoCover 30`. PROVED. -/
theorem noCover_thirty : NoCover 30 := by
  intro a
  obtain ⟨n, hn, hn2, h2, h3, h5⟩ := thirty_fin (a 2 % 2) (Finset.mem_range.2 (Nat.mod_lt _ (by norm_num)))
    (a 3 % 3) (Finset.mem_range.2 (Nat.mod_lt _ (by norm_num))) (a 5 % 5) (Finset.mem_range.2 (Nat.mod_lt _ (by norm_num)))
  have hn' := Finset.mem_range.1 hn
  refine ⟨n, hn2, by omega, ?_⟩
  rintro ⟨p, hp, hpp, h⟩
  rcases sieve_primes_le hp hpp (by norm_num) with rfl | rfl | rfl | rfl
  · exact h2 h
  · exact h3 h
  · exact h5 h
  · norm_num at hpp

/-- Plain math: `NoCover 8`: the only sieving prime is `2`, one class, and `[2, 6]` holds
both parities. PROVED. -/
theorem noCover_eight : NoCover 8 := by
  intro a
  refine ⟨if a 2 % 2 = 0 then 3 else 2, by split <;> omega, by split <;> omega, ?_⟩
  rintro ⟨p, hp, hpp, h⟩
  rcases sieve_primes_le hp hpp (by norm_num) with rfl | rfl | rfl | rfl
  · split at h <;> omega
  all_goals norm_num at hpp

/-- Plain math: `NoCover 4` fails: with `a = 0` the prime `2` covers the only point `2` of
`[2, 2]`, although `4 = 2 + 2`. So `NoCover N` is strictly stronger than Goldbach at `N`.
PROVED. -/
theorem not_noCover_four : ¬ NoCover 4 := by
  intro h
  obtain ⟨n, hn2, hn4, hc⟩ := h (fun _ => 0)
  have : n = 2 := by omega
  subst this
  exact hc ⟨2, Nat.prime_two, by norm_num, Or.inl rfl⟩

/-- Vacuity instance for the bridge: `goldbach_of_noCover` applies at `N = 50`. PROVED. -/
theorem goldbach_fifty_via_noCover : IsGoldbachSum 50 := goldbach_of_noCover noCover_fifty

end LeanLab.Routes.U1586

#print axioms LeanLab.Routes.U1586.prime_of_no_small_factor
#print axioms LeanLab.Routes.U1586.goldbach_of_noCover
#print axioms LeanLab.Routes.U1586.uncovered_zero_of_primes
#print axioms LeanLab.Routes.U1586.covered_reflect
#print axioms LeanLab.Routes.U1586.two_one_class
#print axioms LeanLab.Routes.U1586.goldbach_of_reflectedJacobsthal
#print axioms LeanLab.Routes.U1586.sieve_primes_le
#print axioms LeanLab.Routes.U1586.fifty_fin
#print axioms LeanLab.Routes.U1586.noCover_fifty
#print axioms LeanLab.Routes.U1586.thirty_fin
#print axioms LeanLab.Routes.U1586.noCover_thirty
#print axioms LeanLab.Routes.U1586.noCover_eight
#print axioms LeanLab.Routes.U1586.not_noCover_four
#print axioms LeanLab.Routes.U1586.goldbach_fifty_via_noCover
