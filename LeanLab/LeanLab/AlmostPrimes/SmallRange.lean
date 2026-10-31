/-
The elementary small range of P0048 Dudek, Dunn 2026 and P0020 Campbell 2026.
Unit U-0330, run 20261017T1602Z-14151. AI-written Lean code, Claude; checked by the Lean kernel.
Campbell's abstract says small N are handled by explicit prime gap data. Neither PDF text was
readable this run, so these are the lab's own elementary arguments, not transcriptions of the
papers' lemmas. Goldbach itself is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.Statements

namespace LeanLab.AlmostPrimes

theorem two_pow_length_le_prod (l : List ℕ) (h : ∀ x ∈ l, 2 ≤ x) : 2 ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.prod_cons, pow_succ']
    exact Nat.mul_le_mul (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

/-- Every prime factor is at least 2, so `2 ^ Ω(n) ≤ n` for `n > 0`. -/
theorem two_pow_bigOmega_le {n : ℕ} (hn : 0 < n) : 2 ^ bigOmega n ≤ n := by
  unfold bigOmega
  calc 2 ^ n.primeFactorsList.length ≤ n.primeFactorsList.prod :=
        two_pow_length_le_prod _ fun x hx => (Nat.prime_of_mem_primeFactorsList hx).two_le
    _ = n := Nat.prod_primeFactorsList hn.ne'

/-- `Ω(m) ≤ k` once `0 < m < 2 ^ (k + 1)`. -/
theorem bigOmega_le_of_lt {m k : ℕ} (hm : 0 < m) (hk : m < 2 ^ (k + 1)) : bigOmega m ≤ k := by
  by_contra h
  rw [not_le] at h
  have := two_pow_bigOmega_le hm
  have : 2 ^ (k + 1) ≤ 2 ^ bigOmega m := Nat.pow_le_pow_right (by norm_num) h
  omega

/-- Trivial range: `N = 1 + (N - 1)` gives `Ω(ab) ≤ k` for `2 ≤ N ≤ 2 ^ (k + 1)`. -/
theorem twoAlmostPrimes_of_le_pow {k N : ℕ} (h2 : 2 ≤ N) (hN : N ≤ 2 ^ (k + 1)) :
    TwoAlmostPrimes k N := by
  refine ⟨1, N - 1, by norm_num, by omega, by omega, ?_⟩
  rw [one_mul]
  exact bigOmega_le_of_lt (by omega) (by omega)

/-- Dudek and Dunn's statement holds with no sieve for `N ≤ 2 ^ 41`, about 2.2e12. -/
theorem dudek_dunn_small : ∀ N : ℕ, 2 ≤ N → N ≤ 2 ^ 41 → TwoAlmostPrimes 40 N :=
  fun _ h2 hN => twoAlmostPrimes_of_le_pow h2 hN

/-- Campbell's statement holds with no sieve for `N ≤ 2 ^ 34`, about 1.7e10. -/
theorem campbell_small : ∀ N : ℕ, 2 ≤ N → N ≤ 2 ^ 34 → TwoAlmostPrimes 33 N :=
  fun _ h2 hN => twoAlmostPrimes_of_le_pow h2 hN

/-- Prime gap step: if a prime `p < N` has `N - p < 2 ^ (j + 1)`, then `Ω(p (N - p)) ≤ j + 1`. -/
theorem twoAlmostPrimes_of_prime_near {N p j : ℕ} (hp : p.Prime) (hpN : p < N)
    (hg : N - p < 2 ^ (j + 1)) : TwoAlmostPrimes (j + 1) N := by
  have hm : 0 < N - p := by omega
  have h1 : PrimePlusAlmostPrime j N :=
    ⟨p, N - p, hp, hm, by omega, bigOmega_le_of_lt hm hg⟩
  exact two_of_prime_plus h1

/-- A prime gap bound as a hypothesis: every `n` with `3 ≤ n ≤ X` has a prime `p < n`
with `n - p ≤ G`. This is what cited prime gap tables give. -/
def PrimeBelowWithin (X G : ℕ) : Prop :=
  ∀ n : ℕ, 3 ≤ n → n ≤ X → ∃ p : ℕ, p.Prime ∧ p < n ∧ n - p ≤ G

/-- From a gap bound `G < 2 ^ (j + 1)` up to `X`, every `2 ≤ N ≤ X` is `a + b` with
`Ω(ab) ≤ j + 1`. -/
theorem twoAlmostPrimes_of_gaps {X G j : ℕ} (hX : PrimeBelowWithin X G) (hG : G < 2 ^ (j + 1)) :
    ∀ N : ℕ, 2 ≤ N → N ≤ X → TwoAlmostPrimes (j + 1) N := by
  intro N h2 hN
  rcases Nat.lt_or_ge N 3 with h | h
  · have : N = 2 := by omega
    subst this
    exact ⟨1, 1, by norm_num, by norm_num, rfl, by simp [bigOmega]⟩
  · obtain ⟨p, hp, hpN, hg⟩ := hX N h hN
    exact twoAlmostPrimes_of_prime_near hp hpN (by omega)

/-- Bertrand in Mathlib gives a prime in `(n/2, n)`, so `PrimeBelowWithin` holds with `G = n/2`;
this only recovers the trivial range. Proved for orientation. -/
theorem primeBelow_bertrand (n : ℕ) (h3 : 3 ≤ n) : ∃ p : ℕ, p.Prime ∧ p < n ∧ n - p ≤ n / 2 + 1 := by
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
  rcases Nat.lt_or_ge p n with h | h
  · exact ⟨p, hp, h, by omega⟩
  · -- p = n only when n = 2 * (n / 2), then n is even and ≥ 4, not prime
    have hpn : p = n := by omega
    subst hpn
    exfalso
    have : 2 ∣ p := ⟨p / 2, by omega⟩
    rcases hp.eq_one_or_self_of_dvd 2 this with h | h <;> omega

/-- With a gap bound `G ≤ 1476`, the P0005 maximal gap below 4e18, every `2 ≤ N ≤ X` has
`Ω(ab) ≤ 11`, far below 33. Conditional on the cited gap data, see `OeSHP.maxGap`. -/
theorem eleven_of_gaps {X : ℕ} (hX : PrimeBelowWithin X 1476) :
    ∀ N : ℕ, 2 ≤ N → N ≤ X → TwoAlmostPrimes 11 N :=
  twoAlmostPrimes_of_gaps hX (j := 10) (by norm_num)

end LeanLab.AlmostPrimes
