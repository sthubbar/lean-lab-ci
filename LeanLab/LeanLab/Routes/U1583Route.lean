import LeanLab.Routes.R0007RoughParity

/-!
# R-0059, the pretentious route and the single N multiplicative decoy

T3 MOONSHOT, unit U-1583, PC run 20261028T0803Z-11675. AI wrote this Lean code, Claude,
checked only by the Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

Route. On `N`-rough numbers, every prime factor `p` with `p³ > N`, prime means `λ = -1`
(R-0007). Replace `λ` by any completely multiplicative `f` with values `±1`, built here as
`liftSign s`, the product of signs `s p` over the prime factors with multiplicity. The fake
primes are the rough `n` with `f n = -1`, and for each pair `a + b = N`
`4 · [f a = -1 ∧ f b = -1] = 1 - f a - f b + f a f b`, so summed over rough pairs
`4 r_f(N) = R - S_f + C_f` with `C_f` the reflected correlation. Pretentious theory,
Granville-Soundararajan, Halász, Klurman, Tao, sorts `f` into pretentious ones, whose
correlations are local Euler products, and non-pretentious ones, whose correlations are small
on average. `λ` is non-pretentious, a theorem equivalent to the prime number theorem in
progressions, and that is parity information no sieve has.

What this file proves.
* `four_mul_card`, the counting identity above, any `±1` valued `f`. PROVED.
* `liftSign_mul`, `liftSign_isSign`, `liftSign_sq`: `liftSign s` is completely multiplicative,
  `±1` valued, and `1` on squares, so a pair of squares `a + b = N` always has `f a f b = 1`:
  the pure reflection condition `f a f b = -1` for all pairs is unsatisfiable at such `N`,
  which is why the numerics need the weaker decoy condition. PROVED.
* `liftSign_eq_of_agree`: two sign choices agreeing off a set `F` of primes give the same
  value at every `n` with no prime factor in `F`. PROVED. The decoy changes `λ` only on the
  window `(N^{1/3}, N]`.
* `chi4_mul_odd`, `chi4_reflect`: the local decoy `χ₋₄` on odd numbers, multiplicative, with
  `χ₋₄(a) χ₋₄(N - a) = -1` for every odd `a < N` when `4 ∣ N`. PROVED. This decoy is pretentious
  and visible to a sieve mod 4.
* `decoy100`: an explicit non-local decoy at `N = 100`: `f = λ` except `f p = +1` for
  `p ∈ {13, 53, 59, 71, 83, 89}`, and no rough pair `a + (100 - a)` has `f a = f (100 - a) = -1`,
  although `47 + 53` is a rough Goldbach pair. PROVED by kernel evaluation.
* `goldbach_of_corr`: binary Goldbach at `N` from positivity of `R - S_λ + C_λ` over any set
  of rough pairs. PROVED, the identity only; the positivity is the open input.
-/

namespace LeanLab.Routes.U1583

open Finset

/-! ## Completely multiplicative sign functions -/

/-- Plain math: `liftSign s n = ∏_{p^k ∥ n} s(p)^k`, the completely multiplicative function with
`f(p) = s(p)`. -/
def liftSign (s : ℕ → ℤ) (n : ℕ) : ℤ := (n.primeFactorsList.map s).prod

/-- Plain math: `f(mn) = f(m) f(n)` for `m, n ≥ 1`. PROVED. -/
theorem liftSign_mul (s : ℕ → ℤ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    liftSign s (m * n) = liftSign s m * liftSign s n := by
  unfold liftSign
  rw [((Nat.perm_primeFactorsList_mul hm hn).map s).prod_eq, List.map_append, List.prod_append]

/-- Plain math: `f(p) = s(p)` at a prime `p`. PROVED. -/
theorem liftSign_prime (s : ℕ → ℤ) {p : ℕ} (hp : p.Prime) : liftSign s p = s p := by
  simp [liftSign, Nat.primeFactorsList_prime hp]

/-- Plain math: with every sign `-1`, `liftSign` is Liouville's `λ(n) = (-1)^Ω(n)`. PROVED. -/
theorem liftSign_neg_one (n : ℕ) :
    liftSign (fun _ => -1) n = (-1) ^ n.primeFactorsList.length := by
  simp [liftSign, List.map_const', List.prod_replicate]

/-- Plain math: if every `s(p) = ±1` then every `f(n) = ±1`. PROVED. -/
theorem liftSign_isSign (s : ℕ → ℤ) (hs : ∀ p, s p = 1 ∨ s p = -1) (n : ℕ) :
    liftSign s n = 1 ∨ liftSign s n = -1 := by
  unfold liftSign
  induction n.primeFactorsList with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons]
    rcases hs p with h | h <;> rcases ih with h' | h' <;> simp [h, h']

/-- Plain math: `f(m²) = 1`, so squares are never fake primes. PROVED. -/
theorem liftSign_sq (s : ℕ → ℤ) (hs : ∀ p, s p = 1 ∨ s p = -1) (m : ℕ) :
    liftSign s (m * m) = 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [liftSign]
  rw [liftSign_mul s hm.ne' hm.ne']
  rcases liftSign_isSign s hs m with h | h <;> simp [h]

/-- Plain math: if `a = m²` and `N - a = k²` then `f(a) f(N - a) = 1` for every `±1`
completely multiplicative `f`: the pure reflection decoy `f(a) f(N-a) = -1` for all pairs
fails at such `N`, as found numerically at `N = 170 = 49 + 121`. PROVED. -/
theorem square_pair_obstruction (s : ℕ → ℤ) (hs : ∀ p, s p = 1 ∨ s p = -1) (m k : ℕ) :
    liftSign s (m * m) * liftSign s (k * k) = 1 := by
  rw [liftSign_sq s hs, liftSign_sq s hs, one_mul]

/-- Plain math: if `s = s'` on every prime outside `F` and `n` has no prime factor in `F`, then
`f_s(n) = f_{s'}(n)`. A decoy that changes `λ` only on the primes of `(N^{1/3}, N]` agrees with
`λ` on every `n` free of those primes. PROVED. -/
theorem liftSign_eq_of_agree (s s' : ℕ → ℤ) (F : Set ℕ) (h : ∀ p, p ∉ F → s p = s' p)
    (n : ℕ) (hn : ∀ p ∈ n.primeFactorsList, p ∉ F) : liftSign s n = liftSign s' n := by
  unfold liftSign
  rw [List.map_congr_left (fun p hp => h p (hn p hp))]

/-! ## The counting identity -/

/-- Plain math: for `±1` valued `f` and a set `S` of first coordinates `a` of pairs
`a + (N - a) = N`, `4 #{a ∈ S : f(a) = f(N - a) = -1} = Σ_{a ∈ S} (1 - f a - f(N-a) + f a f(N-a))`,
that is `4 r_f = R - S_f + C_f`. PROVED. -/
theorem four_mul_card (f : ℕ → ℤ) (hf : ∀ n, f n = 1 ∨ f n = -1) (N : ℕ) (S : Finset ℕ) :
    4 * ((S.filter fun a => f a = -1 ∧ f (N - a) = -1).card : ℤ)
      = ∑ a ∈ S, (1 - f a - f (N - a) + f a * f (N - a)) := by
  rw [Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro a _
  rcases hf a with h1 | h1 <;> rcases hf (N - a) with h2 | h2 <;> simp [h1, h2]

/-- Plain math: a decoy, no pair with `f(a) = f(N - a) = -1`, has `C_f = S_f - R` exactly.
PROVED. -/
theorem decoy_corr (f : ℕ → ℤ) (hf : ∀ n, f n = 1 ∨ f n = -1) (N : ℕ) (S : Finset ℕ)
    (hdec : ∀ a ∈ S, ¬ (f a = -1 ∧ f (N - a) = -1)) :
    ∑ a ∈ S, f a * f (N - a) = ∑ a ∈ S, (f a + f (N - a)) - S.card := by
  have h := four_mul_card f hf N S
  have h0 : (S.filter fun a => f a = -1 ∧ f (N - a) = -1) = ∅ :=
    Finset.filter_eq_empty_iff.mpr hdec
  rw [h0, Finset.card_empty] at h
  have e : ∑ a ∈ S, (1 - f a - f (N - a) + f a * f (N - a))
      = (S.card : ℤ) - ∑ a ∈ S, (f a + f (N - a)) + ∑ a ∈ S, f a * f (N - a) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  rw [e] at h
  push_cast at h
  linarith

/-- Plain math: if `R - S_λ + C_λ > 0` over a set `S` of `a` with `1 < a`, `a < N` and both
`a`, `N - a` rough, then `N = p + q` with `p, q` prime. PROVED; the positivity is the open input,
the single `N` Elliott bound for the reflected Liouville pair. -/
theorem goldbach_of_corr (N : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, 1 < a ∧ a < N ∧ R0007.Rough N a ∧ R0007.Rough N (N - a))
    (hpos : 0 < ∑ a ∈ S, (1 - liftSign (fun _ => -1) a - liftSign (fun _ => -1) (N - a)
        + liftSign (fun _ => -1) a * liftSign (fun _ => -1) (N - a))) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N := by
  have hf : ∀ n, liftSign (fun _ => -1) n = 1 ∨ liftSign (fun _ => -1) n = -1 :=
    liftSign_isSign _ (fun _ => Or.inr rfl)
  rw [← four_mul_card _ hf N S] at hpos
  have hc : (0 : ℤ) < ((S.filter fun a => liftSign (fun _ => -1) a = -1 ∧
      liftSign (fun _ => -1) (N - a) = -1).card : ℤ) := by linarith
  have hne := Finset.card_pos.mp (by exact_mod_cast hc)
  obtain ⟨a, ha⟩ := hne
  rw [Finset.mem_filter] at ha
  obtain ⟨haS, h1, h2⟩ := ha
  obtain ⟨ha1, haN, hra, hrb⟩ := hS a haS
  have key : ∀ n, 1 < n → n ≤ N → R0007.Rough N n → liftSign (fun _ => -1) n = -1 → n.Prime := by
    intro n hn hnN hr hl
    rw [R0007.prime_iff_odd_card hn hnN hr]
    rw [liftSign_neg_one] at hl
    exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num)).mp hl
  have hb1 : 1 < N - a := by
    by_contra hc
    have : N - a ≤ 1 := by omega
    have h1' : liftSign (fun _ => -1) (N - a) = 1 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h <;> rw [h] <;> simp [liftSign]
    have h2' : liftSign (fun _ => -1) (N - a) = -1 := h2
    rw [h1'] at h2'; norm_num at h2'
  exact ⟨a, N - a, key a ha1 haN.le hra h1, key (N - a) hb1 (by omega) hrb h2, by omega⟩

/-! ## The local decoy `χ₋₄` -/

/-- Plain math: `χ(n) = -1` if `n ≡ 3 mod 4`, else `1`; on odd `n` this is `χ₋₄`. -/
def chi4 (n : ℕ) : ℤ := if n % 4 = 3 then -1 else 1

/-- Plain math: `χ₋₄(mn) = χ₋₄(m) χ₋₄(n)` for odd `m, n`. PROVED. -/
theorem chi4_mul_odd {m n : ℕ} (hm : m % 2 = 1) (hn : n % 2 = 1) :
    chi4 (m * n) = chi4 m * chi4 n := by
  have h1 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  have h2 : n % 4 = 1 ∨ n % 4 = 3 := by omega
  unfold chi4
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [Nat.mul_mod, h1, h2]

/-- Plain math: if `4 ∣ N` and `a < N` is odd then `χ₋₄(a) χ₋₄(N - a) = -1`: the fake primes
`n ≡ 3 mod 4` never pair to `N`. A local decoy, which the singular series sees. PROVED. -/
theorem chi4_reflect {N a : ℕ} (hN : N % 4 = 0) (ha : a % 2 = 1) (haN : a < N) :
    chi4 a * chi4 (N - a) = -1 := by
  unfold chi4
  split_ifs with h1 h2 h2 <;> (try norm_num) <;> omega

/-! ## An explicit single N decoy at `N = 100`, found by numerics/U1583/u1583_decoy.py -/

instance roughDec (N : ℕ) : DecidablePred (R0007.Rough N) := fun n => by
  unfold R0007.Rough; infer_instance

/-- the primes in `(100^{1/3}, 100]` whose sign the decoy flips from `-1` to `+1` -/
def flips100 : List ℕ := [13, 53, 59, 71, 83, 89]

/-- Plain math: `f(p) = +1` for `p ∈ {13, 53, 59, 71, 83, 89}`, `f(p) = -1 = λ(p)` otherwise,
extended completely multiplicatively. -/
def f100 : ℕ → ℤ := liftSign (fun p => if p ∈ flips100 then 1 else -1)

/-- Plain math: `f100` agrees with Liouville's `λ` at every `n` with no prime factor in the flip
list. PROVED. -/
theorem f100_eq_liouville (n : ℕ) (hn : ∀ p ∈ n.primeFactorsList, p ∉ flips100) :
    f100 n = liftSign (fun _ => -1) n :=
  liftSign_eq_of_agree _ _ {p | p ∈ flips100} (fun p hp => by simp at hp; simp [hp]) n hn

/-- Plain math: no rough pair `a + b = 100`, `2 ≤ a ≤ 50`, has `f100(a) = f100(b) = -1`; so the
fake primes of `f100` do not represent `100`, although `f100` is completely multiplicative,
`±1` valued and equals `λ` off six primes. PROVED by kernel evaluation. -/
theorem decoy100 : ∀ a ∈ Finset.Icc 2 50, R0007.Rough 100 a → R0007.Rough 100 (100 - a) →
    ¬ (f100 a = -1 ∧ f100 (100 - a) = -1) := by
  decide +kernel

/-- Vacuity instance: Liouville itself is not a decoy at `100`: `47 + 53` is a rough pair with
`λ(47) = λ(53) = -1`. PROVED. -/
theorem liouville_not_decoy100 : R0007.Rough 100 47 ∧ R0007.Rough 100 53 ∧
    liftSign (fun _ => -1) 47 = -1 ∧ liftSign (fun _ => -1) 53 = -1 := by
  decide +kernel

/-- Vacuity instance: the hypotheses of `four_mul_card` and `decoy_corr` are met by `f100`
on the rough pairs of `100`. PROVED. -/
theorem f100_isSign (n : ℕ) : f100 n = 1 ∨ f100 n = -1 :=
  liftSign_isSign _ (fun p => by by_cases h : p ∈ flips100 <;> simp [h]) n

/-- Vacuity instance for `goldbach_of_corr`: the set `{47}` meets its hypotheses at `N = 100`.
PROVED. -/
theorem goldbach_of_corr_vacuity : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 100 := by
  apply goldbach_of_corr 100 {47}
  · intro a ha
    rw [Finset.mem_singleton] at ha
    subst ha
    exact ⟨by norm_num, by norm_num, liouville_not_decoy100.1, liouville_not_decoy100.2.1⟩
  · rw [Finset.sum_singleton]
    rw [show 100 - 47 = 53 from rfl, liouville_not_decoy100.2.2.1, liouville_not_decoy100.2.2.2]
    norm_num

end LeanLab.Routes.U1583
