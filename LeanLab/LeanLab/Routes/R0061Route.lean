import LeanLab.Common.Goldbach

/-!
# R-0061, the digit complement reflection at N = b^k - 1

T3 MOONSHOT, unit U-1588, PC run 20261030T0803Z-29399. AI wrote this Lean code, Claude,
checked only by the Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

Route. At `N = b^k - 1` the reflection `n ↦ N - n` on `[0, N]` is the digit complement
`d ↦ b - 1 - d` on length `k` base `b` words. So every digital statistic of `N - p` is a
digital statistic of `p`, a symmetric digit set `D = b - 1 - D` is mapped to itself, and
binary Goldbach at `N` is the statement that some length `k` word and its complement are both
prime. The question is whether the Type II digit technology of Mauduit-Rivat and Maynard,
which works for primes in digit sets, can see the second prime; the file isolates the exact
combinatorial identity, the equivalence, the reflection invariance of symmetric digit sets,
the mod 2 local obstruction found by the numerics, and the conditional bridge.

What this file proves, 0 sorry.
* `ofDigits_compl_add`: `ofDigits b (compl b L) + ofDigits b L + 1 = b ^ L.length`. PROVED.
* `reflect_eq_compl`: `b ^ L.length - 1 - ofDigits b L = ofDigits b (compl b L)`. PROVED.
* `compl_compl`, `compl_lt`: the complement is an involution on base `b` words. PROVED.
* `exists_word`: each `n < b ^ k` is `ofDigits b L` for a length `k` base `b` word. PROVED.
* `goldbach_iff_digitPair`: `IsGoldbachSum (b ^ k - 1) ↔ DigitPair b k`. PROVED.
* `digitSet_reflect`: a symmetric digit set at length `k` is closed under `n ↦ b^k - 1 - n`.
  PROVED.
* `even_ofDigits_iff`: odd base, odd digits: `ofDigits` is even iff the length is even.
  PROVED; `odd_digit_prime_even_length` then forces such a prime to be `2`.
* `goldbach_of_symmDigitGoldbach`: CONDITIONAL ON the OPEN Prop `SymmDigitGoldbach`, never
  asserted.
* Vacuity: `digitPair_five_three`, `41 + 83 = 124` with digits `1, 3` in base 5;
  `goldbach_124_via_digits`; `digitSet_five_odd_41`; `not_prime_word_five_two`.
-/

namespace LeanLab.Routes.R0061

open Nat

/-- Plain math: the digit complement of a base `b` word, `d ↦ b - 1 - d` in each place. -/
def compl (b : ℕ) (L : List ℕ) : List ℕ := L.map (fun d => b - 1 - d)

/-- Plain math: complement keeps length. PROVED. -/
@[simp] theorem compl_length (b : ℕ) (L : List ℕ) : (compl b L).length = L.length := by
  simp [compl]

/-- Plain math: complement digits are base `b` digits when `b ≥ 1`. PROVED. -/
theorem compl_lt {b : ℕ} (hb : 1 ≤ b) (L : List ℕ) : ∀ d ∈ compl b L, d < b := by
  intro d hd
  simp only [compl, List.mem_map] at hd
  obtain ⟨x, -, rfl⟩ := hd
  omega

/-- Plain math: complement is an involution on base `b` words. PROVED. -/
theorem compl_compl {b : ℕ} {L : List ℕ} (hL : ∀ d ∈ L, d < b) : compl b (compl b L) = L := by
  simp only [compl, List.map_map]
  conv_rhs => rw [← List.map_id L]
  apply List.map_congr_left
  intro d hd
  have := hL d hd
  simp only [Function.comp, id]
  omega

/-- Plain math, the headline identity: for a base `b` word `L` of length `k`,
`ofDigits(complement L) + ofDigits L + 1 = b^k`, since each place contributes
`(b - 1 - d + d) b^i` and `Σ (b - 1) b^i = b^k - 1`. PROVED. -/
theorem ofDigits_compl_add {b : ℕ} {L : List ℕ} (hL : ∀ d ∈ L, d < b) :
    ofDigits b (compl b L) + ofDigits b L + 1 = b ^ L.length := by
  induction L with
  | nil => simp [compl, ofDigits]
  | cons d t ih =>
    have ih' := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    have hd := hL d List.mem_cons_self
    simp only [compl, List.map_cons, ofDigits_cons, List.length_cons] at ih' ⊢
    generalize ofDigits b (List.map (fun d => b - 1 - d) t) = A at ih' ⊢
    generalize ofDigits b t = B at ih' ⊢
    obtain ⟨e, rfl⟩ : ∃ e, b = e + d + 1 := ⟨b - d - 1, by omega⟩
    have he : e + d + 1 - 1 - d = e := by omega
    rw [he, pow_succ, ← ih']
    ring

/-- Plain math: at `N = b^k - 1` the reflection `n ↦ N - n` is the digit complement. PROVED. -/
theorem reflect_eq_compl {b : ℕ} {L : List ℕ} (hL : ∀ d ∈ L, d < b) :
    b ^ L.length - 1 - ofDigits b L = ofDigits b (compl b L) := by
  have := ofDigits_compl_add hL
  omega

/-- Plain math: every `n < b^k` has a base `b` word of length exactly `k`, its digits padded
with zeros. PROVED. -/
theorem exists_word {b k n : ℕ} (hb : 1 < b) (hn : n < b ^ k) :
    ∃ L : List ℕ, L.length = k ∧ (∀ d ∈ L, d < b) ∧ ofDigits b L = n := by
  have hlen : (b.digits n).length ≤ k := (digits_length_le_iff hb n).2 hn
  refine ⟨b.digits n ++ List.replicate (k - (b.digits n).length) 0, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]; omega
  · intro d hd
    rcases List.mem_append.1 hd with h | h
    · exact digits_lt_base hb h
    · rw [List.eq_of_mem_replicate h]; omega
  · rw [ofDigits_append_replicate_zero, ofDigits_digits]

/-- Plain math: some length `k` base `b` word and its digit complement are both prime. -/
def DigitPair (b k : ℕ) : Prop :=
  ∃ L : List ℕ, L.length = k ∧ (∀ d ∈ L, d < b) ∧
    (ofDigits b L).Prime ∧ (ofDigits b (compl b L)).Prime

/-- Plain math, the headline equivalence: for `b ≥ 2`, `b^k - 1` is a sum of two primes iff
some length `k` base `b` word and its complement are both prime. PROVED. -/
theorem goldbach_iff_digitPair {b k : ℕ} (hb : 1 < b) :
    IsGoldbachSum (b ^ k - 1) ↔ DigitPair b k := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq⟩
    have hpos : 0 < b ^ k := by positivity
    obtain ⟨L, hlen, hL, hval⟩ := exists_word (k := k) (n := p) hb (by omega)
    refine ⟨L, hlen, hL, hval ▸ hp, ?_⟩
    have := reflect_eq_compl hL
    rw [hlen, hval] at this
    rw [← this]
    have : b ^ k - 1 - p = q := by omega
    rwa [this]
  · rintro ⟨L, hlen, hL, hp, hq⟩
    refine ⟨_, _, hp, hq, ?_⟩
    have := ofDigits_compl_add hL
    rw [hlen] at this
    omega

/-- Plain math: `n` is a length `k` base `b` word with every digit in `D`. -/
def DigitSet (b : ℕ) (D : Finset ℕ) (k n : ℕ) : Prop :=
  ∃ L : List ℕ, L.length = k ∧ (∀ d ∈ L, d ∈ D ∧ d < b) ∧ ofDigits b L = n

/-- Plain math: the digit set `D` is symmetric, `d ∈ D` implies `b - 1 - d ∈ D`. -/
def SymmDigits (b : ℕ) (D : Finset ℕ) : Prop := ∀ d ∈ D, d < b → b - 1 - d ∈ D

/-- Plain math: a symmetric digit set at length `k` is closed under the Goldbach reflection
`n ↦ b^k - 1 - n`, so a Goldbach pair at `b^k - 1` with one summand in it has both. PROVED. -/
theorem digitSet_reflect {b k n : ℕ} {D : Finset ℕ} (hb : 1 ≤ b) (hS : SymmDigits b D)
    (h : DigitSet b D k n) : DigitSet b D k (b ^ k - 1 - n) := by
  obtain ⟨L, hlen, hL, rfl⟩ := h
  refine ⟨compl b L, by simp [hlen], ?_, ?_⟩
  · intro d hd
    refine ⟨?_, compl_lt hb L d hd⟩
    simp only [compl, List.mem_map] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    exact hS x (hL x hx).1 (hL x hx).2
  · rw [← hlen]; exact (reflect_eq_compl (fun d hd => (hL d hd).2)).symm

/-- Plain math, the mod 2 local obstruction: in an odd base with every digit odd,
`ofDigits b L` is even iff `L` has even length, since `b^i ≡ 1` and `d ≡ 1` mod 2. PROVED. -/
theorem even_ofDigits_iff {b : ℕ} (hb : Odd b) {L : List ℕ} (hL : ∀ d ∈ L, Odd d) :
    Even (ofDigits b L) ↔ Even L.length := by
  induction L with
  | nil => simp [ofDigits]
  | cons d t ih =>
    have ih' := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    have hd := hL d List.mem_cons_self
    rw [ofDigits_cons, List.length_cons, Nat.even_add, Nat.even_mul, ih', Nat.even_add_one]
    have h1 : ¬ Even d := Nat.not_even_iff_odd.2 hd
    have h2 : ¬ Even b := Nat.not_even_iff_odd.2 hb
    tauto

/-- Plain math: odd base, odd digits, even length, then a prime word is `2`; so Goldbach in
such a symmetric digit set is impossible at even `k`, as the numerics show. PROVED. -/
theorem odd_digit_prime_even_length {b : ℕ} (hb : Odd b) {L : List ℕ} (hL : ∀ d ∈ L, Odd d)
    (hk : Even L.length) (hp : (ofDigits b L).Prime) : ofDigits b L = 2 :=
  (hp.even_iff).1 ((even_ofDigits_iff hb hL).2 hk)

/-- Plain math, OPEN: for all large odd `k`, some prime in the symmetric digit set at length
`k` has `b^k - 1 - n` prime too. Binary Goldbach restricted to a sparse reflection symmetric
set; it implies Goldbach at `b^k - 1` and is not known for any `D ≠ [0, b)`. Never asserted. -/
def SymmDigitGoldbach (b : ℕ) (D : Finset ℕ) : Prop :=
  ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → Odd k → ∃ n, DigitSet b D k n ∧ n.Prime ∧ (b ^ k - 1 - n).Prime

/-- Plain math: CONDITIONAL ON the OPEN Prop `SymmDigitGoldbach b D`, `b^k - 1` is a sum of
two primes for all large odd `k`. PROVED as an implication. -/
theorem goldbach_of_symmDigitGoldbach {b : ℕ} {D : Finset ℕ} (hb : 1 < b)
    (h : SymmDigitGoldbach b D) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → Odd k → IsGoldbachSum (b ^ k - 1) := by
  obtain ⟨k₀, hk⟩ := h
  refine ⟨k₀, fun k hk0 hko => ?_⟩
  obtain ⟨n, ⟨L, hlen, hL, rfl⟩, hp, hq⟩ := hk k hk0 hko
  have hlt := ofDigits_lt_base_pow_length hb (fun d hd => (hL d hd).2)
  rw [hlen] at hlt
  exact ⟨_, _, hp, hq, by omega⟩

/-! ## Vacuity instances -/

/-- Plain math: `41 = 1 + 3·5 + 1·25` and its complement `83 = 3 + 1·5 + 3·25` are prime,
digits in `{1, 3}`, base 5, `41 + 83 = 124 = 5^3 - 1`. PROVED. -/
theorem digitPair_five_three : DigitPair 5 3 := by
  refine ⟨[1, 3, 1], rfl, by decide, ?_, ?_⟩ <;> norm_num [compl, ofDigits]

/-- Plain math: `124` is a Goldbach sum, obtained through the digit equivalence. PROVED. -/
theorem goldbach_124_via_digits : IsGoldbachSum 124 :=
  (goldbach_iff_digitPair (b := 5) (k := 3) (by norm_num)).2 digitPair_five_three

/-- Plain math: `41` lies in the base 5 odd digit set `{1, 3}` at length 3. PROVED. -/
theorem digitSet_five_odd_41 : DigitSet 5 {1, 3} 3 41 :=
  ⟨[1, 3, 1], rfl, by decide, by norm_num [ofDigits]⟩

/-- Plain math: the set `{1, 3}` is symmetric in base 5. PROVED. -/
theorem symm_five_odd : SymmDigits 5 {1, 3} := by
  unfold SymmDigits; decide

/-- Plain math: the length 2 word `1, 1` in base 5 is `6`, not prime, a case of the mod 2
obstruction. PROVED. -/
theorem not_prime_word_five_two : ¬ (ofDigits 5 [1, 1]).Prime := by norm_num [ofDigits]

end LeanLab.Routes.R0061
