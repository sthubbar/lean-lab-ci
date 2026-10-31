/-
P0057 J. Kim, "Goldbach's problem in short intervals for numbers with a missing digit",
arXiv 2412.19975, v1 read 2026-10-17.
Setting: `X` is a power of a base `g`, `b ∈ {2, …, g-1}` is an excluded digit, and
`[X, X+H]^*` is the set of `n` with `X < n ≤ X + H` having no digit `b` in base `g`.
Theorem 1.1 (unconditional): for `X^{3/5+ε} ≪ H ≪ X^{1-ε}` and `g` large in terms of `ε`,
`∑_{n ∈ [X,X+H]^*} d₄(n) ≪ (log X)^7 |[X,X+H]^*|`.
Theorem 1.2 (conditional on a zero-free strip `Re s > 1 - c₂` for all Dirichlet `L`-functions):
for `X^{2/3+ε} ≪ H ≪ X^{1-ε}` and `g` large in terms of `ε`, almost all even numbers in
`[X,X+H]^*` are sums of two primes.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN. The results here are about almost all, and Theorem 1.2 is conditional.

Encoding of asymptotic notation. Every `≪` is replaced by explicit existential or universal
constants, as stated in each docstring: a hypothesis `X^{a+ε} ≪ H ≪ X^{1-ε}` becomes
`A₁ X^{a+ε} ≤ H ≤ A₂ X^{1-ε}` for arbitrary fixed `A₁, A₂ > 0`; a conclusion `F ≪ G` becomes
`∃ C, F ≤ C G` for all large `X`; "almost all" becomes "the exceptional count is at most
`η` times the count of all even elements, for every `η > 0` and all large `X`".
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.MissingDigit
open Finset Real

attribute [local instance] Classical.propDecidable

/-! ### Definitions -/

/-- `n` has no digit `b` in its base `g` expansion, read off from `Nat.digits g n`, which is the
little-endian expansion with no leading zeros. The paper's `b ∈ {2,…,g-1}` is never `0`, so
leading zeros play no role. Note `Nat.digits g 0 = []`, so `0` qualifies. -/
def NoDigit (g b n : ℕ) : Prop := b ∉ Nat.digits g n

instance (g b : ℕ) : DecidablePred (NoDigit g b) :=
  fun n => inferInstanceAs (Decidable (b ∉ Nat.digits g n))

/-- The paper's `[X, X+H]^*`: natural numbers `X < n ≤ X + H` with no digit `b` in base `g`.
For real `H` and natural `n`, `n ≤ X + H` is equivalent to `n ≤ X + ⌊H⌋₊` when `H ≥ 0`, and both
sides are empty when `H < 0`, so this is exactly the paper's set. -/
noncomputable def starSet (g b X : ℕ) (H : ℝ) : Finset ℕ :=
  (Finset.Ioc X (X + ⌊H⌋₊)).filter (NoDigit g b)

/-- Number of even elements of `[X,X+H]^*`. -/
noncomputable def evenCount (g b X : ℕ) (H : ℝ) : ℕ := ((starSet g b X H).filter Even).card

/-- The exceptional set count: even elements of `[X,X+H]^*` that are not sums of two primes. -/
noncomputable def excCount (g b X : ℕ) (H : ℝ) : ℕ :=
  ((starSet g b X H).filter (fun n => Even n ∧ ¬ IsGoldbachSum n)).card

/-- The `k`-fold divisor function `d_k`, with `d_0 = [n = 1]` and
`d_{k+1}(n) = ∑_{d ∣ n} d_k(n/d)`. So `d_2 = d` and `d_4` is the paper's `d₄`. -/
def dk : ℕ → ℕ → ℕ
  | 0, n => if n = 1 then 1 else 0
  | k + 1, n => ∑ d ∈ n.divisors, dk k (n / d)

/-- The paper's Assumption: there is a fixed `c₂ > 0` with `L(s, χ) ≠ 0` for every Dirichlet
character `χ` of every modulus and every `s` with `Re s > 1 - c₂`. The point `s = 1` is excluded
because there `L(s, χ₀)` has a pole, not a zero; Mathlib assigns a junk value at the pole. -/
def ZeroFreeAssumption : Prop :=
  ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    1 - c₂ < s.re → s ≠ 1 → DirichletCharacter.LFunction χ s ≠ 0

/-- Theorem 1.1 shape with exponent `a` and log power `j`: for every `ε > 0` there is `g₀` such
that for `g ≥ g₀`, every digit `b ∈ {2,…,g-1}`, and all fixed `A₁, A₂ > 0`, there are `C` and `K₀`
with `∑_{n ∈ [X,X+H]^*} d₄(n) ≤ C (log X)^j |[X,X+H]^*|` whenever `X = g^k`, `k ≥ K₀` and
`A₁ X^{a+ε} ≤ H ≤ A₂ X^{1-ε}`. The constant `C` may depend on `ε, g, b, A₁, A₂`. -/
def D4Bound (a : ℝ) (j : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ g₀ : ℕ, ∀ g b : ℕ, g₀ ≤ g → 2 ≤ b → b ≤ g - 1 →
    ∀ A₁ A₂ : ℝ, 0 < A₁ → 0 < A₂ → ∃ C : ℝ, ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      A₁ * ((g ^ k : ℕ) : ℝ) ^ (a + ε) ≤ H → H ≤ A₂ * ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ)) ≤
        C * Real.log ((g ^ k : ℕ) : ℝ) ^ j * (starSet g b (g ^ k) H).card

/-- Theorem 1.2 shape with exponent `a`: for every `ε > 0` there is `g₀` such that for `g ≥ g₀`,
every digit `b ∈ {2,…,g-1}`, all fixed `A₁, A₂ > 0` and every `η > 0`, there is `K₀` with
`excCount ≤ η · evenCount` whenever `X = g^k`, `k ≥ K₀` and `A₁ X^{a+ε} ≤ H ≤ A₂ X^{1-ε}`. -/
def AlmostAllGoldbach (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ g₀ : ℕ, ∀ g b : ℕ, g₀ ≤ g → 2 ≤ b → b ≤ g - 1 →
    ∀ A₁ A₂ : ℝ, 0 < A₁ → 0 < A₂ → ∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      A₁ * ((g ^ k : ℕ) : ℝ) ^ (a + ε) ≤ H → H ≤ A₂ * ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      (excCount g b (g ^ k) H : ℝ) ≤ η * evenCount g b (g ^ k) H

/-- Existence form, odd base: for every `ε > 0` there is `g₀` such that for odd `g ≥ g₀` and every
`b ∈ {2,…,g-1}` there is `K₀` such that every `[X, X+H]^*` with `X = g^k`, `k ≥ K₀` and
`X^{a+ε} ≤ H ≤ X^{1-ε}` contains an even sum of two primes. -/
def ExistsGoldbachOddBase (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ g₀ : ℕ, ∀ g b : ℕ, g₀ ≤ g → Odd g → 2 ≤ b → b ≤ g - 1 →
    ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ (a + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ∃ n ∈ starSet g b (g ^ k) H, Even n ∧ IsGoldbachSum n

/-- Perelli and Pintz, as quoted in P0057: almost all even integers in `[X, X + X^{1/3+ε}]` are
Goldbach numbers. Encoded as: for `ε, η > 0` and `X` large, the number of even `n` with
`X < n ≤ X + X^{1/3+ε}` that are not sums of two primes is at most `η X^{1/3+ε}`. -/
def PerelliPintzQuoted : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    (((Finset.Ioc ⌊X⌋₊ ⌊X + X ^ ((1 : ℝ) / 3 + ε)⌋₊).filter
        (fun n => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ) ≤ η * X ^ ((1 : ℝ) / 3 + ε)

/-! ### The paper's results, cited, with `sorry` -/

/-- Cited. P0057 Theorem 1.1, unconditional: `∑ d₄(n) ≪ (log X)^7 |[X,X+H]^*|` for
`X^{3/5+ε} ≪ H ≪ X^{1-ε}` and `g` large in terms of `ε`. -/
theorem kim_thm1_1 : D4Bound (3 / 5) 7 := by sorry

/-- Cited. P0057 Theorem 1.2, conditional on the Assumption: almost all `2n ∈ [X,X+H]^*` are
Goldbach numbers for `X^{2/3+ε} ≪ H ≪ X^{1-ε}` and `g` large in terms of `ε`. -/
theorem kim_thm1_2 : ZeroFreeAssumption → AlmostAllGoldbach (2 / 3) := by sorry

/-- Cited, as quoted in P0057 from Perelli and Pintz. -/
theorem perelli_pintz_quoted : PerelliPintzQuoted := by sorry

/-! ### Basic facts about the missing digit set, zero sorry -/

theorem md_zero (g b : ℕ) : NoDigit g b 0 := by simp [NoDigit]

/-- The digit recursion: for `x < g`, `x + g y` misses `b` iff `x ≠ b` and `y` misses `b`. -/
theorem md_add_mul {g b x y : ℕ} (hg : 2 ≤ g) (hb : 1 ≤ b) (hx : x < g) :
    NoDigit g b (x + g * y) ↔ x ≠ b ∧ NoDigit g b y := by
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp only [mul_zero, add_zero]
    exact ⟨fun _ => ⟨by omega, md_zero g b⟩, fun _ => md_zero g b⟩
  · have h' : x ≠ 0 ∨ y ≠ 0 := by tauto
    unfold NoDigit
    rw [Nat.digits_add g (by omega) x y hx h']
    simp only [List.mem_cons, not_or]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun e => h1 e.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨fun e => h1 e.symm, h2⟩⟩

/-- A single digit `d < g` qualifies iff `d ≠ b`. -/
theorem md_digit {g b d : ℕ} (hg : 2 ≤ g) (hb : 1 ≤ b) (hd : d < g) :
    NoDigit g b d ↔ d ≠ b := by
  have := md_add_mul (y := 0) hg hb hd
  simp only [mul_zero, add_zero] at this
  rw [this]; exact ⟨fun h => h.1, fun h => ⟨h, md_zero g b⟩⟩

/-- Closure under multiplication by the base: appending a digit `0`. -/
theorem md_mul_base {g b y : ℕ} (hg : 2 ≤ g) (hb : 1 ≤ b) :
    NoDigit g b (g * y) ↔ NoDigit g b y := by
  have := md_add_mul (x := 0) (y := y) hg hb (by omega)
  simp only [zero_add] at this
  rw [this]; exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

/-- Shift by a power of the base: for `m < g^k`, `g^k + m` misses `b` iff `m` does,
provided `b ≠ 1`. This is why `[X, X+H]^*` with `X = g^k` mirrors `(0, H]^*`. -/
theorem md_pow_add {g b : ℕ} (hg : 2 ≤ g) (hb : 2 ≤ b) :
    ∀ k m, m < g ^ k → (NoDigit g b (g ^ k + m) ↔ NoDigit g b m) := by
  intro k
  induction k with
  | zero =>
    intro m hm
    have hm0 : m = 0 := by simpa using hm
    subst hm0
    have := md_digit (d := 1) hg (by omega : 1 ≤ b) (by omega)
    simp only [pow_zero, add_zero]
    rw [this]; exact ⟨fun _ => md_zero g b, fun _ => by omega⟩
  | succ k ih =>
    intro m hm
    have hg0 : 0 < g := by omega
    have hq : m / g < g ^ k := by
      rw [Nat.div_lt_iff_lt_mul hg0]; rwa [← pow_succ]
    have e1 : g ^ (k + 1) + m = m % g + g * (g ^ k + m / g) := by
      rw [pow_succ, mul_add]
      have := Nat.mod_add_div m g
      rw [mul_comm (g ^ k) g]; omega
    have e2 : m = m % g + g * (m / g) := (Nat.mod_add_div m g).symm
    rw [e1, md_add_mul hg (by omega) (Nat.mod_lt _ hg0), ih _ hq]
    conv_rhs => rw [e2]
    rw [md_add_mul hg (by omega) (Nat.mod_lt _ hg0)]

/-- Exact count: exactly `(g-1)^k` numbers `0 ≤ n < g^k` have no digit `b` in base `g`,
for any digit `1 ≤ b < g`. -/
theorem card_md_lt_pow {g b : ℕ} (hg : 2 ≤ g) (hb : 1 ≤ b) (hbg : b < g) :
    ∀ k, ((Finset.range (g ^ k)).filter (NoDigit g b)).card = (g - 1) ^ k := by
  have hg0 : 0 < g := by omega
  intro k
  induction k with
  | zero =>
    simp only [pow_zero]
    rw [show Finset.range 1 = {0} from rfl, Finset.filter_singleton]
    simp [md_zero]
  | succ k ih =>
    let f : ℕ × ℕ → ℕ := fun p => p.1 + g * p.2
    have hset : (Finset.range (g ^ (k + 1))).filter (NoDigit g b) =
        (((Finset.range g).filter (fun x => x ≠ b)) ×ˢ
          ((Finset.range (g ^ k)).filter (NoDigit g b))).image f := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_product,
        Prod.exists, f]
      constructor
      · rintro ⟨hn, hS⟩
        have e : n = n % g + g * (n / g) := (Nat.mod_add_div n g).symm
        have hq : n / g < g ^ k := by
          rw [Nat.div_lt_iff_lt_mul hg0]; rwa [← pow_succ]
        rw [e, md_add_mul hg hb (Nat.mod_lt _ hg0)] at hS
        exact ⟨n % g, n / g, ⟨⟨Nat.mod_lt _ hg0, hS.1⟩, hq, hS.2⟩, e.symm⟩
      · rintro ⟨x, y, ⟨⟨hx, hxb⟩, hy, hyS⟩, rfl⟩
        refine ⟨?_, (md_add_mul hg hb hx).2 ⟨hxb, hyS⟩⟩
        have : g * (y + 1) ≤ g * g ^ k := Nat.mul_le_mul_left g hy
        rw [pow_succ, mul_comm (g ^ k) g]; nlinarith
    have hinj : Set.InjOn f ↑(((Finset.range g).filter (fun x => x ≠ b)) ×ˢ
          ((Finset.range (g ^ k)).filter (NoDigit g b))) := by
      rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy' he
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range]
        at hxy hxy'
      simp only [f] at he
      have h1 : x = x' := by
        have := congrArg (· % g) he
        simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hxy.1.1,
          Nat.mod_eq_of_lt hxy'.1.1] at this
        exact this
      subst h1
      have : g * y = g * y' := by omega
      exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left hg0 this)
    rw [hset, Finset.card_image_of_injOn hinj, Finset.card_product, ih, pow_succ, mul_comm]
    congr 1
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_range.2 hbg), Finset.card_range]

/-- Exact size of the paper's set for `X = g^k` and `H = g^j` with `j < k`:
`|[X, X+H]^*| = (g-1)^j = H^{log(g-1)/log g}`. -/
theorem card_starSet_pow {g b : ℕ} (hg : 2 ≤ g) (hb : 2 ≤ b) (hbg : b < g) {j k : ℕ}
    (hjk : j < k) : (starSet g b (g ^ k) ((g ^ j : ℕ) : ℝ)).card = (g - 1) ^ j := by
  have hlt : g ^ j < g ^ k := Nat.pow_lt_pow_right (by omega) hjk
  have hS : ∀ m, m ≤ g ^ j → (NoDigit g b (g ^ k + m) ↔ NoDigit g b m) :=
    fun m hm => md_pow_add hg hb k m (by omega)
  unfold starSet
  rw [Nat.floor_natCast]
  have e1 : (Finset.Ioc (g ^ k) (g ^ k + g ^ j)).filter (NoDigit g b) =
      ((Finset.Ioc 0 (g ^ j)).filter (NoDigit g b)).image (fun m => g ^ k + m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨n - g ^ k, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      rw [← hS _ (by omega), show g ^ k + (n - g ^ k) = n by omega]; exact h3
    · rintro ⟨m, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, (hS m h2).2 h3⟩
  rw [e1, Finset.card_image_of_injective _ (add_right_injective _)]
  have e2 : (Finset.range (g ^ j + 1)).filter (NoDigit g b) =
      insert 0 ((Finset.Ioc 0 (g ^ j)).filter (NoDigit g b)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hp, by omega⟩, h2⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨by omega, md_zero g b⟩
      · exact ⟨by omega, h3⟩
  have hgj : NoDigit g b (g ^ j) := by
    have := md_pow_add hg hb j 0 (by positivity); simp only [add_zero] at this
    exact this.2 (md_zero g b)
  have e3 : (Finset.range (g ^ j + 1)).filter (NoDigit g b) =
      insert (g ^ j) ((Finset.range (g ^ j)).filter (NoDigit g b)) := by
    rw [Finset.range_add_one, Finset.filter_insert]; simp [hgj]
  have c2 := congrArg Finset.card e2
  rw [e3, Finset.card_insert_of_notMem (by simp), card_md_lt_pow hg (by omega) hbg,
    Finset.card_insert_of_notMem (by simp)] at c2
  omega

/-! ### Counting links, zero sorry -/

theorem excCount_le_evenCount (g b X : ℕ) (H : ℝ) : excCount g b X H ≤ evenCount g b X H := by
  unfold excCount evenCount
  exact Finset.card_le_card (fun n hn => by
    simp only [Finset.mem_filter] at hn ⊢; exact ⟨hn.1, hn.2.1⟩)

theorem evenCount_le_card (g b X : ℕ) (H : ℝ) : evenCount g b X H ≤ (starSet g b X H).card :=
  Finset.card_filter_le _ _

theorem starSet_mono_H (g b X : ℕ) {H H' : ℝ} (h : H ≤ H') :
    starSet g b X H ⊆ starSet g b X H' := by
  intro n hn
  simp only [starSet, Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
  exact ⟨⟨hn.1.1, le_trans hn.1.2 (by have := Nat.floor_le_floor h; omega)⟩, hn.2⟩

theorem excCount_mono_H (g b X : ℕ) {H H' : ℝ} (h : H ≤ H') :
    excCount g b X H ≤ excCount g b X H' :=
  Finset.card_le_card (Finset.filter_subset_filter _ (starSet_mono_H g b X h))

/-- Binary Goldbach empties every exceptional set with `X ≥ 2`. For `X ≤ 1` the even number
`2` can lie in `[X,X+H]^*` and is not a sum of two primes. -/
theorem excCount_eq_zero_of_binaryGoldbach (hG : BinaryGoldbach) (g b : ℕ) {X : ℕ}
    (hX : 2 ≤ X) (H : ℝ) : excCount g b X H = 0 := by
  unfold excCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn ⟨he, hng⟩
  simp only [starSet, Finset.mem_filter, Finset.mem_Ioc] at hn
  have h4 : 4 ≤ n := by rcases he with ⟨r, hr⟩; omega
  exact hng (hG n he h4)

/-- An exceptional count below the even count yields an even Goldbach sum in `[X,X+H]^*`. -/
theorem exists_goldbach_of_exc_lt {g b X : ℕ} {H : ℝ} (h : excCount g b X H < evenCount g b X H) :
    ∃ n ∈ starSet g b X H, Even n ∧ IsGoldbachSum n := by
  unfold excCount evenCount at h
  obtain ⟨n, hn, hn'⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  simp only [Finset.mem_filter, not_and, not_not] at hn hn'
  exact ⟨n, hn.1, hn.2, hn' hn.1 hn.2⟩

/-- For odd `g ≥ 3`, `b ≥ 2`, `k ≥ 1` and `H ≥ 1`, the even number `g^k + 1` lies in
`[g^k, g^k+H]^*`. -/
theorem pow_add_one_mem {g b k : ℕ} (hg : 3 ≤ g) (hgo : Odd g) (hb : 2 ≤ b) (hk : 1 ≤ k)
    {H : ℝ} (hH : 1 ≤ H) : g ^ k + 1 ∈ (starSet g b (g ^ k) H).filter Even := by
  have h1 : 1 < g ^ k := Nat.one_lt_pow (by omega) (by omega)
  have hfl : 1 ≤ ⌊H⌋₊ := Nat.le_floor (by simpa using hH)
  simp only [starSet, Finset.mem_filter, Finset.mem_Ioc]
  refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, (hgo.pow).add_one⟩
  rw [md_pow_add (by omega) hb k 1 h1, md_digit (by omega) (by omega) (by omega)]
  omega

/-! ### Links between the statements, zero sorry -/

theorem pow_ge_one_real {g k : ℕ} (hg : 1 ≤ g) : (1 : ℝ) ≤ ((g ^ k : ℕ) : ℝ) := by
  exact_mod_cast Nat.one_le_pow _ _ hg

/-- Binary Goldbach implies the conclusion of Theorem 1.2 for every exponent. -/
theorem almostAll_of_binaryGoldbach (hG : BinaryGoldbach) (a : ℝ) : AlmostAllGoldbach a := by
  intro ε _
  refine ⟨2, fun g b hg _ _ A₁ A₂ _ _ η hη => ⟨1, fun k H hk _ _ => ?_⟩⟩
  have hX : 2 ≤ g ^ k := le_trans hg (Nat.le_self_pow (by omega) g)
  rw [excCount_eq_zero_of_binaryGoldbach hG g b hX H, Nat.cast_zero]
  positivity

/-- Theorem 1.2 shape is monotone in the exponent. -/
theorem almostAll_mono {a a' : ℝ} (haa : a ≤ a') (h : AlmostAllGoldbach a) :
    AlmostAllGoldbach a' := by
  intro ε hε
  obtain ⟨g₀, hg₀⟩ := h ε hε
  refine ⟨g₀, fun g b hg hb hbg A₁ A₂ hA₁ hA₂ η hη => ?_⟩
  obtain ⟨K₀, hK⟩ := hg₀ g b hg hb hbg A₁ A₂ hA₁ hA₂ η hη
  refine ⟨K₀, fun k H hk h1 h2 => hK k H hk (le_trans ?_ h1) h2⟩
  have hX : (1 : ℝ) ≤ ((g ^ k : ℕ) : ℝ) := pow_ge_one_real (by omega)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) hA₁.le

/-- Theorem 1.1 shape is monotone in the exponent and in the log power. -/
theorem d4Bound_mono {a a' : ℝ} {j j' : ℕ} (haa : a ≤ a') (hjj : j ≤ j') (h : D4Bound a j) :
    D4Bound a' j' := by
  intro ε hε
  obtain ⟨g₀, hg₀⟩ := h ε hε
  refine ⟨max g₀ 2, fun g b hg hb hbg A₁ A₂ hA₁ hA₂ => ?_⟩
  have hg2 : 2 ≤ g := le_trans (le_max_right _ _) hg
  obtain ⟨C, K₀, hK⟩ := hg₀ g b (le_trans (le_max_left _ _) hg) hb hbg A₁ A₂ hA₁ hA₂
  refine ⟨max C 0, max K₀ 1, fun k H hk h1 h2 => ?_⟩
  have hX : (1 : ℝ) ≤ ((g ^ k : ℕ) : ℝ) := pow_ge_one_real (by omega)
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  have hlog1 : 1 ≤ Real.log ((g ^ k : ℕ) : ℝ) := by
    have h3 : (3 : ℝ) ≤ ((g ^ k : ℕ) : ℝ) := by
      have : 3 ≤ g ^ k := le_trans (by omega : 3 ≤ g) (Nat.le_self_pow (by omega) g)
      exact_mod_cast this
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hb1 := hK k H (le_trans (le_max_left _ _) hk) (le_trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) hA₁.le) h1) h2
  have hcard : (0 : ℝ) ≤ (starSet g b (g ^ k) H).card := Nat.cast_nonneg _
  have hpow : Real.log ((g ^ k : ℕ) : ℝ) ^ j ≤ Real.log ((g ^ k : ℕ) : ℝ) ^ j' :=
    pow_le_pow_right₀ hlog1 hjj
  have hlogj : 0 ≤ Real.log ((g ^ k : ℕ) : ℝ) ^ j := by positivity
  calc _ ≤ C * Real.log ((g ^ k : ℕ) : ℝ) ^ j * (starSet g b (g ^ k) H).card := hb1
    _ ≤ max C 0 * Real.log ((g ^ k : ℕ) : ℝ) ^ j * (starSet g b (g ^ k) H).card := by
        gcongr; exact le_max_left _ _
    _ ≤ max C 0 * Real.log ((g ^ k : ℕ) : ℝ) ^ j' * (starSet g b (g ^ k) H).card := by
        gcongr

/-- Theorem 1.2 shape with a nonnegative exponent gives an even Goldbach sum in every
admissible `[X, X+H]^*` for odd bases. -/
theorem existsGoldbachOddBase_of_almostAll {a : ℝ} (ha : 0 ≤ a) (h : AlmostAllGoldbach a) :
    ExistsGoldbachOddBase a := by
  intro ε hε
  obtain ⟨g₀, hg₀⟩ := h ε hε
  refine ⟨g₀, fun g b hg hgo hb hbg => ?_⟩
  obtain ⟨K₀, hK⟩ := hg₀ g b hg hb hbg 1 1 one_pos one_pos (1 / 2) (by norm_num)
  refine ⟨max K₀ 1, fun k H hk h1 h2 => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  have hX : (1 : ℝ) ≤ ((g ^ k : ℕ) : ℝ) := pow_ge_one_real (by omega)
  have hH : 1 ≤ H := le_trans (Real.one_le_rpow hX (by linarith)) h1
  have hexc := hK k H (le_trans (le_max_left _ _) hk) (by rwa [one_mul])
    (by rwa [one_mul])
  have hpos : 0 < evenCount g b (g ^ k) H :=
    Finset.card_pos.2 ⟨_, pow_add_one_mem (by omega) hgo hb hk1 hH⟩
  apply exists_goldbach_of_exc_lt
  have : (0 : ℝ) < evenCount g b (g ^ k) H := by exact_mod_cast hpos
  exact_mod_cast (show (excCount g b (g ^ k) H : ℝ) < evenCount g b (g ^ k) H by linarith)

/-! ### Small cases, kernel checked, zero sorry -/

/-- Digits of `1004` in base `10` contain no `3`. -/
theorem nd_1004 : NoDigit 10 3 1004 := by decide +kernel

/-- `1004 = 7 + 997`, an even element of `[1000, 1000+H]^*` for base 10 missing digit 3,
`H ≥ 4`, written as a sum of two primes. -/
theorem goldbach_1004 : IsGoldbachSum 1004 := ⟨7, 997, by norm_num, by norm_num, rfl⟩

/-- Exact count, kernel checked: 81 = 9^2 numbers below 100 have no digit 3 in base 10. -/
theorem card_nd_lt_100 : ((Finset.range 100).filter (NoDigit 10 3)).card = 81 := by
  decide +kernel

/-- Exact count, kernel checked: base 3 missing digit 2, 8 = 2^3 numbers below 27. -/
theorem card_nd_base3 : ((Finset.range 27).filter (NoDigit 3 2)).card = 8 := by decide +kernel

/-- Kernel check of `|[100, 110]^*| = 9` for base 10 missing digit 3, matching
`card_starSet_pow` with `k = 2`, `j = 1`. -/
theorem card_Ioc_100_110 : ((Finset.Ioc 100 110).filter (NoDigit 10 3)).card = 9 := by
  decide +kernel

theorem card_starSet_100_10 : (starSet 10 3 (10 ^ 2) ((10 ^ 1 : ℕ) : ℝ)).card = 9 :=
  card_starSet_pow (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Every even number in `[100, 200]^*`, base 10, missing digit 3, is a sum of two primes. -/
theorem goldbach_starSet_100_100 :
    ∀ n ∈ starSet 10 3 100 (100 : ℝ), Even n → IsGoldbachSum n := by
  have hall := allEvenGB_sound 200 (by decide +kernel)
  intro n hn he
  have hfl : ⌊(100 : ℝ)⌋₊ = 100 := Nat.floor_ofNat 100
  simp only [starSet, Finset.mem_filter, Finset.mem_Ioc, hfl] at hn
  exact hall n he (by omega) (by omega)

theorem excCount_100_100 : excCount 10 3 100 (100 : ℝ) = 0 := by
  unfold excCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun n hn ⟨he, hng⟩ => hng (goldbach_starSet_100_100 n hn he)

/-- `d₂(12) = 6` and `d₄(4) = 10`, kernel checked. -/
theorem dk_small : dk 2 12 = 6 ∧ dk 4 4 = 10 := by decide +kernel

end LeanLab.MissingDigit
