/-
I-0095, T2 FRONTIER, unit U-1337, PC run 20261021T0203Z-29730.

Goldbach numbers in short intervals CONDITIONAL ON the 7/8 half-plane `HalfPlane78`,
OpenAI, The Quasi-Riemann Hypothesis, 30 Sep 2026, Theorem 1.1, p. 4, unrefereed.

* `HalfPlane78`: no zero of any Dirichlet `L(s, χ)` in `Re s > 7/8`, pole of principal `χ` at 1
  excepted. Same shape as `Ternary78.Threshold.HalfPlane78` with no bound on the modulus.
* Route a. `ExplicitShort78`, CITED input: the half-plane gives a prime in every `(x, x + x^{7/8+ε}]`
  for large `x`, truncated explicit formula. `goldbach_of_primesAll`: PROVED, primes in all
  intervals of exponent `θ` give Goldbach numbers `p + 3` in all intervals of exponent `θ`.
  `goldbach_short_a`: CONDITIONAL ON `HalfPlane78`, `ExplicitShort78`, exponent `7/8 + ε`.
* Route b. `goldbach_of_counts`: PROVED, the combinatorial step: if fewer `z ∈ [Y, 2Y]` have a
  prime free `[z, z + H]` than there are primes in `[x - 2Y, x - Y]`, some `n ∈ [x, x + H]` is a
  Goldbach number. `goldbach_short_b`: PROVED from the two named count inputs `WindowCount`,
  `AlmostAllCount`, any exponents, giving `[x, x + 3 x^{ab}]`. `goldbach_short_b78`: CONDITIONAL ON
  `HalfPlane78`, `MeanSquare78`, exponent `(7/8 + ε)(3/4 + ε)`, i.e. `21/32 + O(ε)`.
* Exponent arithmetic: `21/32`, the RH sanity check `θ₀ = 1/2 ↦ 0`, the Guth-Maynard
  numbers `30/13`, `17/30`, `2/15` and the fact that the density maximum `σ = 7/10` lies below
  `7/8`, so the half-plane does not touch the binding range.

AI-written Lean code, Claude, unit U-1337. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.GoldbachShort78
open Real

/-! ### Definitions and named inputs -/

/-- **The 7/8 half-plane**, CITED, OpenAI 30 Sep 2026 Theorem 1.1, unrefereed. -/
def HalfPlane78 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    7 / 8 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- A Goldbach number: an even sum of two primes. -/
def IsGoldbachNumber (n : ℕ) : Prop := Even n ∧ IsGoldbachSum n

/-- A prime in every interval `(x, x + x^θ]`, `x ≥ x₀`. -/
def PrimesAll (θ x₀ : ℝ) : Prop :=
  ∀ x : ℝ, x₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ θ

/-- **Cited input, route a**: the truncated explicit formula with every zero in `Re s ≤ 7/8`
gives `ψ(x + h) − ψ(x) = h + O(x^{7/8} log² x)`, hence a prime in `(x, x + x^{7/8+ε}]`. -/
def ExplicitShort78 : Prop :=
  HalfPlane78 → ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, PrimesAll (7 / 8 + ε) x₀

/-- The primes in `[x − 2Y, x − Y]`. -/
noncomputable def primeWindow (x Y : ℕ) : Finset ℕ :=
  (Finset.Icc (x - 2 * Y) (x - Y)).filter Nat.Prime

/-- The `z ∈ [Y, 2Y]` with no prime in `[z, z + H]`. -/
noncomputable def badSet (Y H : ℕ) : Finset ℕ :=
  (Finset.Icc Y (2 * Y)).filter (fun z => ∀ q ∈ Finset.Icc z (z + H), ¬ q.Prime)

/-- **Count input, all intervals**: for `x ≥ x₀` and `Y ≥ x^a` with `2Y + 3 ≤ x`, the window
`[x − 2Y, x − Y]` holds at least `c Y / log x` primes. -/
def WindowCount (a c x₀ : ℝ) : Prop :=
  ∀ x : ℕ, x₀ ≤ x → ∀ Y : ℕ, (x : ℝ) ^ a ≤ Y → 2 * Y + 3 ≤ x →
    c * Y / Real.log x ≤ (primeWindow x Y).card

/-- **Count input, almost all intervals**: for `Y ≥ y₀` and `H ≥ Y^b`, at most `Y / log² Y` of the
`z ∈ [Y, 2Y]` have a prime free `[z, z + H]`. -/
def AlmostAllCount (b y₀ : ℝ) : Prop :=
  ∀ Y : ℕ, y₀ ≤ Y → ∀ H : ℕ, (Y : ℝ) ^ b ≤ H → ((badSet Y H).card : ℝ) ≤ Y / Real.log Y ^ 2

/-- **Cited input, route b**: the half-plane, through the explicit formula and the
Saffari-Vaughan mean square with only `N(T) ≪ T log T` zeros, gives both counts with
`a = 7/8 + ε`, `c = 1/2`, and `b = 2·(7/8) − 1 + ε = 3/4 + ε`. -/
def MeanSquare78 : Prop :=
  HalfPlane78 → ∀ ε : ℝ, 0 < ε → ∃ x₀ y₀ : ℝ,
    WindowCount (7 / 8 + ε) (1 / 2) x₀ ∧ AlmostAllCount (3 / 4 + ε) y₀

/-! ### Route a -/

/-- `p + 3` is a Goldbach number when `p > 3` is prime. -/
theorem goldbach_add_three {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : IsGoldbachNumber (p + 3) := by
  refine ⟨?_, p, 3, hp, Nat.prime_three, rfl⟩
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  exact hodd.add_odd (by decide)

/-- **Route a, combinatorial step**, PROVED: primes in all intervals of exponent `θ ≥ 0` give a
Goldbach number in every `(x, x + x^θ]`, `x ≥ max (x₀ + 3) 7`. -/
theorem goldbach_of_primesAll {θ x₀ : ℝ} (hθ : 0 ≤ θ) (h : PrimesAll θ x₀) :
    ∀ x : ℝ, max (x₀ + 3) 7 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + x ^ θ := by
  intro x hx
  have hx1 : x₀ + 3 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (7 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨p, hp, h1, h2⟩ := h (x - 3) (by linarith)
  have hp3 : 3 < p := by
    have : (3 : ℝ) < p := by linarith
    exact_mod_cast this
  refine ⟨p + 3, goldbach_add_three hp hp3, ?_, ?_⟩
  · push_cast; linarith
  · have hpow : (x - 3) ^ θ ≤ x ^ θ := Real.rpow_le_rpow (by linarith) (by linarith) hθ
    push_cast; linarith

/-- **Route a**, CONDITIONAL ON `HalfPlane78`, `ExplicitShort78`: a Goldbach number in every
`(x, x + x^{7/8+ε}]` for large `x`. -/
theorem goldbach_short_a (h78 : HalfPlane78) (hin : ExplicitShort78) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + x ^ (7 / 8 + ε) := by
  obtain ⟨x₀, hx₀⟩ := hin h78 ε hε
  exact ⟨_, goldbach_of_primesAll (by linarith) hx₀⟩

/-! ### Route b -/

/-- **Route b, combinatorial step**, PROVED unconditional. -/
theorem goldbach_of_counts {x Y H : ℕ} (hY : 3 ≤ Y) (hx : 2 * Y + 3 ≤ x)
    (hcount : (badSet Y H).card < (primeWindow x Y).card) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧ n ≤ x + H := by
  by_contra hne
  push Not at hne
  have hmaps : ∀ p ∈ primeWindow x Y, x - p ∈ badSet Y H := by
    intro p hp
    simp only [primeWindow, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hp2⟩, hpp⟩ := hp
    simp only [badSet, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro q hq hqp
    obtain ⟨hq1, hq2⟩ := hq
    have hpodd : Odd p := hpp.odd_of_ne_two (by omega)
    have hqodd : Odd q := hqp.odd_of_ne_two (by omega)
    have hG : IsGoldbachNumber (p + q) := ⟨hpodd.add_odd hqodd, p, q, hpp, hqp, rfl⟩
    have := hne (p + q) hG (by omega)
    omega
  have hinj : Set.InjOn (fun p => x - p) (primeWindow x Y : Set ℕ) := by
    intro p hp p' hp' h
    simp only [Finset.coe_filter, Finset.mem_Icc, primeWindow, Set.mem_ofPred_eq] at hp hp'
    simp only at h
    omega
  have := Finset.card_le_card_of_injOn (fun p => x - p) hmaps hinj
  omega

/-- **Route b from the two counts**, PROVED from `WindowCount a c x₀` and `AlmostAllCount b y₀`,
with explicit side conditions true for large `x`: a Goldbach number in `[x, x + 3 x^{ab}]`. -/
theorem goldbach_short_b {a b c x₀ y₀ : ℝ} (ha : 0 < a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc : 0 < c) (hW : WindowCount a c x₀) (hA : AlmostAllCount b y₀) {x : ℕ}
    (hx0 : x₀ ≤ x) (hxy : y₀ ≤ (x : ℝ) ^ a) (h3 : 3 ≤ (x : ℝ) ^ a)
    (hlog : 1 < c * a ^ 2 * Real.log x) (hsize : 2 * ⌈(x : ℝ) ^ a⌉₊ + 3 ≤ x) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧ (n : ℝ) ≤ x + 3 * (x : ℝ) ^ (a * b) := by
  set Y : ℕ := ⌈(x : ℝ) ^ a⌉₊ with hYdef
  set H : ℕ := ⌈(Y : ℝ) ^ b⌉₊ with hHdef
  have hxa_le : (x : ℝ) ^ a ≤ Y := Nat.le_ceil _
  have hYlt : (Y : ℝ) < (x : ℝ) ^ a + 1 := Nat.ceil_lt_add_one (by linarith)
  have hY3 : 3 ≤ Y := by
    have : (3 : ℝ) ≤ Y := le_trans h3 hxa_le
    exact_mod_cast this
  have hYpos : (0 : ℝ) < Y := by linarith
  have hlogx : 0 < Real.log x := by
    by_contra hneg; push Not at hneg
    have : c * a ^ 2 * Real.log x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have hxpos : (0 : ℝ) < x := by
    have : (x : ℝ) ≠ 0 := by intro h0; rw [h0, Real.log_zero] at hlogx; exact lt_irrefl _ hlogx
    positivity
  -- the two counts
  have hwin := hW x hx0 Y hxa_le hsize
  have hbad := hA Y (le_trans hxy hxa_le) H (Nat.le_ceil _)
  -- compare Y / log² Y < c Y / log x
  have hlogY : a * Real.log x ≤ Real.log Y := by
    rw [← Real.log_rpow hxpos]
    exact Real.log_le_log (by positivity) hxa_le
  have hal : 0 < a * Real.log x := mul_pos ha hlogx
  have hsq : (a * Real.log x) ^ 2 ≤ Real.log Y ^ 2 := pow_le_pow_left₀ hal.le hlogY 2
  have hkey : Real.log x < c * (a * Real.log x) ^ 2 := by
    have : c * (a * Real.log x) ^ 2 = (c * a ^ 2 * Real.log x) * Real.log x := by ring
    rw [this]; nlinarith
  have hlt : (Y : ℝ) / Real.log Y ^ 2 < c * Y / Real.log x := by
    have hLY : 0 < Real.log Y ^ 2 := lt_of_lt_of_le (by positivity) hsq
    rw [div_lt_div_iff₀ hLY hlogx]
    have : c * (a * Real.log x) ^ 2 ≤ c * Real.log Y ^ 2 := mul_le_mul_of_nonneg_left hsq hc.le
    nlinarith
  have hcount : (badSet Y H).card < (primeWindow x Y).card := by
    have : ((badSet Y H).card : ℝ) < (primeWindow x Y).card := by linarith
    exact_mod_cast this
  obtain ⟨n, hn, h1, h2⟩ := goldbach_of_counts hY3 hsize hcount
  refine ⟨n, hn, h1, ?_⟩
  -- H ≤ 3 x^{ab}
  have hx1 : (1 : ℝ) ≤ x := by
    by_contra hlt1; push Not at hlt1
    have : Real.log x < 0 := Real.log_neg hxpos hlt1
    linarith
  have hxab : (1 : ℝ) ≤ (x : ℝ) ^ (a * b) := Real.one_le_rpow hx1 (by positivity)
  have hH : (H : ℝ) < (Y : ℝ) ^ b + 1 := Nat.ceil_lt_add_one (by positivity)
  have hYb : (Y : ℝ) ^ b ≤ (2 * (x : ℝ) ^ a) ^ b :=
    Real.rpow_le_rpow hYpos.le (by linarith) hb0
  have h2b : (2 : ℝ) ^ b ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hb1
    simpa using this
  have hsplit : (2 * (x : ℝ) ^ a) ^ b = (2 : ℝ) ^ b * (x : ℝ) ^ (a * b) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hxpos.le]
  have h2le : (2 * (x : ℝ) ^ a) ^ b ≤ 2 * (x : ℝ) ^ (a * b) := by
    rw [hsplit]; exact mul_le_mul_of_nonneg_right h2b (by positivity)
  have : (n : ℝ) ≤ x + H := by exact_mod_cast h2
  linarith

/-- **Route b**, CONDITIONAL ON `HalfPlane78`, `MeanSquare78`: for `0 < ε ≤ 1/4` there are
`x₀, y₀` such that every natural `x` meeting the elementary side conditions has a Goldbach number
in `[x, x + 3 x^{(7/8+ε)(3/4+ε)}]`. -/
theorem goldbach_short_b78 (h78 : HalfPlane78) (hin : MeanSquare78) {ε : ℝ} (hε : 0 < ε)
    (hε4 : ε ≤ 1 / 4) :
    ∃ x₀ y₀ : ℝ, ∀ x : ℕ, x₀ ≤ x → y₀ ≤ (x : ℝ) ^ (7 / 8 + ε) → 3 ≤ (x : ℝ) ^ (7 / 8 + ε) →
      1 < 1 / 2 * (7 / 8 + ε) ^ 2 * Real.log x → 2 * ⌈(x : ℝ) ^ (7 / 8 + ε)⌉₊ + 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧
        (n : ℝ) ≤ x + 3 * (x : ℝ) ^ ((7 / 8 + ε) * (3 / 4 + ε)) := by
  obtain ⟨x₀, y₀, hW, hA⟩ := hin h78 ε hε
  exact ⟨x₀, y₀, fun x h0 h1 h2 h3 h4 =>
    goldbach_short_b (by linarith) (by linarith) (by linarith) (by norm_num) hW hA h0 h1 h2 h3 h4⟩

/-! ### Exponent arithmetic -/

/-- Route b exponent from a zero-free half-plane `Re s > θ₀` alone: `θ₀ (2θ₀ − 1)`. -/
noncomputable def thetaB (θ₀ : ℝ) : ℝ := θ₀ * (2 * θ₀ - 1)

theorem thetaB_78 : thetaB (7 / 8) = 21 / 32 := by unfold thetaB; norm_num

/-- RH sanity check: at `θ₀ = 1/2` the exponent is `0`, matching the `log² x` intervals. -/
theorem thetaB_half : thetaB (1 / 2) = 0 := by unfold thetaB; norm_num

/-- The `ε` version: `(7/8 + ε)(3/4 + ε) = 21/32 + (13/8) ε + ε²`. -/
theorem exponent_b_eps (ε : ℝ) : (7 / 8 + ε) * (3 / 4 + ε) = 21 / 32 + 13 / 8 * ε + ε ^ 2 := by
  ring

/-- Route b beats route a, and both lose to Baker-Harman-Pintz `0.525` fed into route a,
and to Cai's unconditional `11/400`. -/
theorem compare_records : (11 : ℝ) / 400 < 0.525 ∧ (0.525 : ℝ) < 21 / 32 ∧ (21 : ℝ) / 32 < 7 / 8 := by
  norm_num

/-- Guth-Maynard: Ingham's `3/(2 − σ)` meets `30/13` at `σ = 7/10`, below `7/8`. -/
theorem gm_peak : (3 : ℝ) / (2 - 7 / 10) = 30 / 13 ∧ (7 : ℝ) / 10 < 7 / 8 := by norm_num

/-- `1 − 1/A = 17/30` and `1 − 2/A = 2/15` at `A = 30/13`; their product `17/225`. -/
theorem gm_exponents : (1 : ℝ) - 1 / (30 / 13) = 17 / 30 ∧ (1 : ℝ) - 2 / (30 / 13) = 2 / 15 ∧
    (17 : ℝ) / 30 * (2 / 15) = 17 / 225 := by norm_num

/-- Products seen in the literature pattern: Cai `11/20 · 1/20 = 11/400`, Jia `7/12 · 1/20 = 7/240`,
and `0.525 / 21.5 = 21/860` from Baker-Harman-Pintz and R. Li's `1/21.5`. -/
theorem product_pattern : (11 : ℝ) / 20 * (1 / 20) = 11 / 400 ∧ (7 : ℝ) / 12 * (1 / 20) = 7 / 240 ∧
    (0.525 : ℝ) * (1 / 21.5) = 21 / 860 ∧ (21 : ℝ) / 860 < 11 / 400 := by norm_num

/-! ### Vacuity tests -/

/-- `HalfPlane78` is a genuine statement: its hypotheses hold at `q = 1`, `χ = 1`, `s = 2`. -/
theorem halfPlane78_instance : (7 : ℝ) / 8 < (2 : ℂ).re ∧ ((1 : DirichletCharacter ℂ 1) ≠ 1 ∨ (2 : ℂ) ≠ 1) := by
  refine ⟨by norm_num, Or.inr (by norm_num)⟩

/-- Vacuity test for `goldbach_of_counts` at `x = 9`, `Y = 3`, `H = 2`: the window `[3, 6]` holds
the primes 3 and 5, and every `[z, z + 2]` with `3 ≤ z ≤ 6` holds a prime, so `badSet 3 2 = ∅`. -/
theorem counts_instance : (badSet 3 2).card < (primeWindow 9 3).card := by
  decide +kernel

/-- The conclusion at that instance: a Goldbach number in `[9, 11]`. -/
theorem counts_instance_goldbach : ∃ n : ℕ, IsGoldbachNumber n ∧ 9 ≤ n ∧ n ≤ 9 + 2 :=
  goldbach_of_counts (by norm_num) (by norm_num) counts_instance

end LeanLab.GoldbachShort78
