/-
AI-written Lean code, Claude, 2026-10-21, PC run 20261021T1103Z-29422, unit U-1405.
P0020 P. J. Campbell 2026, A Sharper Explicit Result for the Sum of Two Almost Primes,
arXiv 2608.09488 v1, re-read on arxiv.org/html/2608.09488 this run, Section 4, Lemma 4.2:
for `z ≥ z₁ = 10^8`, `V(z) ≥ 1.241/log² z`, where `V(z) = ∏_{p < z, p ≠ 3} (1 - g(p))`,
`g(2) = 1/2`, `g(p) = 2/p` for odd `p ∤ N`, `g(p) = 1/p` for odd `p ∣ N`.

The paper's route: Rosser-Schoenfeld 1962 Theorem 5 for the tail `10^8 ≤ p < z` and a finite
computation of `½ ∏_{5 ≤ p < 10^8} (1 - 2/p) = 0.00367979…`, too large for the kernel.

Route here, different input, no finite computation beyond `p < 1000`:
`1 - 2/p = (1 - 1/(p-1)²)(1 - 1/p)²`, so with `A = {5 ≤ p < z}`
`∏_A (1 - 2/p) = ∏_A (1 - 1/(p-1)²) · (∏_A (1 - 1/p))²`.
* `∏_A (1 - 1/(p-1)²) ≥ 0.88032 · 998/999`: the primes below 1000 by a kernel checked integer
  chain, the primes from 1000 on by the telescoping product over all integers.
* `∏_A (1 - 1/p) ≥ 3 ∏_{p ≤ z} (1 - 1/p) > 3 e^{-γ}/log z · (1 - 1/(2 log² z))` by
  **Rosser-Schoenfeld 1962, Theorem 7, eq (3.25), p. 70**, for `285 ≤ x`, cited as `RS325`.
* `e^{-2γ} ≥ 1024² (1 - r)/2.7182818286^15` from Mathlib's `γ < H₁₀₂₄ - log 1024`, with
  `H₁₀₂₄` bounded by a kernel checked integer sum, `r = 2 H⁺ - 15`.
Product: `V(z) log² z ≥ 4.5 · 0.88032 · 998/999 · e^{-2γ}⁻ · (1 - 1/(2 · 18.4192²))² > 1.241`;
Python margin 1.24245 against 1.241.

PROVED, no cited input: `chain_le`, `cov_sound`, `K_low`, `tele`, `K_high`, `K_bound`,
`Q_bound_of`, `gamma_sq_bound`, `factor_split`, `final_const`, `rs325_at_1000` (vacuity check:
eq (3.25) holds at `x = 1000`).
CONDITIONAL ON `RS325`: `lemma42_of_RS325`, the cited `CampbellCase3X.Lemma42`.
CONDITIONAL ON `Thm21Case3 R4`, `RS325`, `Lemma43 R4`: `case3Sieve_of_RS`.
CONDITIONAL ON `GapTable`, `Case2Sieve`, `Case2Table`, `Thm21Case3 R4`, `RS325`, `Lemma43 R4`:
`theorem1_2_of_inputs_RS`.
Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.CampbellCase3X
import LeanLab.AlmostPrimes.RS1962

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimes.CampbellLemma42
open LeanLab.AlmostPrimes Campbell2026 CampbellCase3 CampbellCase2 CampbellCase2X CampbellCase3X

/-! ### The cited input -/

/-- **Rosser-Schoenfeld 1962, Theorem 7, eq (3.25), p. 70.**
Plain math: for every real `x ≥ 285`,
`e^{-C}/log x · (1 - 1/(2 log² x)) < ∏_{p ≤ x} (1 - 1/p)`, with `C` Euler's constant, here
Mathlib's `Real.eulerMascheroniConstant`. Cited. -/
def RS325 : Prop := ∀ x : ℝ, 285 ≤ x →
  exp (-eulerMascheroniConstant) / log x * (1 - 1 / (2 * log x ^ 2)) <
    ∏ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

/-! ### Generic product lemmas -/

lemma prod_le_of_sub {s t : Finset ℕ} {f : ℕ → ℝ} (h : s ⊆ t) (h0 : ∀ i ∈ t, 0 ≤ f i)
    (h1 : ∀ i ∈ t, f i ≤ 1) : ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
  rw [← prod_sdiff h]
  have a : ∏ i ∈ t \ s, f i ≤ 1 :=
    prod_le_one₀ (fun i hi => h0 i (mem_sdiff.1 hi).1) (fun i hi => h1 i (mem_sdiff.1 hi).1)
  have b : 0 ≤ ∏ i ∈ s, f i := prod_nonneg (fun i hi => h0 i (h hi))
  exact mul_le_of_le_one_left b a

/-- A floor chain: `m ↦ ⌊m · a(p) / b(p)⌋` along a list. -/
def chain (a b : ℕ → ℕ) : List ℕ → ℕ → ℕ
  | [], m => m
  | p :: l, m => chain a b l (m * a p / b p)

/-- **The chain is a lower bound, PROVED.** -/
theorem chain_le (a b : ℕ → ℕ) : ∀ (l : List ℕ) (m : ℕ),
    (chain a b l m : ℝ) ≤ m * (l.map (fun p => (a p : ℝ) / b p)).prod
  | [], m => by simp [chain]
  | p :: l, m => by
    simp only [chain, List.map_cons, List.prod_cons]
    have ih := chain_le a b l (m * a p / b p)
    have hfl : ((m * a p / b p : ℕ) : ℝ) ≤ m * ((a p : ℝ) / b p) := by
      have := Nat.cast_div_le (α := ℝ) (m := m * a p) (n := b p)
      push_cast at this
      rw [mul_div_assoc] at this
      exact this
    have hP : 0 ≤ (l.map (fun p => (a p : ℝ) / b p)).prod :=
      List.prod_nonneg (by simp only [List.mem_map]; rintro _ ⟨q, _, rfl⟩; positivity)
    calc _ ≤ _ := ih
      _ ≤ m * ((a p : ℝ) / b p) * (l.map (fun p => (a p : ℝ) / b p)).prod :=
          mul_le_mul_of_nonneg_right hfl hP
      _ = _ := by ring

/-! ### The primes below 1000 -/

/-- The primes `5 ≤ p < 1000`. -/
def pl5 : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
  83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
  191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283,
  293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
  419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523,
  541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647,
  653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773,
  787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911,
  919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997]

/-- The primes `p < 1000`. -/
def pl : List ℕ := 2 :: 3 :: pl5

/-- Kernel check: every `2 ≤ m ≤ 1000` outside `pl` has a divisor `2 ≤ d < m`. -/
theorem cov_check : ∀ m, m < 1001 → 2 ≤ m → m ∉ pl → ∃ d, d < m ∧ (2 ≤ d ∧ m % d = 0) := by
  decide +kernel

theorem pl5_ge : ∀ p ∈ pl5, 5 ≤ p := by decide +kernel

theorem pl_nodup : pl.Nodup := by decide +kernel

theorem pl5_nodup : pl5.Nodup := by
  have := pl_nodup
  unfold pl at this
  exact (List.nodup_cons.1 (List.nodup_cons.1 this).2).2

/-- **Coverage, PROVED**: every prime `p ≤ 1000` is in `pl`. -/
theorem cov_sound {p : ℕ} (hp : p.Prime) (h : p ≤ 1000) : p ∈ pl := by
  by_contra hn
  obtain ⟨d, hd, h2, hm⟩ := cov_check p (by omega) hp.two_le hn
  have hdv : d ∣ p := Nat.dvd_of_mod_eq_zero hm
  rcases hp.eq_one_or_self_of_dvd d hdv with h' | h' <;> omega

theorem cov5_sound {p : ℕ} (hp : p.Prime) (h : p < 1000) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    p ∈ pl5 := by
  have := cov_sound hp h.le
  unfold pl at this
  simp only [List.mem_cons] at this
  rcases this with h' | h' | h'
  · exact absurd h' h2
  · exact absurd h' h3
  · exact h'

/-! ### The twin factor `1 - 1/(p-1)²` -/

/-- `f₁(p) = 1 - 1/(p-1)²`. -/
def f1 (p : ℕ) : ℝ := 1 - 1 / ((p : ℝ) - 1) ^ 2

/-- `f₂(p) = 1 - 1/p`. -/
def f2 (p : ℕ) : ℝ := 1 - 1 / (p : ℝ)

lemma f1_bounds {p : ℕ} (hp : 3 ≤ p) : 0 ≤ f1 p ∧ f1 p ≤ 1 := by
  unfold f1
  have h : (2 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have h1 : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have h0 : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
  constructor <;> linarith

lemma f2_bounds {p : ℕ} (hp : 1 ≤ p) : 0 ≤ f2 p ∧ f2 p ≤ 1 := by
  unfold f2
  have h : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact h
  have h0 : 0 ≤ 1 / (p : ℝ) := by positivity
  constructor <;> linarith

/-- `1 - 2/p = (1 - 1/(p-1)²)(1 - 1/p)²` for `p ≥ 2`. -/
lemma factor_split {p : ℕ} (hp : 2 ≤ p) : 1 - 2 / (p : ℝ) = f1 p * f2 p ^ 2 := by
  unfold f1 f2
  have h : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h0 : (p : ℝ) ≠ 0 := by linarith
  field_simp
  ring

def a1 (p : ℕ) : ℕ := (p - 1) ^ 2 - 1
def b1 (p : ℕ) : ℕ := (p - 1) ^ 2

lemma frac1 {p : ℕ} (hp : 2 ≤ p) : (a1 p : ℝ) / b1 p = f1 p := by
  unfold a1 b1 f1
  have hq : 1 ≤ (p - 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub hq]
  push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
  have h : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : ((p : ℝ) - 1) ^ 2 ≠ 0 := by
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    positivity
  rw [one_sub_div h1]

/-- The scale of the chains. -/
def CR : ℕ := 10 ^ 30

/-- Kernel check of the chain for `∏_{5 ≤ p < 1000} (1 - 1/(p-1)²)`. -/
theorem chain1_check : 88032 * 10 ^ 25 ≤ chain a1 b1 pl5 CR := by decide +kernel

/-- **`∏_{5 ≤ p < 1000} (1 - 1/(p-1)²) ≥ 0.88032`, PROVED.** -/
theorem K_low : (0.88032 : ℝ) ≤ ∏ p ∈ pl5.toFinset, f1 p := by
  rw [List.prod_toFinset _ pl5_nodup]
  have hc := chain_le a1 b1 pl5 CR
  have hm : pl5.map (fun p => (a1 p : ℝ) / b1 p) = pl5.map f1 :=
    List.map_congr_left (fun p hp => frac1 (by have := pl5_ge p hp; omega))
  rw [hm] at hc
  have hk : ((88032 * 10 ^ 25 : ℕ) : ℝ) ≤ (chain a1 b1 pl5 CR : ℝ) := by
    exact_mod_cast chain1_check
  have hCR : (CR : ℝ) = 10 ^ 30 := by unfold CR; push_cast; ring
  rw [hCR] at hc
  push_cast at hk
  nlinarith

/-- **Telescoping, PROVED**: `∏_{a ≤ m < b} (1 - 1/(m-1)²) = (a-2)(b-1)/((a-1)(b-2))`. -/
theorem tele (a : ℕ) (ha : 3 ≤ a) : ∀ b, a ≤ b →
    ∏ m ∈ Ico a b, f1 m = ((a : ℝ) - 2) * ((b : ℝ) - 1) / (((a : ℝ) - 1) * ((b : ℝ) - 2)) := by
  have hA : (3 : ℝ) ≤ a := by exact_mod_cast ha
  intro b hab
  induction b, hab using Nat.le_induction with
  | base =>
    simp only [Ico_self, prod_empty]
    have h1 : (a : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (a : ℝ) - 2 ≠ 0 := by linarith
    field_simp
  | succ b hab ih =>
    rw [prod_Ico_succ_top hab, ih]
    have hB : (3 : ℝ) ≤ b := by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    unfold f1
    push_cast
    have h1 : (a : ℝ) - 1 ≠ 0 := by linarith
    have h3 : (b : ℝ) - 1 ≠ 0 := by linarith
    have h4 : (b : ℝ) - 2 ≠ 0 := by linarith
    have h5 : (b : ℝ) + 1 - 2 ≠ 0 := by linarith
    field_simp
    ring

/-- **`∏_{1000 ≤ m < b} (1 - 1/(m-1)²) ≥ 998/999`, PROVED.** -/
theorem K_high (b : ℕ) (hb : 1000 ≤ b) : (998 / 999 : ℝ) ≤ ∏ m ∈ Ico 1000 b, f1 m := by
  rw [tele 1000 (by norm_num) b hb]
  have hB : (1000 : ℝ) ≤ b := by exact_mod_cast hb
  push_cast
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith

/-! ### The bound for `∏_A (1 - 1/(p-1)²)` -/

lemma mem_A {z : ℝ} {p : ℕ} (hp : p ∈ primes5Below z) :
    p.Prime ∧ p ≠ 3 ∧ (p : ℝ) < z ∧ p ≠ 2 := by
  unfold primes5Below at hp
  rw [mem_filter, mem_primesBelow] at hp
  exact ⟨hp.1.1, hp.1.2.1, hp.1.2.2, hp.2⟩

/-- **`∏_{5 ≤ p < z} (1 - 1/(p-1)²) ≥ 0.88032 · 998/999` for `z ≥ 1000`, PROVED.** -/
theorem K_bound {z : ℝ} (hz : 1000 ≤ z) :
    (0.88032 : ℝ) * (998 / 999) ≤ ∏ p ∈ primes5Below z, f1 p := by
  rw [← prod_filter_mul_prod_filter_not (primes5Below z) (fun p => p < 1000)]
  have h5 : ∀ p ∈ primes5Below z, 5 ≤ p := by
    intro p hp
    obtain ⟨hpr, h3, _, h2⟩ := mem_A hp
    exact two_le_of_ne3 hpr h2 h3
  have hlo : (0.88032 : ℝ) ≤ ∏ p ∈ (primes5Below z).filter (fun p => p < 1000), f1 p := by
    refine le_trans K_low (prod_le_of_sub ?_ ?_ ?_)
    · intro p hp
      rw [mem_filter] at hp
      obtain ⟨hpr, h3, _, h2⟩ := mem_A hp.1
      exact List.mem_toFinset.2 (cov5_sound hpr hp.2 h2 h3)
    · intro p hp; exact (f1_bounds (by have := pl5_ge p (List.mem_toFinset.1 hp); omega)).1
    · intro p hp; exact (f1_bounds (by have := pl5_ge p (List.mem_toFinset.1 hp); omega)).2
  have hb : 1000 ≤ ⌊z⌋₊ + 1 := by
    have : 1000 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
    omega
  have hhi : (998 / 999 : ℝ) ≤ ∏ p ∈ (primes5Below z).filter (fun p => ¬ p < 1000), f1 p := by
    refine le_trans (K_high _ hb) (prod_le_of_sub ?_ ?_ ?_)
    · intro p hp
      rw [mem_filter] at hp
      obtain ⟨_, _, hpz, _⟩ := mem_A hp.1
      have : p ≤ ⌊z⌋₊ := Nat.le_floor hpz.le
      rw [mem_Ico]; omega
    · intro p hp; rw [mem_Ico] at hp; exact (f1_bounds (by omega)).1
    · intro p hp; rw [mem_Ico] at hp; exact (f1_bounds (by omega)).2
  calc (0.88032 : ℝ) * (998 / 999) ≤ _ := mul_le_mul hlo hhi (by norm_num) (by linarith)
    _ = _ := rfl

/-! ### The Mertens part `∏_A (1 - 1/p)` -/

/-- **`∏_{p ≤ z} (1 - 1/p) ≤ ⅓ ∏_{5 ≤ p < z} (1 - 1/p)` for `z ≥ 3`, PROVED.** -/
theorem T_le_A {z : ℝ} (hz : 3 ≤ z) :
    ∏ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime, f2 p ≤ (1 / 3) * ∏ p ∈ primes5Below z, f2 p := by
  have h3z : 3 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
  have h2A : (2 : ℕ) ∉ primes5Below z := fun h => (mem_A h).2.2.2 rfl
  have h3A : (3 : ℕ) ∉ insert 2 (primes5Below z) := by
    rw [mem_insert]; rintro (h | h)
    · exact absurd h (by norm_num)
    · exact (mem_A h).2.1 rfl
  have hsub : insert 3 (insert 2 (primes5Below z)) ⊆ (range (⌊z⌋₊ + 1)).filter Nat.Prime := by
    intro p hp
    rw [mem_insert, mem_insert] at hp
    rw [mem_filter, mem_range]
    rcases hp with rfl | rfl | hp
    · exact ⟨by omega, Nat.prime_three⟩
    · exact ⟨by omega, Nat.prime_two⟩
    · obtain ⟨hpr, _, hpz, _⟩ := mem_A hp
      have : p ≤ ⌊z⌋₊ := Nat.le_floor hpz.le
      exact ⟨by omega, hpr⟩
  have hle := prod_le_of_sub (f := f2) hsub
    (fun p hp => (f2_bounds (mem_filter.1 hp).2.one_lt.le).1)
    (fun p hp => (f2_bounds (mem_filter.1 hp).2.one_lt.le).2)
  rw [prod_insert h3A, prod_insert h2A] at hle
  have e : f2 3 * (f2 2 * ∏ p ∈ primes5Below z, f2 p) = 1 / 3 * ∏ p ∈ primes5Below z, f2 p := by
    unfold f2; push_cast; ring
  linarith

/-- **`∏_{5 ≤ p < z} (1 - 1/p) ≥ 3 e^{-γ}/log z · (1 - 1/(2 log² z))`, CONDITIONAL ON
`RS325`, for `z ≥ 285`.** -/
theorem Q_bound_of (h : RS325) {z : ℝ} (hz : 285 ≤ z) :
    3 * (exp (-eulerMascheroniConstant) / log z * (1 - 1 / (2 * log z ^ 2))) ≤
      ∏ p ∈ primes5Below z, f2 p := by
  have h1 := h z hz
  have h2 := T_le_A (by linarith : (3 : ℝ) ≤ z)
  unfold f2 at h2 ⊢
  linarith

/-! ### `e^{-2γ}` from Mathlib's `γ < H_n - log n` -/

def HR : ℕ := 10 ^ 20

/-- `Σ_{i < n} ⌈HR/(i+1)⌉`. -/
def hsU : ℕ → ℕ
  | 0 => 0
  | n + 1 => hsU n + (HR + n) / (n + 1)

/-- `Σ_{i < n} ⌊HR/(i+1)⌋`. -/
def hsL : ℕ → ℕ
  | 0 => 0
  | n + 1 => hsL n + HR / (n + 1)

theorem harmonic_le_hsU : ∀ n, (harmonic n : ℝ) ≤ hsU n / HR
  | 0 => by simp [hsU]
  | n + 1 => by
    have ih := harmonic_le_hsU n
    rw [harmonic_succ]
    simp only [hsU]
    push_cast
    have hq : HR ≤ (HR + n) / (n + 1) * (n + 1) := by
      have := Nat.lt_div_mul_add (a := HR + n) (Nat.succ_pos n)
      generalize (HR + n) / (n + 1) * (n + 1) = t at this
      omega
    have hHR : (0 : ℝ) < HR := by unfold HR; positivity
    have hstep : ((n : ℝ) + 1)⁻¹ ≤ (((HR + n) / (n + 1) : ℕ) : ℝ) / HR := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hHR]
      have : (HR : ℝ) ≤ (((HR + n) / (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast hq
      linarith
    rw [add_div]
    linarith

theorem hsL_le_harmonic : ∀ n, (hsL n : ℝ) / HR ≤ harmonic n
  | 0 => by simp [hsL]
  | n + 1 => by
    have ih := hsL_le_harmonic n
    rw [harmonic_succ]
    simp only [hsL]
    push_cast
    have hq : HR / (n + 1) * (n + 1) ≤ HR := Nat.div_mul_le_self _ _
    have hHR : (0 : ℝ) < HR := by unfold HR; positivity
    have hstep : ((HR / (n + 1) : ℕ) : ℝ) / HR ≤ ((n : ℝ) + 1)⁻¹ := by
      rw [inv_eq_one_div, div_le_div_iff₀ hHR (by positivity)]
      have : ((HR / (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1) ≤ HR := by exact_mod_cast hq
      linarith
    rw [add_div]
    linarith

theorem hsU_1024 : hsU 1024 = 750917567227813383848 := by decide +kernel

theorem hsL_255 : hsL 255 = 612043871281728036770 := by decide +kernel

/-- `H₁₀₂₄ ≤ 7.50917567227813383848`. -/
theorem H1024_le : (harmonic 1024 : ℝ) ≤ 750917567227813383848 / 10 ^ 20 := by
  have := harmonic_le_hsU 1024
  rw [hsU_1024] at this
  unfold HR at this
  have e : ((10 : ℕ) ^ 20 : ℕ) = ((10 : ℝ) ^ 20) := by push_cast; ring
  rw [e] at this
  exact this

/-- `H₂₅₅ ≥ 6.12043871281728036770`. -/
theorem H255_ge : (612043871281728036770 / 10 ^ 20 : ℝ) ≤ harmonic 255 := by
  have := hsL_le_harmonic 255
  rw [hsL_255] at this
  unfold HR at this
  have e : ((10 : ℕ) ^ 20 : ℕ) = ((10 : ℝ) ^ 20) := by push_cast; ring
  rw [e] at this
  exact this

/-- The lower bound constant for `e^{-2γ}`: `1024² (1 - r)/2.7182818286^15`,
`r = 2 · 7.50917567227813383848 - 15`. -/
def E0 : ℝ := 1024 ^ 2 * (1 - (2 * (750917567227813383848 / 10 ^ 20) - 15)) / 2.7182818286 ^ 15

/-- **`e^{-2γ} ≥ E0`, PROVED** from Mathlib's `γ < H₁₀₂₄ - log 1024`. -/
theorem gamma_sq_bound : E0 ≤ exp (-eulerMascheroniConstant) ^ 2 := by
  have hg := eulerMascheroniConstant_lt_eulerMascheroniSeq' 1024
  simp only [eulerMascheroniSeq', show (1024 : ℕ) ≠ 0 by norm_num, ite_false] at hg
  push_cast at hg
  have hH := H1024_le
  set Hu : ℝ := 750917567227813383848 / 10 ^ 20 with hHu
  have hr0 : 0 < 2 * Hu - 15 := by rw [hHu]; norm_num
  have hr1 : 2 * Hu - 15 < 1 := by rw [hHu]; norm_num
  -- exp(2 Hu) ≤ 2.7182818286^15 / (1 - r)
  have he15 : exp 15 ≤ 2.7182818286 ^ 15 := by
    have := Real.exp_nat_mul 1 15
    rw [show ((15 : ℕ) : ℝ) * 1 = 15 by norm_num] at this
    rw [this]
    exact pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 15
  have her : exp (2 * Hu - 15) ≤ 1 / (1 - (2 * Hu - 15)) :=
    (exp_bound_div_one_sub_of_interval' hr0 hr1).le
  have hexp : exp (2 * Hu) ≤ 2.7182818286 ^ 15 / (1 - (2 * Hu - 15)) := by
    have : exp (2 * Hu) = exp 15 * exp (2 * Hu - 15) := by rw [← exp_add]; ring_nf
    rw [this]
    have h1r : 0 < 1 - (2 * Hu - 15) := by linarith
    calc exp 15 * exp (2 * Hu - 15) ≤ 2.7182818286 ^ 15 * (1 / (1 - (2 * Hu - 15))) :=
          mul_le_mul he15 her (exp_pos _).le (by positivity)
      _ = _ := by ring
  -- exp(-γ)^2 = exp(-2γ) ≥ exp(2 log 1024 - 2 Hu) = 1024² / exp(2 Hu)
  have hsq : exp (-eulerMascheroniConstant) ^ 2 = exp (-2 * eulerMascheroniConstant) := by
    rw [← exp_nat_mul]; ring_nf
  have hmono : exp (2 * log 1024 - 2 * Hu) ≤ exp (-2 * eulerMascheroniConstant) :=
    exp_le_exp.2 (by linarith)
  have hsplit : exp (2 * log 1024 - 2 * Hu) = 1024 ^ 2 / exp (2 * Hu) := by
    rw [exp_sub, show 2 * log (1024 : ℝ) = log (1024 ^ 2) by rw [Real.log_pow]; norm_num,
      exp_log (by norm_num)]
  have hpos : 0 < exp (2 * Hu) := exp_pos _
  have h1r : 0 < 1 - (2 * Hu - 15) := by linarith
  have : E0 ≤ 1024 ^ 2 / exp (2 * Hu) := by
    unfold E0
    rw [← hHu, div_le_div_iff₀ (by positivity) hpos]
    have := mul_le_mul_of_nonneg_left hexp (show (0 : ℝ) ≤ 1024 ^ 2 * (1 - (2 * Hu - 15)) by
      positivity)
    calc 1024 ^ 2 * (1 - (2 * Hu - 15)) * exp (2 * Hu)
        ≤ 1024 ^ 2 * (1 - (2 * Hu - 15)) * (2.7182818286 ^ 15 / (1 - (2 * Hu - 15))) := this
      _ = 1024 ^ 2 * 2.7182818286 ^ 15 := by field_simp
  rw [hsq]
  calc E0 ≤ _ := this
    _ = _ := hsplit.symm
    _ ≤ _ := hmono

/-! ### The final constant -/

/-- `4.5 · 0.88032 · 998/999 · E0 · (1 - 1/(2 · 18.4192²))² > 1.241`. -/
theorem final_const :
    (1.241 : ℝ) < 9 / 2 * ((0.88032 : ℝ) * (998 / 999)) * E0 * (1 - 1 / (2 * 18.4192 ^ 2)) ^ 2 := by
  unfold E0
  norm_num

/-- `log z > 18.4192` for `z ≥ 10^8`. -/
lemma log_ge {z : ℝ} (hz : (10 : ℝ) ^ 8 ≤ z) : (18.4192 : ℝ) < log z := by
  have h1 : log ((10 : ℝ) ^ 8) ≤ log z := log_le_log (by positivity) hz
  rw [Real.log_pow] at h1
  have := RS1962.log_ten_gt
  push_cast at h1
  linarith

/-! ### Lemma 4.2 -/

/-- **Lemma 4.2, `V(z) ≥ 1.241/log² z` for `z ≥ 10^8` and every `N`, CONDITIONAL ON `RS325`,
Rosser-Schoenfeld 1962 eq (3.25).** -/
theorem lemma42_of_RS325 (h : RS325) : Lemma42 := by
  intro N z hz
  have hL := log_ge hz
  set L := log z with hLdef
  have hz1000 : (1000 : ℝ) ≤ z := le_trans (by norm_num) hz
  have hz285 : (285 : ℝ) ≤ z := le_trans (by norm_num) hz
  have hV := V_ge_half N z
  have hsplit : ∏ p ∈ primes5Below z, (1 - 2 / (p : ℝ)) =
      (∏ p ∈ primes5Below z, f1 p) * (∏ p ∈ primes5Below z, f2 p) ^ 2 := by
    rw [← prod_pow, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    obtain ⟨hpr, _, _, _⟩ := mem_A hp
    exact factor_split hpr.two_le
  rw [hsplit] at hV
  have hK := K_bound hz1000
  have hQ := Q_bound_of h hz285
  rw [← hLdef] at hQ
  set K := ∏ p ∈ primes5Below z, f1 p
  set Q := ∏ p ∈ primes5Below z, f2 p
  set e := exp (-eulerMascheroniConstant)
  have hE := gamma_sq_bound
  have hLpos : 0 < L := by linarith
  have hL2 : (18.4192 : ℝ) ^ 2 < L ^ 2 := by nlinarith
  set u := 1 - 1 / (2 * L ^ 2) with hu
  have hc : 1 - 1 / (2 * 18.4192 ^ 2) ≤ u := by
    rw [hu]
    have : 1 / (2 * L ^ 2) ≤ 1 / (2 * (18.4192 : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity); linarith
    linarith
  have hc0 : (0 : ℝ) ≤ 1 - 1 / (2 * 18.4192 ^ 2) := by norm_num
  have he0 : 0 < e := exp_pos _
  have hm0 : 0 ≤ 3 * (e / L * u) := by
    have : 0 ≤ u := le_trans hc0 hc
    positivity
  -- Q² ≥ 9 e² u² / L²
  have hQ2 : (3 * (e / L * u)) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ hm0 hQ 2
  have hK0 : 0 ≤ 0.88032 * (998 / 999 : ℝ) := by norm_num
  have hstep1 : 0.88032 * (998 / 999 : ℝ) * (3 * (e / L * u)) ^ 2 ≤ K * Q ^ 2 :=
    mul_le_mul hK hQ2 (by positivity) (le_trans hK0 hK)
  have e1 : (3 * (e / L * u)) ^ 2 = 9 * (e ^ 2 * u ^ 2) / L ^ 2 := by
    field_simp
    norm_num
  have hu2 : (1 - 1 / (2 * 18.4192 ^ 2)) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hc0 hc 2
  have hE0 : 0 ≤ E0 := by unfold E0; norm_num
  have heu : E0 * (1 - 1 / (2 * 18.4192 ^ 2)) ^ 2 ≤ e ^ 2 * u ^ 2 :=
    mul_le_mul hE hu2 (by positivity) (by positivity)
  have hfin := final_const
  have hLL : 0 < L ^ 2 := by positivity
  have key : 1.241 ≤ 9 / 2 * (0.88032 * (998 / 999 : ℝ)) * (e ^ 2 * u ^ 2) := by
    have := mul_le_mul_of_nonneg_left heu (show (0 : ℝ) ≤ 9 / 2 * (0.88032 * (998 / 999)) by
      norm_num)
    nlinarith
  rw [e1] at hstep1
  have : 1.241 / L ^ 2 ≤ 1 / 2 * (0.88032 * (998 / 999 : ℝ) * (9 * (e ^ 2 * u ^ 2) / L ^ 2)) := by
    rw [div_le_iff₀ hLL]
    have e2 : 1 / 2 * (0.88032 * (998 / 999 : ℝ) * (9 * (e ^ 2 * u ^ 2) / L ^ 2)) * L ^ 2 =
        9 / 2 * (0.88032 * (998 / 999 : ℝ)) * (e ^ 2 * u ^ 2) := by
      field_simp
    rw [e2]; exact key
  linarith

/-! ### Wiring -/

/-- **`Case3Sieve`, CONDITIONAL ON `Thm21Case3 R4`, `RS325` and `Lemma43 R4`.** -/
theorem case3Sieve_of_RS (R4 : ℕ → ℝ) (h21 : Thm21Case3 R4) (h325 : RS325) (h43 : Lemma43 R4) :
    Case3Sieve :=
  case3Sieve_of R4 h21 (lemma42_of_RS325 h325) h43

/-- **Theorem 1.2, `Ω(ab) ≤ 33` for every `N ≥ 2`, CONDITIONAL ON `GapTable`, `Case2Sieve`,
`Case2Table`, `Thm21Case3 R4`, `RS325` and `Lemma43 R4`.** -/
theorem theorem1_2_of_inputs_RS (hG : GapTable) (hs : Case2Sieve) (ht : Case2Table)
    (R4 : ℕ → ℝ) (h21 : Thm21Case3 R4) (h325 : RS325) (h43 : Lemma43 R4) :
    ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 33 N :=
  theorem1_2_of_inputs3 hG hs ht R4 h21 (lemma42_of_RS325 h325) h43

/-! ### Vacuity check: eq (3.25) holds at `x = 1000` -/

def a2 (p : ℕ) : ℕ := p - 1
def b2 (p : ℕ) : ℕ := p

lemma frac2 {p : ℕ} (hp : 1 ≤ p) : (a2 p : ℝ) / b2 p = f2 p := by
  unfold a2 b2 f2
  rw [Nat.cast_sub hp]
  have h : (1 : ℝ) ≤ p := by exact_mod_cast hp
  field_simp
  push_cast
  ring

theorem chain2_check : 8096 * 10 ^ 25 ≤ chain a2 b2 pl CR := by decide +kernel

theorem pl_ge : ∀ p ∈ pl, 2 ≤ p := by decide +kernel

/-- `∏_{p ≤ 1000} (1 - 1/p) ≥ 0.08096`, PROVED. -/
theorem P1000_ge :
    (0.08096 : ℝ) ≤ ∏ p ∈ (range (⌊(1000 : ℝ)⌋₊ + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  have hfl : ⌊(1000 : ℝ)⌋₊ = 1000 := by norm_num
  rw [hfl]
  have hsub : (range (1000 + 1)).filter Nat.Prime ⊆ pl.toFinset := by
    intro p hp
    rw [mem_filter, mem_range] at hp
    exact List.mem_toFinset.2 (cov_sound hp.2 (by omega))
  have hle := prod_le_of_sub (f := f2) hsub
    (fun p hp => (f2_bounds (by have := pl_ge p (List.mem_toFinset.1 hp); omega)).1)
    (fun p hp => (f2_bounds (by have := pl_ge p (List.mem_toFinset.1 hp); omega)).2)
  rw [List.prod_toFinset _ pl_nodup] at hle
  have hc := chain_le a2 b2 pl CR
  have hm : pl.map (fun p => (a2 p : ℝ) / b2 p) = pl.map f2 :=
    List.map_congr_left (fun p hp => frac2 (by have := pl_ge p hp; omega))
  rw [hm] at hc
  have hk : ((8096 * 10 ^ 25 : ℕ) : ℝ) ≤ (chain a2 b2 pl CR : ℝ) := by
    exact_mod_cast chain2_check
  have hCR : (CR : ℝ) = 10 ^ 30 := by unfold CR; push_cast; ring
  rw [hCR] at hc
  push_cast at hk
  show (0.08096 : ℝ) ≤ ∏ p ∈ (range (1000 + 1)).filter Nat.Prime, f2 p
  linarith

/-- `e^{-γ} ≤ 256/(2.7182818283^6 (1 + y + y²/2))`, `y = H₂₅₅⁻ - 6`, from Mathlib's
`H₂₅₅ - log 256 < γ`. -/
theorem exp_neg_gamma_le :
    exp (-eulerMascheroniConstant) ≤
      256 / (2.7182818283 ^ 6 * (1 + (612043871281728036770 / 10 ^ 20 - 6) +
        (612043871281728036770 / 10 ^ 20 - 6) ^ 2 / 2)) := by
  have hg := eulerMascheroniSeq_lt_eulerMascheroniConstant 255
  rw [eulerMascheroniSeq] at hg
  have e256 : ((255 : ℕ) : ℝ) + 1 = 256 := by norm_num
  rw [e256] at hg
  have hH := H255_ge
  set Hl : ℝ := 612043871281728036770 / 10 ^ 20 with hHl
  have hy : 0 ≤ Hl - 6 := by rw [hHl]; norm_num
  have h1 : exp (-eulerMascheroniConstant) ≤ exp (log 256 - Hl) :=
    exp_le_exp.2 (by linarith)
  rw [exp_sub, exp_log (by norm_num)] at h1
  have hlow : 2.7182818283 ^ 6 * (1 + (Hl - 6) + (Hl - 6) ^ 2 / 2) ≤ exp Hl := by
    have he6 : (2.7182818283 : ℝ) ^ 6 ≤ exp 6 := by
      have := Real.exp_nat_mul 1 6
      rw [show ((6 : ℕ) : ℝ) * 1 = 6 by norm_num] at this
      rw [this]
      exact pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 6
    have hq := quadratic_le_exp_of_nonneg hy
    have : exp Hl = exp 6 * exp (Hl - 6) := by rw [← exp_add]; ring_nf
    rw [this]
    exact mul_le_mul he6 hq (by positivity) (exp_pos _).le
  calc exp (-eulerMascheroniConstant) ≤ 256 / exp Hl := h1
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity) hlow

/-- **Vacuity check, PROVED: eq (3.25) holds at `x = 1000`.** So `RS325` is not refuted by its
first instance checked here; Python margin 0.44 percent. -/
theorem rs325_at_1000 :
    exp (-eulerMascheroniConstant) / log 1000 * (1 - 1 / (2 * log 1000 ^ 2)) <
      ∏ p ∈ (range (⌊(1000 : ℝ)⌋₊ + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  have hP := P1000_ge
  have he := exp_neg_gamma_le
  have hlo := RS1962.log_ten_gt
  have hhi := log_ten_lt
  have hlog : log (1000 : ℝ) = 3 * log 10 := by
    rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow]; norm_num
  rw [hlog]
  set L := 3 * log (10 : ℝ)
  have hL1 : (6.9072 : ℝ) < L := by linarith
  have hL2 : L < (6.90783 : ℝ) := by linarith
  set e := exp (-eulerMascheroniConstant)
  have he0 : 0 < e := exp_pos _
  have hu : 1 - 1 / (2 * L ^ 2) ≤ 1 - 1 / (2 * (6.90783 : ℝ) ^ 2) := by
    have : 1 / (2 * (6.90783 : ℝ) ^ 2) ≤ 1 / (2 * L ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    linarith
  have hu0 : 0 ≤ 1 - 1 / (2 * (6.90783 : ℝ) ^ 2) := by norm_num
  have hLpos : 0 < L := by linarith
  have h1 : e / L * (1 - 1 / (2 * L ^ 2)) ≤ e / L * (1 - 1 / (2 * (6.90783 : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left hu (by positivity)
  have h2 : e / L ≤ e / 6.9072 := div_le_div_of_nonneg_left he0.le (by norm_num) hL1.le
  have h3 : e / L * (1 - 1 / (2 * (6.90783 : ℝ) ^ 2)) ≤
      e / 6.9072 * (1 - 1 / (2 * (6.90783 : ℝ) ^ 2)) := mul_le_mul_of_nonneg_right h2 hu0
  have h4 : e / 6.9072 * (1 - 1 / (2 * (6.90783 : ℝ) ^ 2)) ≤
      (256 / (2.7182818283 ^ 6 * (1 + (612043871281728036770 / 10 ^ 20 - 6) +
        (612043871281728036770 / 10 ^ 20 - 6) ^ 2 / 2))) / 6.9072 *
          (1 - 1 / (2 * (6.90783 : ℝ) ^ 2)) := by
    apply mul_le_mul_of_nonneg_right _ hu0
    exact div_le_div_of_nonneg_right he (by norm_num)
  have h5 : (256 / (2.7182818283 ^ 6 * (1 + (612043871281728036770 / 10 ^ 20 - 6) +
        (612043871281728036770 / 10 ^ 20 - 6) ^ 2 / 2))) / 6.9072 *
          (1 - 1 / (2 * (6.90783 : ℝ) ^ 2)) < 0.08096 := by norm_num
  linarith

end LeanLab.AlmostPrimes.CampbellLemma42
