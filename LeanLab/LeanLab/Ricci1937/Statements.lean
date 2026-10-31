/-
P0092 G. Ricci, Su la congettura di Goldbach e la costante di Schnirelmann, prima memoria,
Ann. Scuola Norm. Sup. Pisa 2 6 1937 71-90, read from the numdam scan pages 71 to 74,
run 20261016T2204Z-20593.
STATED: G(n), Schnirelmann's constant S as the eventual bound, the history
S ≤ 800000, 2208, 71, the Heilbronn-Landau-Scherk form, Theorem A S ≤ 67, Theorem B.
PROVED zero sorry: the introduction's remark that every composite 6h + 5 has G ≥ 3, so S ≥ 3;
Goldbach's (2) implies (3); the step "passing from n to n + 2 gives S ≤ 71" from the HLS form
plus a kernel check to 1021; Theorem A from ternary Goldbach; Theorem B from Dirichlet's theorem
in Mathlib, NOT by Ricci's elementary sieve.
Not stated: Theorem C on polynomial values, Theorem D, Theorems I to IV.
AI-written Lean code, Claude. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.SchnirelmannConstant.Defs
import LeanLab.SchnirelmannBounds.Statements
import LeanLab.Common.GoldbachSmall

namespace LeanLab.Ricci1937
open LeanLab.SchnirelmannConstant

/-- `G(n)`, the least `g` with `n = p' + ... + p^(g)`. -/
noncomputable def G (n : ℕ) : ℕ := sInf {g | AtMostPrimes g n}

/-- `S ≤ K`: every large enough integer is a sum of at most `K` primes. -/
def EventuallyAtMost (K : ℕ) : Prop := ∃ N, ∀ n, N < n → AtMostPrimes K n

/-! ### The results Ricci quotes and proves, cited as `Prop`s -/

/-- Schnirelmann 1930, as Ricci lists it: `S ≤ 800000`. -/
def Schnirelmann1930 : Prop := EventuallyAtMost 800000
/-- Romanoff 1935: `S ≤ 2208`. -/
def Romanoff1935 : Prop := EventuallyAtMost 2208
/-- Heilbronn, Landau, Scherk 1936: `S ≤ 71`. -/
def HLS1936 : Prop := EventuallyAtMost 71
/-- The precise HLS form: every large `n` is `p' + ... + p^(68) + v` with `0 ≤ v ≤ 1019`. -/
def HLSForm : Prop :=
  ∃ N, ∀ n, N < n → ∃ l : List ℕ, l.length = 68 ∧ (∀ p ∈ l, p.Prime) ∧ ∃ v, v ≤ 1019 ∧ l.sum + v = n
/-- Theorem A: every large enough integer is a sum of at most 67 primes, `S ≤ 67`. -/
def TheoremA : Prop := EventuallyAtMost 67

/-- Theorem B: in every progression `ax + b`, `x = 1, 2, 3, ...`, `(a, b) = 1`,
1° infinitely many terms have at most two prime factors, equal or distinct, all `> n^{1/3}`;
2° infinitely many terms have at most three prime factors, all distinct, all `> n^{1/4}`. -/
def TheoremB : Prop :=
  ∀ a b : ℕ, 0 < a → Nat.Coprime a b →
    {n | ∃ x, 1 ≤ x ∧ n = a * x + b ∧ n.primeFactorsList.length ≤ 2 ∧
        ∀ p ∈ n.primeFactorsList, (n : ℝ) ^ ((1 : ℝ) / 3) < p}.Infinite ∧
    {n | ∃ x, 1 ≤ x ∧ n = a * x + b ∧ n.primeFactorsList.length ≤ 3 ∧
        n.primeFactorsList.Nodup ∧ ∀ p ∈ n.primeFactorsList, (n : ℝ) ^ ((1 : ℝ) / 4) < p}.Infinite

/-! ### The introduction's remark: composite `6h + 5` needs three primes -/

theorem not_atMost2_of_6h5 (h : ℕ) (hc : ¬ (6 * h + 5).Prime) : ¬ AtMostPrimes 2 (6 * h + 5) := by
  rintro ⟨l, hl, hp, hs⟩
  match l, hl, hp, hs with
  | [], _, _, hs => simp at hs
  | [p], _, hp, hs =>
    simp at hs hp; exact hc (hs ▸ hp)
  | [p, q], _, hp, hs =>
    simp at hs hp
    obtain ⟨hpP, hqP⟩ := hp
    -- one of p, q is 2, the other is 6h + 3, divisible by 3
    have h2 : p = 2 ∨ q = 2 := by
      rcases hpP.eq_two_or_odd with h1 | h1
      · exact Or.inl h1
      rcases hqP.eq_two_or_odd with h2 | h2
      · exact Or.inr h2
      omega
    rcases h2 with rfl | rfl
    · have h3 : 3 ∣ q := ⟨2 * h + 1, by omega⟩
      rcases hqP.eq_one_or_self_of_dvd 3 h3 with h | h
      · omega
      · subst h; apply hc; have : 6 * 0 + 5 = 5 := rfl; have hh : h = 0 := by omega
        subst hh; norm_num
    · have h3 : 3 ∣ p := ⟨2 * h + 1, by omega⟩
      rcases hpP.eq_one_or_self_of_dvd 3 h3 with h | h
      · omega
      · subst h; apply hc; have hh : h = 0 := by omega
        subst hh; norm_num
  | _ :: _ :: _ :: _, hl, _, _ => simp at hl

/-- Infinitely many `n` with `G(n) ≥ 3`: the composites `30k + 35 = 5 (6k + 7) = 6 (5k + 5) + 5`. -/
theorem infinite_not_atMost2 : {n | ¬ AtMostPrimes 2 n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  refine ⟨6 * (5 * N + 5) + 5, ?_, by omega⟩
  apply not_atMost2_of_6h5
  rw [show 6 * (5 * N + 5) + 5 = 5 * (6 * N + 7) by ring]
  exact Nat.not_prime_mul (by norm_num) (by omega)

/-- `3 ≤ S`. -/
theorem three_le_S : ¬ EventuallyAtMost 2 := by
  rintro ⟨N, hN⟩
  obtain ⟨n, hn, hgt⟩ := Set.infinite_iff_exists_gt.mp infinite_not_atMost2 N
  exact hn (hN n hgt)

/-! ### Goldbach's (2) implies (3) -/

theorem conj3_of_goldbach (hG : BinaryGoldbach) : ∀ n, 2 ≤ n → AtMostPrimes 3 n := by
  intro n hn
  rcases Nat.even_or_odd n with he | ho
  · rcases Nat.lt_or_ge n 4 with h | h
    · have : n = 2 := by obtain ⟨k, rfl⟩ := he; omega
      subst this; exact (AtMostPrimes.prime Nat.prime_two).mono (by norm_num)
    · exact (AtMostPrimes.of_goldbach (hG n he h)).mono (by norm_num)
  · rcases Nat.lt_or_ge n 7 with h | h
    · obtain ⟨k, rfl⟩ := ho
      have : k = 1 ∨ k = 2 := by omega
      rcases this with rfl | rfl
      · exact (AtMostPrimes.prime Nat.prime_three).mono (by norm_num)
      · exact (AtMostPrimes.prime (by norm_num : Nat.Prime 5)).mono (by norm_num)
    · have he : Even (n - 3) := by obtain ⟨k, rfl⟩ := ho; exact ⟨k - 1, by omega⟩
      have := (AtMostPrimes.prime Nat.prime_three).add
        (AtMostPrimes.of_goldbach (hG (n - 3) he (by omega)))
      rwa [show 3 + (n - 3) = n by omega] at this

/-! ### From the HLS form to `S ≤ 71`, Ricci's step -/

theorem evenGoldbachUpTo_1020 : EvenGoldbachUpTo 1020 :=
  allEvenGB_sound 1020 (by decide +kernel)

/-- `1 ≤ G(m) ≤ 3` for `2 ≤ m ≤ 1021`, by the kernel. -/
theorem small_atMost3 : ∀ m, 2 ≤ m → m ≤ 1021 → AtMostPrimes 3 m := by
  intro m h2 h
  rcases Nat.even_or_odd m with he | ho
  · exact (atMost2_of_even evenGoldbachUpTo_1020 he (by obtain ⟨k, hk⟩ := he; omega)).mono
      (by norm_num)
  · rcases Nat.lt_or_ge m 7 with h7 | h7
    · obtain ⟨k, rfl⟩ := ho
      have : k = 1 ∨ k = 2 := by omega
      rcases this with rfl | rfl
      · exact (AtMostPrimes.prime Nat.prime_three).mono (by norm_num)
      · exact (AtMostPrimes.prime (by norm_num : Nat.Prime 5)).mono (by norm_num)
    · have he : Even (m - 3) := by obtain ⟨k, rfl⟩ := ho; exact ⟨k - 1, by omega⟩
      have := (AtMostPrimes.prime Nat.prime_three).add
        (atMost2_of_even evenGoldbachUpTo_1020 he (by omega))
      rwa [show 3 + (m - 3) = m by omega] at this

/-- "ed essendo 2 ≤ v + 2 ≤ 1021, 1 ≤ G(v + 2) ≤ 3, passando da n a n + 2 ricaviamo S ≤ 71". -/
theorem hls71_of_form (h : HLSForm) : HLS1936 := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 2, fun n hn => ?_⟩
  obtain ⟨l, hl, hp, v, hv, hs⟩ := hN (n - 2) (by omega)
  have h68 : AtMostPrimes 68 l.sum := ⟨l, hl.le, hp, rfl⟩
  have h3 := small_atMost3 (v + 2) (by omega) (by omega)
  have := h68.add h3
  rwa [show l.sum + (v + 2) = n by omega] at this

/-! ### Links -/

theorem EventuallyAtMost.mono {K K' : ℕ} (h : EventuallyAtMost K) (hK : K ≤ K') :
    EventuallyAtMost K' := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn => (hN n hn).mono hK⟩

/-- Ternary Goldbach, Helfgott 2013, gives Theorem A with room: `S ≤ 4`. -/
theorem theoremA_of_ternary (hT : TernaryGoldbach) : TheoremA :=
  EventuallyAtMost.mono ⟨1, fun n hn => SchnirelmannBounds.atMost4_of_ternary hT n hn⟩ (by norm_num)

theorem theoremA_imp_HLS (h : TheoremA) : HLS1936 := h.mono (by norm_num)
theorem HLS_imp_romanoff (h : HLS1936) : Romanoff1935 := h.mono (by norm_num)
theorem romanoff_imp_schnirelmann (h : Romanoff1935) : Schnirelmann1930 := h.mono (by norm_num)

/-! ### Theorem B from Dirichlet's theorem, not Ricci's elementary proof -/

theorem primes_in_ap_terms (a b : ℕ) (ha : 0 < a) (hab : Nat.Coprime a b) (N : ℕ) :
    ∃ p, N < p ∧ p.Prime ∧ ∃ x, 1 ≤ x ∧ p = a * x + b := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (N + b) (q := a) (a := b) ha.ne' hab.symm
  refine ⟨p, by omega, hp, (p - b) / a, ?_, ?_⟩
  · have hdvd : a ∣ p - b := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.mul_div_cancel_left c ha]
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; omega
    · exact h0
  · have hdvd : a ∣ p - b := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
    rw [Nat.mul_div_cancel' hdvd]; omega

theorem rpow_lt_prime {p : ℕ} (hp : p.Prime) {r : ℝ} (hr : r < 1) : (p : ℝ) ^ r < p :=
  Real.rpow_lt_self_of_one_lt (by exact_mod_cast hp.one_lt) hr

theorem theoremB : TheoremB := by
  intro a b ha hab
  constructor
  · apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨p, hpN, hp, x, hx, hpx⟩ := primes_in_ap_terms a b ha hab N
    refine ⟨p, ⟨x, hx, hpx, ?_, ?_⟩, hpN⟩
    · rw [Nat.primeFactorsList_prime hp]; simp
    · intro q hq
      rw [Nat.primeFactorsList_prime hp, List.mem_singleton] at hq
      subst hq; exact rpow_lt_prime hp (by norm_num)
  · apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨p, hpN, hp, x, hx, hpx⟩ := primes_in_ap_terms a b ha hab N
    refine ⟨p, ⟨x, hx, hpx, ?_, ?_, ?_⟩, hpN⟩
    · rw [Nat.primeFactorsList_prime hp]; simp
    · rw [Nat.primeFactorsList_prime hp]; simp
    · intro q hq
      rw [Nat.primeFactorsList_prime hp, List.mem_singleton] at hq
      subst hq; exact rpow_lt_prime hp (by norm_num)

end LeanLab.Ricci1937
