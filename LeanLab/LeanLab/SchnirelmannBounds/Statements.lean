/-
Bounds on Schnirelmann's constant, and Kaniecki's RH results.
P0066 Vaughan 1977, J. reine angew. Math. 290, 93-108: Schnirelmann's constant at most 27.
  Confirmed by Helfgott arXiv 1312.7748 Section 1.2.3, Vaughan [Vau77] k = 27.
P0032 Riesel, Vaughan 1983: at most 19, as Kaniecki and Helfgott state it; paper not read.
P0022 Kaniecki 1995, Acta Arith. 72, 361-374, Main Theorem, read from the CC-BY PDF:
  "Suppose the Riemann Hypothesis is true. Then every odd natural number can be written as a
  sum of at most five primes. If G2 > 1.405 · 10^12 then every even natural number can be
  written as a sum of at most four primes." G2 is the height to which even Goldbach is
  verified.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.SchnirelmannConstant.Defs
import LeanLab.Ramare1995.Statements
import LeanLab.Verifications.Statements

namespace LeanLab.SchnirelmannBounds
open LeanLab.SchnirelmannConstant

/-! ### The papers, cited, with `sorry` -/

/-- P0066 Vaughan 1977: every integer larger than 1 is a sum of at most 27 primes. A Prop
since unit U-1273, PC run 20261020T2004Z-7678, no longer a `sorry`: Vaughan1977Route.lean
proves it as `Vaughan1977.vaughan1977_of_RV`, CONDITIONAL ON the Riesel-Vaughan inputs, and
Vaughan1977.lean gives it from the reconstructed density input `VaughanDensity26`. -/
def vaughan1977_stmt : Prop := ∀ n : ℕ, 1 < n → AtMostPrimes 27 n

/-- P0032 Riesel-Vaughan 1983: at most 19 primes. Cited Prop, no sorry theorem. -/
def rieselVaughan_stmt : Prop := ∀ n : ℕ, 1 < n → AtMostPrimes 19 n

/-- P0032 Riesel-Vaughan 1983, page 1 Theorem: every even natural number is a sum of at most
eighteen primes.
Cited Prop, no sorry theorem. -/
def rieselVaughan_even_stmt : Prop := ∀ n : ℕ, Even n → AtMostPrimes 18 n

/-- Deshouillers 1975/76, Sem. Delange-Pisot-Poitou, cited as ref [2] on page 1 of P0032:
every integer larger than 1 is a sum of at most 26 primes. Not in PAPERS.md, paper not read.
Cited Prop, no sorry theorem. -/
def deshouillers1976_stmt : Prop := ∀ n : ℕ, 1 < n → AtMostPrimes 26 n

/-- P0022 Kaniecki, first part. The paper says every odd natural number; `1` is not a sum
of primes, so the statement is read for odd `n > 1`. A Prop since audit U-1069, PC run
20261019T1503Z-1562: it is PROVED CONDITIONAL ON goldbach_10's three inputs and Liu-Wang as
`SchnirelmannBounds.kaniecki_odd` in Discharged.lean, no longer a `sorry`. -/
def kaniecki_odd_stmt : Prop :=
  RiemannHypothesis → ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n

/-- P0022 Kaniecki, second part: under RH, if even Goldbach is verified past
`1.405 · 10^12`, every even natural number is a sum of at most four primes. A Prop since
audit U-1069; PROVED CONDITIONAL in Discharged.lean. -/
def kaniecki_even_stmt : Prop := RiemannHypothesis →
    (∃ G2 : ℕ, 1405 * 10 ^ 9 < G2 ∧ EvenGoldbachUpTo G2) →
    ∀ n : ℕ, Even n → AtMostPrimes 4 n

/-! ### Links, zero sorry -/

/-- Ramaré's 7 gives Riesel-Vaughan's 19. -/
theorem rieselVaughan_of_ramare (h : ∀ n : ℕ, 1 < n → AtMostPrimes 7 n) :
    ∀ n : ℕ, 1 < n → AtMostPrimes 19 n := fun n hn => (h n hn).mono (by norm_num)

/-- Riesel-Vaughan's 19 gives Vaughan's 27. -/
theorem vaughan_of_rieselVaughan (h : ∀ n : ℕ, 1 < n → AtMostPrimes 19 n) :
    ∀ n : ℕ, 1 < n → AtMostPrimes 27 n := fun n hn => (h n hn).mono (by norm_num)

/-- Kaniecki's hypothesis on G2 is now met: Oliveira e Silva, Herzog, Pardi verify even
Goldbach to `4 · 10^18`. So under RH alone every even number is at most four primes. -/
theorem kaniecki_even_RH_of (hK : RiemannHypothesis →
      (∃ G2 : ℕ, 1405 * 10 ^ 9 < G2 ∧ EvenGoldbachUpTo G2) →
      ∀ n : ℕ, Even n → AtMostPrimes 4 n)
    (hO : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    RiemannHypothesis → ∀ n : ℕ, Even n → AtMostPrimes 4 n :=
  fun hRH => hK hRH ⟨4 * 10 ^ 18, by norm_num, hO⟩

/-- Ternary Goldbach gives every odd `n > 1` as at most three primes. -/
theorem odd_atMost3_of_ternary (hT : TernaryGoldbach) :
    ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 3 n := by
  intro n ho hn
  rcases Nat.lt_or_ge n 7 with h | h
  · obtain ⟨k, rfl⟩ := ho
    have : k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl
    · exact (AtMostPrimes.prime Nat.prime_three).mono (by norm_num)
    · exact (AtMostPrimes.prime (by norm_num : Nat.Prime 5)).mono (by norm_num)
  · obtain ⟨p, q, r, hp, hq, hr, rfl⟩ := hT n ho h
    exact ((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add (AtMostPrimes.prime hr)

/-- Ternary Goldbach gives every even number as at most four primes, unconditionally
replacing Kaniecki's RH result: `n = 3 + (n - 3)` for `n ≥ 10`, small cases by hand. -/
theorem even_atMost4_of_ternary (hT : TernaryGoldbach) :
    ∀ n : ℕ, Even n → AtMostPrimes 4 n := by
  intro n he
  rcases Nat.lt_or_ge n 10 with h | h
  · obtain ⟨k, rfl⟩ := he
    have hk : k < 5 := by omega
    interval_cases k
    · exact AtMostPrimes.zero.mono (by norm_num)
    · exact (AtMostPrimes.prime Nat.prime_two).mono (by norm_num)
    · exact ((AtMostPrimes.prime Nat.prime_two).add (AtMostPrimes.prime Nat.prime_two)).mono
        (by norm_num)
    · exact ((AtMostPrimes.prime Nat.prime_three).add (AtMostPrimes.prime Nat.prime_three)).mono
        (by norm_num)
    · exact ((AtMostPrimes.prime Nat.prime_three).add
        (AtMostPrimes.prime (by norm_num : Nat.Prime 5))).mono (by norm_num)
  · have ho : Odd (n - 3) := by obtain ⟨k, rfl⟩ := he; exact ⟨k - 2, by omega⟩
    have := (AtMostPrimes.prime Nat.prime_three).add
      (odd_atMost3_of_ternary hT (n - 3) ho (by omega))
    rwa [show 3 + (n - 3) = n by omega] at this

/-- Ternary Goldbach gives Schnirelmann's constant at most 4, beating Ramaré's 7. -/
theorem atMost4_of_ternary (hT : TernaryGoldbach) : ∀ n : ℕ, 1 < n → AtMostPrimes 4 n := by
  intro n hn
  rcases Nat.even_or_odd n with he | ho
  · exact even_atMost4_of_ternary hT n he
  · exact (odd_atMost3_of_ternary hT n ho hn).mono (by norm_num)

/-- Kaniecki's two RH statements both follow from ternary Goldbach. -/
theorem kaniecki_of_ternary (hT : TernaryGoldbach) :
    (∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n) ∧ (∀ n : ℕ, Even n → AtMostPrimes 4 n) :=
  ⟨fun n ho hn => (odd_atMost3_of_ternary hT n ho hn).mono (by norm_num),
    even_atMost4_of_ternary hT⟩

end LeanLab.SchnirelmannBounds
