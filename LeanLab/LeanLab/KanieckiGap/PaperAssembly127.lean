/-
P0022, page 373. The even conclusion using the paper's interval input.
The cutoff is kept arbitrary to show exactly where each cited input enters.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.KanieckiGap.Decomp127

namespace LeanLab.KanieckiGap.PaperAssembly127

open LeanLab.SchnirelmannConstant

/-- Page 373. The x = 0 instance forces every interval length to be at least six. -/
theorem interval_length_ge_six {H N₀ : ℕ} (hI : IntervalProp H N₀) : 6 ≤ H := by
  obtain ⟨p, q, hp, op, hq, oq, _, hhi⟩ := hI 0 (Nat.zero_le _)
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  obtain ⟨a, ha⟩ := op
  obtain ⟨b, hb⟩ := oq
  omega

/-- Page 373. A concrete satisfiable interval input, using 3 plus 3 throughout. -/
theorem interval_instance : IntervalProp 18 6 := by
  intro x hx
  exact ⟨3, 3, Nat.prime_three, by decide, Nat.prime_three, by decide, by omega, by omega⟩

/-- LEAF. Page 373, the residual m. Choosing x = n - H - 4 bounds an even
residual between four and H plus four. CONDITIONAL ON the interval input. -/
theorem even_residual {H N₀ n : ℕ} (hI : IntervalProp H N₀) (hn : Even n)
    (hlarge : H + 4 ≤ n) (hx : n - H - 4 ≤ N₀) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Even (n - (p + q)) ∧
      4 ≤ n - (p + q) ∧ n - (p + q) ≤ H + 4 ∧
      n = (p + q) + (n - (p + q)) := by
  obtain ⟨p, q, hp, op, hq, oq, hlo, hhi⟩ := hI (n - H - 4) hx
  have hsum : p + q ≤ n := by omega
  have hm : Even (n - (p + q)) := by
    obtain ⟨a, ha⟩ := hn
    obtain ⟨b, hb⟩ := op.add_odd oq
    exact ⟨a - b, by omega⟩
  exact ⟨p, q, hp, hq, hm, by omega, by omega, by omega⟩

/-- LEAF. Page 373, the even assembly after the interval step.
CONDITIONAL ON the interval input, finite Goldbach through H plus four,
and the cited large odd ternary input. -/
theorem even_atMost4_of_interval {H N₀ : ℕ} (hI : IntervalProp H N₀)
    (hE : EvenGoldbachUpTo (H + 4))
    (hCW : ∀ n : ℕ, Odd n → N₀ < n → IsTernarySum n) :
    ∀ n : ℕ, Even n → AtMostPrimes 4 n := by
  intro n hn
  have hH : 6 ≤ H := interval_length_ge_six hI
  by_cases hsmall : n ≤ H + 4
  · by_cases h4 : 4 ≤ n
    · exact (AtMostPrimes.of_goldbach (hE n hn h4 hsmall)).mono (by omega)
    · obtain ⟨a, ha⟩ := hn
      have hcases : n = 0 ∨ n = 2 := by omega
      rcases hcases with rfl | rfl
      · exact AtMostPrimes.zero.mono (by omega)
      · exact (AtMostPrimes.prime Nat.prime_two).mono (by omega)
  by_cases hx : n - H - 4 ≤ N₀
  · obtain ⟨p, q, hp, hq, hm, hm4, hmH, heq⟩ := even_residual hI hn (by omega) hx
    have hres := AtMostPrimes.of_goldbach (hE _ hm hm4 hmH)
    have hsum := ((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add hres
    rw [← heq] at hsum
    exact hsum
  · have hodd : Odd (n - 3) := Nat.Even.sub_odd (by omega) hn (by decide)
    obtain ⟨p, q, r, hp, hq, hr, heq⟩ := hCW (n - 3) hodd (by omega)
    have hsum := (AtMostPrimes.prime Nat.prime_three).add
      (((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add (AtMostPrimes.prime hr))
    have heq' : 3 + (p + q + r) = n := by omega
    rw [heq'] at hsum
    exact hsum

/-- Page 373. The even half in the exact paper route, with its finite input
at 1.405 times ten to the twelve. CONDITIONAL ON IntervalProp and the large
odd ternary input. -/
theorem kaniecki_even_of_interval {N₀ : ℕ}
    (hI : IntervalProp (14045 * 10 ^ 8) N₀)
    (hE : EvenGoldbachUpTo (1405 * 10 ^ 9))
    (hCW : ∀ n : ℕ, Odd n → N₀ < n → IsTernarySum n) :
    ∀ n : ℕ, Even n → AtMostPrimes 4 n := by
  apply even_atMost4_of_interval hI
  · intro n hn h4 hhi
    exact hE n hn h4 (by omega)
  · exact hCW

/-- Page 373. The odd half from the even conclusion, with no gap table.
CONDITIONAL ON the same interval, finite Goldbach and large ternary inputs. -/
theorem kaniecki_odd_of_interval {N₀ : ℕ}
    (hI : IntervalProp (14045 * 10 ^ 8) N₀)
    (hE : EvenGoldbachUpTo (1405 * 10 ^ 9))
    (hCW : ∀ n : ℕ, Odd n → N₀ < n → IsTernarySum n) :
    ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n := by
  intro n hn hn1
  have hn3 : 3 ≤ n := by obtain ⟨a, ha⟩ := hn; omega
  have hev : Even (n - 3) := Nat.Odd.sub_odd hn (by decide)
  have h4 := kaniecki_even_of_interval hI hE hCW (n - 3) hev
  have h5 := (AtMostPrimes.prime Nat.prime_three).add h4
  have heq : 3 + (n - 3) = n := by omega
  simpa only [heq] using h5

/-- Page 373. The odd conclusion through the original interval proof, with
no modern G10 input. CONDITIONAL ON RH, Lemma 5, Schoenfeld61,
Young-Potler and Chen-Wang. -/
theorem odd_from_paper (hRH : RiemannHypothesis) (h5 : LeanLab.Kaniecki1995.Lemma5)
    (hS : LeanLab.DERZ1997.Schoenfeld61) (hYP : LeanLab.Kaniecki1995.YoungPotler)
    (hCW : LeanLab.Kaniecki1995.ChenWang) :
    ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n := by
  apply KanieckiGap.kaniecki_odd_of (Decomp127.interval_from_paper hRH h5 hS hYP)
  · intro n ho hn
    exact hCW n ho (Nat.lt_of_floor_lt hn).le
  · exact Decomp127.youngPotler_of_paper hYP

/-- Page 373. The even conclusion through the original interval proof.
CONDITIONAL ON RH, Lemma 5, Schoenfeld61, Young-Potler, Chen-Wang
and even Goldbach through 1.405 times ten to the twelve. -/
theorem even_from_paper (hRH : RiemannHypothesis) (h5 : LeanLab.Kaniecki1995.Lemma5)
    (hS : LeanLab.DERZ1997.Schoenfeld61) (hYP : LeanLab.Kaniecki1995.YoungPotler)
    (hCW : LeanLab.Kaniecki1995.ChenWang) (hE : EvenGoldbachUpTo (1405 * 10 ^ 9)) :
    ∀ n : ℕ, Even n → AtMostPrimes 4 n := by
  apply kaniecki_even_of_interval (Decomp127.interval_from_paper hRH h5 hS hYP) hE
  intro n ho hn
  exact hCW n ho (Nat.lt_of_floor_lt hn).le

end LeanLab.KanieckiGap.PaperAssembly127

#print axioms LeanLab.KanieckiGap.PaperAssembly127.interval_length_ge_six
#print axioms LeanLab.KanieckiGap.PaperAssembly127.interval_instance
#print axioms LeanLab.KanieckiGap.PaperAssembly127.even_residual
#print axioms LeanLab.KanieckiGap.PaperAssembly127.even_atMost4_of_interval
#print axioms LeanLab.KanieckiGap.PaperAssembly127.kaniecki_even_of_interval
#print axioms LeanLab.KanieckiGap.PaperAssembly127.kaniecki_odd_of_interval

#print axioms LeanLab.KanieckiGap.PaperAssembly127.odd_from_paper
#print axioms LeanLab.KanieckiGap.PaperAssembly127.even_from_paper
