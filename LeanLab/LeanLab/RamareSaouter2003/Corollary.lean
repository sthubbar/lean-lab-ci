/-
P0099 Ramaré-Saouter 2003, Corollary 1 re-derived: from Theorem 3 and even Goldbach to
4 · 10^14, Richstein's range, every odd n with 7 ≤ n ≤ 1.13256 · 10^22 = 28314000 × 4 · 10^14
is a sum of three primes. As in Kadiri-Lumley, the top of the range needs one more even
number, 4 · 10^14 + 2 = 5 + 399999999999997, certified here by a Pratt certificate.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.RamareSaouter2003.Statements
import LeanLab.Verifications.Pratt
import LeanLab.Verifications.Statements
import LeanLab.SchnirelmannConstant.Defs

namespace LeanLab.RamareSaouter2003
open Real LeanLab.Verifications.Pratt LeanLab.Verifications LeanLab.SchnirelmannConstant

theorem pQ : Nat.Prime 399999999999997 := by
  refine pratt 399999999999997 2 [(2, 2), (3, 2), (11, 1), (239, 1), (4649, 1), (909091, 1)]
    (by norm_num) (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Nat.prime_two
  · exact Nat.prime_three
  all_goals exact pB (by decide +kernel)

theorem goldbach_top14 : IsGoldbachSum (4 * 10 ^ 14 + 2) :=
  ⟨5, 399999999999997, Nat.prime_five, pQ, by norm_num⟩

/-- Corollary 1, odd `n ≥ 7` form, from Theorem 3 and the `4 · 10^14` even range. -/
theorem corollary1_of
    (h3 : theorem3_stmt)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 14)) :
    ∀ n : ℕ, Odd n → 7 ≤ n → n ≤ 113256 * 10 ^ 17 → IsTernarySum n := by
  intro n hn h7 hhi
  rcases Nat.lt_or_ge (4 * 10 ^ 14 + 3) n with hbig | hsmall
  · have hnR : (4 * 10 ^ 14 + 3 : ℝ) < n := by exact_mod_cast hbig
    have hnR2 : (n : ℝ) ≤ 113256 * 10 ^ 17 := by exact_mod_cast hhi
    obtain ⟨p, hp, hl, hu⟩ := h3 ((n : ℝ) - 3) (by linarith)
    have hp3 : p + 3 ≤ n := by
      have : (p : ℝ) + 3 ≤ n := by linarith
      exact_mod_cast this
    have hgap : n < p + (4 * 10 ^ 14 + 3) := by
      have : (n : ℝ) < p + (4 * 10 ^ 14 + 3) := by nlinarith
      exact_mod_cast this
    have hp2 : p ≠ 2 := by
      rintro rfl
      norm_num at hl
      nlinarith
    have hpo : Odd p := hp.odd_of_ne_two hp2
    have hev : Even (n - p) := Nat.Odd.sub_odd hn hpo
    have h4 : 4 ≤ n - p := by rcases hev with ⟨k, hk⟩; omega
    rcases Nat.lt_or_ge (n - p) (4 * 10 ^ 14 + 1) with hin | htop
    · obtain ⟨q, r, hq, hr, hqr⟩ := hE (n - p) hev h4 (by omega)
      exact ⟨p, q, r, hp, hq, hr, by omega⟩
    · have heq : n - p = 4 * 10 ^ 14 + 2 := by rcases hev with ⟨k, hk⟩; omega
      obtain ⟨q, r, hq, hr, hqr⟩ := goldbach_top14
      exact ⟨p, q, r, hp, hq, hr, by omega⟩
  · have hev : Even (n - 3) := Nat.Odd.sub_odd hn (by decide)
    obtain ⟨q, r, hq, hr, hqr⟩ := hE (n - 3) hev (by omega) (by omega)
    exact ⟨3, q, r, Nat.prime_three, hq, hr, by omega⟩

/-- `AtMostPrimes` representation of `IsTernarySum` -/
theorem atMostPrimes_of_ternary_sum {n : ℕ} (h : IsTernarySum n) : AtMostPrimes 3 n := by
  obtain ⟨p, q, r, hp, hq, hr, rfl⟩ := h
  exact ((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add (AtMostPrimes.prime hr)

/-- Corollary 1 CONDITIONAL ON `Theorem 3` and the `4 · 10^18` even Goldbach check. -/
theorem corollary1_stmt_of (h3 : theorem3_stmt) (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) : corollary1_stmt :=
  fun n hn h_1_lt_n hn_le => by
    rcases Nat.lt_or_ge n 7 with h_lt_7 | h_ge_7
    · have h_3_5 : n = 3 ∨ n = 5 := by
        have h_odd : ∃ k, n = 2 * k + 1 := hn
        rcases h_odd with ⟨k, rfl⟩
        have h_lt : 2 * k + 1 < 7 := h_lt_7
        have h_gt : 1 < 2 * k + 1 := h_1_lt_n
        omega
      rcases h_3_5 with rfl | rfl
      · exact (AtMostPrimes.prime Nat.prime_three).mono (by norm_num)
      · exact (AtMostPrimes.prime (by norm_num : Nat.Prime 5)).mono (by norm_num)
    · have h_ternary := corollary1_of h3 (richstein_of_oesilva hE) n hn h_ge_7 hn_le
      exact atMostPrimes_of_ternary_sum h_ternary

end LeanLab.RamareSaouter2003
