/-
Split of s145r_compositeCofactor_count, MMS arXiv 1610.02017v2 page 11 bottom
display, composite rough cofactors via their least prime factor.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp581bS145a

namespace LeanLab.Ternary.MMS.Task581.Feed1122
open Finset MeasureTheory

/-- Removing the least prime factor q of m not one: m is rough at y iff y is at most q
and m over q is rough at q. Derived, MMS page 11 bottom display. -/
theorem s145e_rough_leastPrime {m : ℕ} (hm : m ≠ 1) (y : ℝ) :
    Task361.roughIndicator m y =
      if y ≤ (m.minFac : ℝ) then Task361.roughIndicator (m / m.minFac) m.minFac else 0 := by
  classical
  have hq : m.minFac.Prime := Nat.minFac_prime hm
  by_cases hy : y ≤ (m.minFac : ℝ)
  · rw [if_pos hy]
    unfold Task361.roughIndicator
    rw [if_pos, if_pos]
    · intro p hp hpq hpd
      have := Nat.minFac_le_of_dvd hp.two_le (hpd.trans (Nat.div_dvd_of_dvd (Nat.minFac_dvd m)))
      have : (m.minFac : ℝ) ≤ p := by exact_mod_cast this
      linarith
    · intro p hp hpy hpd
      have := Nat.minFac_le_of_dvd hp.two_le hpd
      have : (m.minFac : ℝ) ≤ p := by exact_mod_cast this
      linarith
  · rw [if_neg hy]
    unfold Task361.roughIndicator
    rw [if_neg]
    push Not at hy
    intro h
    exact h m.minFac hq hy (Nat.minFac_dvd m)
/-- Exact least prime identity for the composite rough cofactor count. Derived,
MMS page 11 bottom display, first Buchstab step. -/
theorem s145e_composite_leastPrime_eq {x : ℝ} (hx : 1 < x) {p : ℕ × ℕ × ℕ}
    (hp : p ∈ primeTriples x) (a b : ℝ) :
    (∑ n ∈ ints x (x + Task379.referenceLength x),
        if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
          (if (n / tripleProduct p).Prime then 0 else
            Task361.roughIndicator (n / tripleProduct p) p.1) else 0) =
      ∑ n ∈ ints x (x + Task379.referenceLength x),
        if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
          (if (n / tripleProduct p).Prime then 0 else
            if (p.1 : ℝ) ≤ ((n / tripleProduct p).minFac : ℝ) then
              Task361.roughIndicator (n / tripleProduct p / (n / tripleProduct p).minFac)
                (n / tripleProduct p).minFac else 0) else 0 := by
  classical
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Task379.referenceLength x := by
    unfold Task379.referenceLength; positivity
  have hdpos : 0 < tripleProduct p := tripleProduct_pos hp
  have hd : (0:ℝ) < tripleProduct p := by exact_mod_cast hdpos
  have hp1 : (2:ℝ) ≤ p.1 := by exact_mod_cast ((mem_filter.mp hp).2.1.two_le)
  have hdp : (tripleProduct p : ℝ) * p.1 ≤ x := by
    have := (s145r_triple_logs hx hp).2
    exact (Real.log_le_log_iff (by positivity) hx0).mp this
  have hdx : (tripleProduct p : ℝ) < x := by nlinarith
  refine sum_congr rfl fun n hn => ?_
  have hxn : x ≤ n := ((s145r_mem_ints (by positivity) n).mp hn).1
  by_cases hc : tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b
  · rw [if_pos hc, if_pos hc]
    by_cases hpr : (n / tripleProduct p).Prime
    · rw [if_pos hpr, if_pos hpr]
    · rw [if_neg hpr, if_neg hpr]
      have hm1 : n / tripleProduct p ≠ 1 := by
        intro h1
        have : n = tripleProduct p := by
          have := Nat.div_mul_cancel hc.1
          rw [h1, one_mul] at this; exact this.symm
        have : (n : ℝ) = tripleProduct p := by exact_mod_cast this
        linarith
      exact s145e_rough_leastPrime hm1 _
  · rw [if_neg hc, if_neg hc]

/-- The least prime main term: for each prime q with p one at most q and
d q squared at most x, the rough density of m over q at modulus d q,
log x over d q log q times buchstab of log of x over d q over log q. MMS arXiv 1610.02017v2 p. 11 bottom display; new definition, needed to state the least prime recursion. -/
noncomputable def s145e_leastPrimeMain (x : ℝ) (p : ℕ × ℕ × ℕ) : ℝ :=
  ∑ q ∈ (Finset.range (⌊x⌋₊ + 1)).filter
      (fun q : ℕ => q.Prime ∧ p.1 ≤ q ∧ (tripleProduct p : ℝ) * q * q ≤ x),
    Real.log x / ((tripleProduct p : ℝ) * q * Real.log q) *
      Task571.buchstabModel (Real.log (x / ((tripleProduct p : ℝ) * q)) / Real.log q)

/-- LEAF: MMS page 11 bottom display, after the proved least prime identity:
for each least prime q at least p one of m equal to n over d, the count of m
over q rough at q at modulus d q, at most x to the nine tenths, from the
hypothesis by a bounded depth recursion, summed over q; q squared above x over
d and prime powers are negligible. Class HARD. -/
theorem s145e_leastPrime_count (hPNT : s145r_PNTHyp) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p ∈ primeTriples x,
      ∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
          if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
            (if (n / tripleProduct p).Prime then 0 else
              if (p.1 : ℝ) ≤ ((n / tripleProduct p).minFac : ℝ) then
                Task361.roughIndicator (n / tripleProduct p / (n / tripleProduct p).minFac)
                  (n / tripleProduct p).minFac else 0) else 0) -
          (b - a) * s145e_leastPrimeMain x p| ≤
        ε * Task379.referenceLength x / tripleProduct p := by
  sorry

/-- LEAF: MMS page 11 bottom display, Buchstab prime sum: by Mertens and
partial summation the sum over primes q of buchstab of log of x over d q over
log q divided by q log q equals buchstab of u over log p one minus one over
log of x over d, u equal to log of x over d over log p one. Class MEDIUM. -/
theorem s145e_buchstab_prime_sum :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p ∈ primeTriples x,
      |s145e_leastPrimeMain x p - (cofactorModel x p - Real.log x /
            ((tripleProduct p : ℝ) * Real.log (x / tripleProduct p)))| ≤
        ε / tripleProduct p := by
  sorry

/-- s145r_compositeCofactor_count from the two leaves. Glue proved. -/
theorem s145r_compositeCofactor_count_of_s145e_leaves (hPNT : s145r_PNTHyp) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p ∈ primeTriples x,
      ∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
          if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
            (if (n / tripleProduct p).Prime then 0 else
              Task361.roughIndicator (n / tripleProduct p) p.1) else 0) -
          (b - a) * (cofactorModel x p - Real.log x /
            ((tripleProduct p : ℝ) * Real.log (x / tripleProduct p)))| ≤
        ε * Task379.referenceLength x / tripleProduct p := by
  intro ε hε
  obtain ⟨X₁, h₁⟩ := s145e_leastPrime_count hPNT (ε / 2) (by linarith)
  obtain ⟨X₂, h₂⟩ := s145e_buchstab_prime_sum (ε / 2) (by linarith)
  refine ⟨max (max X₁ X₂) 2, fun x hx p hp a b ha hab hb => ?_⟩
  have hx1 : 1 < x := by linarith [le_max_right (max X₁ X₂) 2]
  have hx' : max X₁ X₂ ≤ x := (le_max_left _ _).trans hx
  rw [s145e_composite_leastPrime_eq hx1 hp a b]
  have e1 := h₁ x ((le_max_left _ _).trans hx') p hp a b ha hab hb
  have e2 := h₂ x ((le_max_right _ _).trans hx') p hp
  set C := ∑ n ∈ ints x (x + Task379.referenceLength x),
          if tripleProduct p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
            (if (n / tripleProduct p).Prime then 0 else
              if (p.1 : ℝ) ≤ ((n / tripleProduct p).minFac : ℝ) then
                Task361.roughIndicator (n / tripleProduct p / (n / tripleProduct p).minFac)
                  (n / tripleProduct p).minFac else 0) else 0
  set M := s145e_leastPrimeMain x p
  set T := cofactorModel x p - Real.log x /
            ((tripleProduct p : ℝ) * Real.log (x / tripleProduct p))
  set L := Task379.referenceLength x
  have hd : (0:ℝ) < tripleProduct p := by exact_mod_cast tripleProduct_pos hp
  have hba : 0 ≤ b - a := by linarith
  have hbaL : b - a ≤ L := by linarith
  have hsplit : Real.log x * C - (b - a) * T =
      (Real.log x * C - (b - a) * M) + (b - a) * (M - T) := by ring
  rw [hsplit]
  have h2 : |(b - a) * (M - T)| ≤ ε / 2 * L / tripleProduct p := by
    rw [abs_mul, abs_of_nonneg hba]
    have hε2 : 0 ≤ ε / 2 / tripleProduct p := by positivity
    calc (b - a) * |M - T| ≤ L * (ε / 2 / tripleProduct p) :=
          mul_le_mul hbaL e2 (abs_nonneg _) (hba.trans hbaL)
      _ = ε / 2 * L / tripleProduct p := by ring
  have hh := abs_add_le (Real.log x * C - (b - a) * M) ((b - a) * (M - T))
  have he : ε / 2 * L / tripleProduct p + ε / 2 * L / tripleProduct p =
      ε * L / tripleProduct p := by ring
  linarith

end LeanLab.Ternary.MMS.Task581.Feed1122
