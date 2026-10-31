import Mathlib

/-!
# Helfgott's book, chapter 11, Lemma 11.11: the elementary steps of (11.79)

Unit U-6454, CLOUD 20261020T1318Z-cloud43, P0001 P0013. AI wrote this file.

Source: H. A. Helfgott, The ternary Goldbach problem, book draft of 2019-12-14, chapter 11, Type I
sums, page 313, copy papers/P0001-book-chap11.pdf. The proof of (11.79) bounds
`Σ_{v ≤ x, (v,q) ≠ 1} Λ(v)(v, q)` by `(log x) Σ_{p ∣ q} p^{v_p(q)}` and then uses
`Σ_{p ∣ q} p^{v_p(q)} ≤ q`. This file proves that last step:

* `sum_le_prod_of_two_le`: a finite sum of naturals each at least 2 is at most their product;
* `sum_primePow_parts_le`: `Σ_{p ∣ q} p^{v_p(q)} ≤ q` for every `q ≥ 1`.

The other steps of Lemma 11.11 were tested numerically, gen/chap11_*_U6453.out and
gen/chap11_062008_U6454.out: (11.77), (11.78) hold, sharply, and the constant 0.62008 of
Cor. 5.5 is the supremum 0.62007638 of `Σ_{n ≤ x} Λ(n)n/x²`, attained at `x = 5`.
Ternary Goldbach is a theorem; binary Goldbach is OPEN.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/

namespace LeanLab.HelfgottArcs.BookChap11
open Finset

/-- A finite sum of naturals, each at least `2`, is at most their product. -/
theorem sum_le_prod_of_two_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, 2 ≤ f i) : ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have hfa := hf a (mem_insert_self a s)
    have ih' := ih (fun i hi => hf i (mem_insert_of_mem hi))
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs; simp
    · have hP : 2 ≤ ∏ i ∈ s, f i := by
        obtain ⟨b, hb⟩ := hs
        have h1 : f b ∣ ∏ i ∈ s, f i := dvd_prod_of_mem f hb
        have h2 : 0 < ∏ i ∈ s, f i := prod_pos fun i hi => by
          have := hf i (mem_insert_of_mem hi); omega
        exact le_trans (hf b (mem_insert_of_mem hb)) (Nat.le_of_dvd h2 h1)
      nlinarith

/-- **`Σ_{p ∣ q} p^{v_p(q)} ≤ q`**, the last step of the proof of (11.79). -/
theorem sum_primePow_parts_le {q : ℕ} (hq : q ≠ 0) :
    ∑ p ∈ q.primeFactors, p ^ q.factorization p ≤ q := by
  calc ∑ p ∈ q.primeFactors, p ^ q.factorization p
      ≤ ∏ p ∈ q.primeFactors, p ^ q.factorization p := by
        apply sum_le_prod_of_two_le
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hv : 1 ≤ q.factorization p := by
          rw [← Nat.support_factorization] at hp
          exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
        calc 2 ≤ p := hpp.two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ q.factorization p := Nat.pow_le_pow_right hpp.pos hv
    _ = q := (Nat.prod_primeFactors_pow_factorization hq).symm

/-- Vacuity: at `q = 360 = 2³ · 3² · 5` the sum is `8 + 9 + 5 = 22 ≤ 360`. -/
example : ∑ p ∈ (360 : ℕ).primeFactors, p ^ (360 : ℕ).factorization p ≤ 360 :=
  sum_primePow_parts_le (by norm_num)

end LeanLab.HelfgottArcs.BookChap11
