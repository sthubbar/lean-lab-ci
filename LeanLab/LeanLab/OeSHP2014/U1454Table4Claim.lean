/-
U-1454, P0005 Oliveira e Silva, Herzog, Pardi 2014, Table 4, p. 2043, as a reduction.
The paper's claim behind Table 4: for every even n with 6 ≤ n ≤ 4·10^18, n = p + q with p ≤ p(m)
for the last record row m ≤ n. `Table4Claim N` states that with an explicit partition.
* `evenGoldbach_of_table4Claim`: Table4Claim N gives EvenGoldbachUpTo N. PROVED.
* `small_prime_of_table4Claim`: then every even n from 4 to N is p + q with p ≤ 9781. PROVED.
* `table4Claim_iff`: Table4Claim N is EvenGoldbachUpTo N together with the minGB form of
  completeness that U-6818 proved to 10^8. PROVED. The minGB form alone is weaker, since
  minGB n = 0 when n has no partition, U1454Reductions.minGB_eq_zero_iff.
AI-written Lean code, Claude, 2026-10-22, run 20261022T0003Z-15508. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.Tables
import LeanLab.OeSHP2014.U1454Reductions

namespace LeanLab.OeSHP2014.U1454

open LeanLab LeanLab.Verifications LeanLab.OeSHP2014

/-- Table 4 as a claim up to N, with the partition written out. -/
def Table4Claim (N : ℕ) : Prop :=
  ∀ n, Even n → 6 ≤ n → n ≤ N →
    ∃ x ∈ table4, x.1 ≤ n ∧ ∃ p, p.Prime ∧ (n - p).Prime ∧ p ≤ x.2

/-- The largest record of Table 4 is 9781. -/
theorem table4_p_le : ∀ x ∈ table4, x.2 ≤ 9781 := by
  intro x hx
  have h : table4.all (fun x => decide (x.2 ≤ 9781)) = true := by decide +kernel
  simpa using List.all_eq_true.mp h x hx

theorem evenGoldbach_of_table4Claim {N : ℕ} (h : Table4Claim N) : EvenGoldbachUpTo N := by
  intro n hev h4 hn
  rcases Nat.lt_or_ge n 6 with hs | hb
  · have : n = 4 := by obtain ⟨k, hk⟩ := hev; omega
    subst this; exact ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
  · obtain ⟨x, -, -, p, hp, hq, -⟩ := h n hev hb hn
    exact ⟨p, n - p, hp, hq, by have := hq.two_le; omega⟩

/-- Under the claim, the smaller prime never needs to exceed 9781. -/
theorem small_prime_of_table4Claim {N : ℕ} (h : Table4Claim N) :
    ∀ n, Even n → 4 ≤ n → n ≤ N → ∃ p, p ≤ 9781 ∧ p.Prime ∧ (n - p).Prime := by
  intro n hev h4 hn
  rcases Nat.lt_or_ge n 6 with hs | hb
  · have : n = 4 := by obtain ⟨k, hk⟩ := hev; omega
    subst this; exact ⟨2, by norm_num, Nat.prime_two, Nat.prime_two⟩
  · obtain ⟨x, hx, -, p, hp, hq, hle⟩ := h n hev hb hn
    exact ⟨p, hle.trans (table4_p_le x hx), hp, hq⟩

/-- The claim is Goldbach plus the minGB form of completeness. -/
theorem table4Claim_iff (N : ℕ) : Table4Claim N ↔ (EvenGoldbachUpTo N ∧
    ∀ n, Even n → 6 ≤ n → n ≤ N → ∃ x ∈ table4, x.1 ≤ n ∧ minGB n ≤ x.2) := by
  constructor
  · intro h
    refine ⟨evenGoldbach_of_table4Claim h, fun n hev h6 hn => ?_⟩
    obtain ⟨x, hx, hxn, p, hp, hq, hle⟩ := h n hev h6 hn
    refine ⟨x, hx, hxn, le_trans ?_ hle⟩
    have hG : IsGoldbachSum n := ⟨p, n - p, hp, hq, by have := hq.two_le; omega⟩
    by_contra hc
    exact (minGB_spec hG).2.2 p (by omega) ⟨hp, hq⟩
  · rintro ⟨hE, hC⟩ n hev h6 hn
    obtain ⟨x, hx, hxn, hle⟩ := hC n hev h6 hn
    have hG := hE n hev (by omega) hn
    exact ⟨x, hx, hxn, minGB n, (minGB_spec hG).1, (minGB_spec hG).2.1, hle⟩

/-- A kernel check of the claim up to N with the partition found by `firstP`. -/
def claimOK (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => n % 2 == 1 || n < 6 ||
    table4.any fun x => decide (x.1 ≤ n) && primeB (firstP n) && primeB (n - firstP n) &&
      decide (firstP n ≤ x.2)

theorem table4Claim_of_check (N : ℕ) (h : claimOK N = true) : Table4Claim N := by
  intro n hev h6 hn
  have := List.all_eq_true.mp h n (List.mem_range.mpr (by omega))
  have hodd : n % 2 = 0 := Nat.even_iff.mp hev
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this with (h1 | h1) | h1
  · omega
  · omega
  · obtain ⟨x, hx, hc⟩ := List.any_eq_true.mp h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hxn, hp⟩, hq⟩, hle⟩ := hc
    exact ⟨x, hx, hxn, firstP n, primeB_sound hp, primeB_sound hq, hle⟩

/-- Vacuity: the claim holds at N = 1000, through rows 1 to 8 of Table 4. -/
theorem table4Claim_1000 : Table4Claim 1000 := table4Claim_of_check 1000 (by decide +kernel)

end LeanLab.OeSHP2014.U1454

open LeanLab.OeSHP2014.U1454 in
#print axioms table4_p_le
open LeanLab.OeSHP2014.U1454 in
#print axioms evenGoldbach_of_table4Claim
open LeanLab.OeSHP2014.U1454 in
#print axioms small_prime_of_table4Claim
open LeanLab.OeSHP2014.U1454 in
#print axioms table4Claim_iff
open LeanLab.OeSHP2014.U1454 in
#print axioms table4Claim_1000
open LeanLab.OeSHP2014.U1454 in
#print axioms table4Claim_of_check
