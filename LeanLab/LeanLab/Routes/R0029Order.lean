import Mathlib

/-!
# R-0029, the model theory route: binary Goldbach needs the order of ℕ

Lab proof, unit U-1244, PC 20261020T1503Z-30533. AI wrote the Lean code. Known mathematics:
Kaplan and Shelah, arXiv 1601.07099, prove that under Dickson's conjecture Th(ℤ, +, 0, 1, Pr),
Pr the primes and their negatives, is decidable; Bateman, Jockusch and Woods, JSL 1993, show that
Th(ℤ, +, 0, Pr, <) is undecidable. In the language without order the binary Goldbach sentence
can only say N = a + b with a, b in ±P, which a single prime pair p, p + N already witnesses,
a Polignac-type statement. Binary Goldbach is OPEN; this is a T3 route, never progress on it.

* `PrZ`: the predicate Pr of Kaplan-Shelah on ℤ.
* `goldbachZ_of_pair`: a prime pair p, p + N gives N = (p + N) + (−p) in ±P.
* `goldbachZ_of_goldbach`: the positive form implies the ℤ form.
* `goldbach_iff_pos`: the positive form is the ℤ form with both summands positive, so the
  order is exactly what the decidable theory lacks.
* `vacuity_two`: 2 = 5 + (−3).
-/

namespace LeanLab.Routes.R0029

/-- The predicate of Kaplan-Shelah: `a` is a prime or the negative of a prime. -/
def PrZ (a : ℤ) : Prop := a.natAbs.Prime

theorem goldbachZ_of_pair {N p : ℕ} (hp : p.Prime) (hq : (p + N).Prime) :
    ∃ a b : ℤ, PrZ a ∧ PrZ b ∧ (N : ℤ) = a + b := by
  refine ⟨(p + N : ℕ), -(p : ℤ), ?_, ?_, ?_⟩
  · unfold PrZ; rw [Int.natAbs_natCast]; exact hq
  · unfold PrZ; rw [Int.natAbs_neg, Int.natAbs_natCast]; exact hp
  · push_cast; ring

theorem goldbachZ_of_goldbach {N p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : N = p + q) :
    ∃ a b : ℤ, PrZ a ∧ PrZ b ∧ (N : ℤ) = a + b :=
  ⟨p, q, by unfold PrZ; simpa using hp, by unfold PrZ; simpa using hq, by rw [h]; push_cast; ring⟩

/-- Positive binary Goldbach for `N` is the ℤ form with `0 < a` and `0 < b`. -/
theorem goldbach_iff_pos (N : ℕ) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N = p + q) ↔
      ∃ a b : ℤ, PrZ a ∧ PrZ b ∧ 0 < a ∧ 0 < b ∧ (N : ℤ) = a + b := by
  constructor
  · rintro ⟨p, q, hp, hq, rfl⟩
    exact ⟨p, q, by unfold PrZ; simpa using hp, by unfold PrZ; simpa using hq,
      by exact_mod_cast hp.pos, by exact_mod_cast hq.pos, by push_cast; ring⟩
  · rintro ⟨a, b, ha, hb, ha0, hb0, hN⟩
    refine ⟨a.natAbs, b.natAbs, ha, hb, ?_⟩
    have h1 : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha0.le
    have h2 : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg hb0.le
    have : (N : ℤ) = (a.natAbs : ℤ) + (b.natAbs : ℤ) := by rw [h1, h2]; exact hN
    exact_mod_cast this

/-- Vacuity: `2 = 5 + (−3)` in `±P`, while `2` has no positive representation. -/
theorem vacuity_two : PrZ 5 ∧ PrZ (-3) ∧ (2 : ℤ) = 5 + -3 ∧
    ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 = p + q := by
  refine ⟨by unfold PrZ; norm_num, by unfold PrZ; norm_num, by norm_num, ?_⟩
  rintro ⟨p, q, hp, hq, h⟩
  have := hp.two_le; have := hq.two_le; omega

end LeanLab.Routes.R0029
