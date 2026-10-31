import LeanLab.Common.Goldbach
import Mathlib.Computability.Primrec.List

/-!
# R-5100: binary Goldbach is a Π⁰₁ sentence

Lab proof, unit U-5852, CLOUD 20261020T0014Z-cloud30, T3 MOONSHOT route R-5100. AI wrote this
file. Known folklore, recorded as a map of the logic route. Binary Goldbach is OPEN.

`goldbach_pi01`: there is a primitive recursive predicate `P` on `ℕ` with
`BinaryGoldbach ↔ ∀ n, P n`, namely `P n`: some `p < 2n + 5` has `p` and `2n + 4 - p` prime.
So Goldbach is `Π⁰₁`. Consequences for the route, in ROUTES.md R-5100: a false Goldbach is
refuted by one finite computation, `not_goldbach_iff`; independence from PA would make it true,
but showing PA does not refute it is, for a `Π⁰₁` sentence and a `Σ⁰₁`-sound theory, the same as
proving it, so logic gives no shortcut.
-/

namespace LeanLab.Routes.R5100

open Primrec

/-- Primality is primitive recursive: `2 ≤ n` and no `2 ≤ m < n` divides `n`. -/
theorem primrec_prime : PrimrecPred Nat.Prime := by
  have hR : PrimrecRel (fun m n : ℕ => ¬ (2 ≤ m ∧ n % m = 0)) :=
    (PrimrecPred.and (nat_le.comp (const 2) fst)
      (Primrec.eq.comp (nat_mod.comp snd fst) (const 0))).not
  have hall : PrimrecPred fun n : ℕ => ∀ m < n, ¬ (2 ≤ m ∧ n % m = 0) :=
    (PrimrecRel.forall_lt hR).comp Primrec.id Primrec.id
  refine (PrimrecPred.and (nat_le.comp (const 2) Primrec.id) hall).of_eq fun n => ?_
  rw [Nat.prime_def_lt']
  constructor
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun m hm hmn hd => h m hmn ⟨hm, Nat.mod_eq_zero_of_dvd hd⟩⟩
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun m hmn ⟨hm, hmod⟩ => h m hm hmn (Nat.dvd_of_mod_eq_zero hmod)⟩

/-- The bounded Goldbach test for the even number `2n + 4`. -/
def P (n : ℕ) : Prop := ∃ p < 2 * n + 5, p.Prime ∧ (2 * n + 4 - p).Prime

theorem primrec_P : PrimrecPred P := by
  have hR : PrimrecRel (fun p n : ℕ => p.Prime ∧ (2 * n + 4 - p).Prime) :=
    PrimrecPred.and (primrec_prime.comp fst)
      (primrec_prime.comp (nat_sub.comp (nat_add.comp (nat_mul.comp (const 2) snd) (const 4)) fst))
  exact ((PrimrecRel.exists_lt hR).comp
    (nat_add.comp (nat_mul.comp (const 2) Primrec.id) (const 5)) Primrec.id).of_eq fun n => Iff.rfl

theorem isGoldbachSum_iff (n : ℕ) : IsGoldbachSum (2 * n + 4) ↔ P n := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq⟩
    exact ⟨p, by omega, hp, by rwa [show 2 * n + 4 - p = q by omega]⟩
  · rintro ⟨p, _, hp, hq⟩
    exact ⟨p, 2 * n + 4 - p, hp, hq, by
      have := hq.two_le; omega⟩

theorem goldbach_iff_P : BinaryGoldbach ↔ ∀ n, P n := by
  constructor
  · intro h n
    rw [← isGoldbachSum_iff]
    exact h _ ⟨n + 2, by ring⟩ (by omega)
  · intro h m hm h4
    obtain ⟨k, rfl⟩ := hm
    have := (isGoldbachSum_iff (k - 2)).mpr (h (k - 2))
    rwa [show 2 * (k - 2) + 4 = k + k by omega] at this

/-- **Binary Goldbach is `Π⁰₁`**: it is `∀ n, P n` for a primitive recursive `P`. -/
theorem goldbach_pi01 : ∃ Q : ℕ → Prop, PrimrecPred Q ∧ (BinaryGoldbach ↔ ∀ n, Q n) :=
  ⟨P, primrec_P, goldbach_iff_P⟩

instance : DecidablePred P := fun n => by unfold P; infer_instance

/-- A false Goldbach is refuted by one finite, decidable computation. -/
theorem not_goldbach_iff : ¬ BinaryGoldbach ↔ ∃ n, decide (P n) = false := by
  rw [goldbach_iff_P]
  simp

/-- Vacuity and sanity: the test passes at `n = 0, …, 9`, the even numbers `4, …, 22`. -/
theorem P_small : ∀ n < 10, decide (P n) = true := by decide

end LeanLab.Routes.R5100
