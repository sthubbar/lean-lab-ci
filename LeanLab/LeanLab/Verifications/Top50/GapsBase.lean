/-
P0005 and OEIS A002386: the maximal prime gap records below 4e18, shared machinery.
`IsGapAt p g`: p and p + g are prime and nothing strictly between is prime, so p + g is the
next prime after p. `gapC` checks a divisor for each p + k, 0 < k < g.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.Base

namespace LeanLab.Verifications.Top50.Gaps

open LeanLab.Verifications.OeSHP (certOK not_prime_of_certOK)

/-- p + g is the prime that follows the prime p. -/
def IsGapAt (p g : ℕ) : Prop :=
  p.Prime ∧ (p + g).Prime ∧ ∀ k, 0 < k → k < g → ¬ (p + k).Prime

def gapC (p : ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => true
  | fuel + 1, k, ds =>
    match ds with
    | d :: ds' => certOK (p + k) d && gapC p fuel (k + 1) ds'
    | [] => false

theorem gapC_sound (p : ℕ) : ∀ fuel k ds, gapC p fuel k ds = true →
    ∀ j, k ≤ j → j < k + fuel → ¬ (p + j).Prime := by
  intro fuel
  induction fuel with
  | zero => intro k ds _ j h1 h2; omega
  | succ n ih =>
    intro k ds h j h1 h2
    match ds, h with
    | (d :: ds'), h =>
      simp only [gapC, Bool.and_eq_true] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact not_prime_of_certOK h.1
      · exact ih (k + 1) ds' h.2 j hlt (by omega)

theorem isGapAt_of (p g : ℕ) (hp : p.Prime) (hq : (p + g).Prime) (ds : List ℕ)
    (hc : gapC p (g - 1) 1 ds = true) : IsGapAt p g :=
  ⟨hp, hq, fun k hk hkg => gapC_sound p (g - 1) 1 ds hc k hk (by omega)⟩

end LeanLab.Verifications.Top50.Gaps
