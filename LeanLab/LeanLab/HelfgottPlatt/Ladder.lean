/-
The ladder reduction of Helfgott and Platt, P0006, unit U-0341, run 20261017T1803Z-21479.
If binary Goldbach holds up to B and odd primes 3 = p₀ < p₁ < ... < p_k have every gap at most
B - 4, then ternary Goldbach holds up to p_k + B: for odd n, take the largest pᵢ ≤ n - 4, then
4 ≤ n - pᵢ ≤ B. This is the reduction P0006 uses with B = 4e18; here it is proved in general.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.Verifications.Top50.FastCheck

namespace LeanLab.HelfgottPlatt

open LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Fast

/-- One rung of the ladder: the next prime is larger and at most `B - 4` above. -/
def LadderStep (B a b : ℕ) : Prop := a < b ∧ b ≤ a + (B - 4)

/-- One step: an odd `n` with `a + 4 ≤ n ≤ a + B`, `a` an odd prime, is a sum of three primes. -/
theorem ternary_step {B : ℕ} (hB : EvenGoldbachUpTo B) {a n : ℕ} (ha : a.Prime) (ha3 : 3 ≤ a)
    (hn : Odd n) (h1 : a + 4 ≤ n) (h2 : n ≤ a + B) : IsTernarySum n := by
  have hao : Odd a := ha.odd_of_ne_two (by omega)
  have he : Even (n - a) := Nat.Odd.sub_odd hn hao
  obtain ⟨p, q, hp, hq, hpq⟩ := hB (n - a) he (by omega) (by omega)
  exact ⟨a, p, q, ha, hp, hq, by omega⟩

theorem getLastD_cons' (a b : ℕ) (t : List ℕ) : (b :: t).getLastD a = t.getLastD b := by
  cases t with
  | nil => rfl
  | cons c t => simp [List.getLastD]

/-- The ladder lemma, by induction along the ladder. -/
theorem ternary_of_ladder_aux {B : ℕ} (hB : EvenGoldbachUpTo B) :
    ∀ (t : List ℕ) (a : ℕ), a.Prime → 3 ≤ a → (∀ p ∈ t, p.Prime) →
      (a :: t).IsChain (LadderStep B) →
      ∀ n, Odd n → a + 4 ≤ n → n ≤ t.getLastD a + B → IsTernarySum n := by
  intro t
  induction t with
  | nil =>
    intro a ha ha3 _ _ n hn h1 h2
    exact ternary_step hB ha ha3 hn h1 (by simpa using h2)
  | cons b t ih =>
    intro a ha ha3 ht hc n hn h1 h2
    rw [List.isChain_cons_cons] at hc
    obtain ⟨⟨hab, hba⟩, hc⟩ := hc
    have hbp : b.Prime := ht b (by simp)
    by_cases hnb : b + 4 ≤ n
    · exact ih b hbp (by omega) (fun p hp => ht p (List.mem_cons_of_mem _ hp)) hc n hn hnb
        (by rw [getLastD_cons'] at h2; exact h2)
    · exact ternary_step hB ha ha3 hn h1 (by omega)

/-- The ladder lemma of P0006 in general form. -/
theorem ternary_of_ladder {B X : ℕ} (hB : EvenGoldbachUpTo B) (t : List ℕ)
    (ht : ∀ p ∈ t, p.Prime) (hc : (3 :: t).IsChain (LadderStep B))
    (hX : X ≤ t.getLastD 3 + B) : TernaryGoldbachUpTo X := by
  intro n hn h7 hnX
  exact ternary_of_ladder_aux hB t 3 Nat.prime_three le_rfl ht hc n hn (by omega) (by omega)

/-! ### Boolean checks for the kernel -/

/-- Boolean chain check. -/
def chainB (B : ℕ) : List ℕ → Bool
  | a :: b :: t => (decide (a < b) && decide (b ≤ a + (B - 4))) && chainB B (b :: t)
  | _ => true

theorem chainB_sound (B : ℕ) : ∀ l : List ℕ, chainB B l = true → l.IsChain (LadderStep B)
  | [], _ => List.IsChain.nil
  | [_], _ => List.IsChain.singleton _
  | a :: b :: t, h => by
    simp only [chainB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.IsChain.cons_cons ⟨h.1.1, h.1.2⟩ (chainB_sound B (b :: t) h.2)

/-- Boolean primality for the ladder, sound below 10^8. -/
def okB (m : ℕ) : Bool := decide (2 ≤ m) && decide (m < 10 ^ 8) && td m P10k

theorem prime_of_okB {m : ℕ} (h : okB m = true) : m.Prime := by
  simp only [okB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact prime_of_td h.1.1 h.1.2 h.2

theorem all_prime_of {L : List ℕ} (h : L.all okB = true) : ∀ p ∈ L, p.Prime :=
  fun p hp => prime_of_okB (List.all_eq_true.mp h p hp)

end LeanLab.HelfgottPlatt
