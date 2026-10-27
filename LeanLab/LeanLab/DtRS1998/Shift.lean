/-
Deshouillers, te Riele, Saouter 1998, P0037, unit U-0936, run 20261018T1002Z-987.
Soundness of a shifted window check for even Goldbach in an interval far from 0:
every even n = B + x with x in a window is q + p, q = B - d a large prime with a Lucas
certificate, p = x + d a small prime read off the lab's window prime bitmap `wpm2`.
The covered set is an OR of right shifts of one bitmap, one equality of naturals per window.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.BitSieve2
import LeanLab.Saouter1998.Lucas

namespace LeanLab.DtRS1998

open LeanLab.Verifications.Top50.Bits

/-- Bit `j` set when bit `j + s` of `P` is set for some shift `s ∈ S`. -/
def gmR (P : ℕ) : List ℕ → ℕ
  | [] => 0
  | s :: t => (P >>> s) ||| gmR P t

theorem of_gmR (P : ℕ) : ∀ (S : List ℕ) (j : ℕ), (gmR P S).testBit j = true →
    ∃ s ∈ S, P.testBit (j + s) = true := by
  intro S
  induction S with
  | nil => intro j h; simp [gmR] at h
  | cons a t ih =>
    intro j h
    simp only [gmR, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftRight] at h
    rcases h with h | h
    · exact ⟨a, by simp, by rwa [Nat.add_comm] at h⟩
    · obtain ⟨s, hs, h3⟩ := ih j h
      exact ⟨s, List.mem_cons_of_mem _ hs, h3⟩

/-- Every even `n` with `a ≤ n ≤ b` is a sum of two primes. -/
def GoldbachOn (a b : ℕ) : Prop := ∀ n, a ≤ n → n ≤ b → 2 ∣ n → IsGoldbachSum n

theorem goldbachOn_join {a b c : ℕ} (hbe : 2 ∣ b) (h1 : GoldbachOn a b)
    (h2 : GoldbachOn (b + 2) c) : GoldbachOn a c := by
  intro n ha hc he
  by_cases hb : n ≤ b
  · exact h1 n ha hb he
  · exact h2 n (by omega) hc he

/-- Soundness of one shifted window. -/
theorem win_sound {Bq x0 x1 lo W : ℕ} {Ds : List ℕ} (hB : 2 ∣ Bq) (hx0 : 2 ∣ x0)
    (h2 : 2 ≤ lo) (hW : lo + W ≤ B2)
    (hlo : ∀ d ∈ Ds, lo ≤ x0 + d) (hQ : ∀ d ∈ Ds, d ≤ Bq ∧ (Bq - d).Prime)
    (h : wem 0 0 (x1 - x0) &&& gmR (wpm2 lo W) (Ds.map (fun d => x0 + d - lo)) =
      wem 0 0 (x1 - x0)) :
    GoldbachOn (Bq + x0) (Bq + x1) := by
  intro n ha hb he
  set j := n - (Bq + x0) with hj
  have hje : 2 ∣ j - 0 := by
    rw [Nat.sub_zero, hj]; exact Nat.dvd_sub he (Nat.dvd_add hB hx0)
  have h1 := testBit_wem (lo := 0) (A := 0) (B := x1 - x0) (n := j) le_rfl (Nat.zero_le _)
    (by omega) hje
  rw [Nat.sub_zero, ← h, Nat.testBit_and, Bool.and_eq_true] at h1
  obtain ⟨s, hs, hp⟩ := of_gmR _ _ j h1.2
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hs
  have hpr := prime_of_wpm2 h2 hW hp
  obtain ⟨hdB, hq⟩ := hQ d hd
  have hl := hlo d hd
  refine ⟨Bq - d, lo + (j + (x0 + d - lo)), hq, hpr, ?_⟩
  omega

end LeanLab.DtRS1998
