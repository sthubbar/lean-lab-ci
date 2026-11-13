/-
AI wrote this Lean code for FREE-nv-minimax task342.
Self-contained shifted window sieve for the fixed alternative offset list.
The window bitmap is computed from the primes below the square root of its endpoint.
Binary Goldbach is open.
-/
import Mathlib
import LeanLab.Verifications.Top50.BitSieve

namespace LeanLab.DtRS1998.CoverUpper342Bitmap

open LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The sieving primes for a window ending at `L`. -/
def D2 (L : ℕ) : List ℕ :=
  (List.range (Nat.sqrt L + 1)).filter (fun p => p.Prime)

/-- Every possible prime divisor of a number below `L` occurs in `D2 L`. -/
theorem mem_D2 {L p : ℕ} (hp : p.Prime) (hpL : p * p < L) : p ∈ D2 L := by
  unfold D2
  rw [List.mem_filter]
  constructor
  · apply List.mem_range.mpr
    have hp' : p ≤ Nat.sqrt L := (Nat.le_sqrt).2 (Nat.le_of_lt hpL)
    omega
  · simpa only [decide_eq_true_eq] using hp

/-- Window prime bitmap with the sieving list `D2`. -/
def wpm2 (lo W : ℕ) : ℕ :=
  (wsieve lo W (D2 (lo + W)) % 2 ^ W) ^^^ (2 ^ W - 1)

/-- A set bit in the window bitmap certifies the corresponding prime. -/
theorem prime_of_wpm2 {lo W i : ℕ} (h2 : 2 ≤ lo)
    (h : (wpm2 lo W).testBit i = true) : (lo + i).Prime := by
  simp only [wpm2, Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one] at h
  by_cases hiW : i < W
  · simp only [hiW, decide_true, Bool.true_and] at h
    by_contra hp
    set m := lo + i with hm
    have hmf := Nat.minFac_prime (show m ≠ 1 by omega)
    have hsq : m.minFac * m.minFac ≤ m := by
      have h := Nat.minFac_sq_le_self (show 0 < m by omega) hp
      simpa [sq] using h
    have hb := wsieve_of_dvd lo W m m.minFac hmf.one_lt.le hsq (by omega) (by omega)
      (Nat.minFac_dvd m) (D2 (lo + W)) (mem_D2 hmf (by omega))
    rw [show m - lo = i by omega] at hb
    rw [hb] at h
    simp at h
  · simp [hiW] at h

/-- Bit `j` is set when bit `j + s` is set for some shift `s` in the list. -/
def gmR (P : ℕ) : List ℕ → ℕ
  | [] => 0
  | s :: t => (P >>> s) ||| gmR P t

/-- A set bit in `gmR` comes from one of the listed shifts. -/
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

/-- An accepted shifted bitmap supplies a prime difference. -/
theorem offset_window {x0 x1 lo W : ℕ} {Ds : List ℕ}
    (h2 : 2 ≤ lo)
    (hlo : ∀ d ∈ Ds, lo ≤ x0 + d)
    (h : wem 0 0 (x1 - x0) &&& gmR (wpm2 lo W) (Ds.map (fun d => x0 + d - lo)) =
      wem 0 0 (x1 - x0))
    {x : ℕ} (hx0 : x0 ≤ x) (hx1 : x ≤ x1) (he : 2 ∣ x - x0) :
    ∃ d ∈ Ds, (x + d).Prime := by
  have hbit := testBit_wem (lo := 0) (A := 0) (B := x1 - x0)
    (n := x - x0) le_rfl (Nat.zero_le _) (by omega) (by simpa using he)
  rw [Nat.sub_zero, ← h, Nat.testBit_and, Bool.and_eq_true] at hbit
  obtain ⟨s, hs, hp⟩ := of_gmR _ _ _ hbit.2
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hs
  have hprime := prime_of_wpm2 h2 hp
  have hl := hlo d hd
  refine ⟨d, hd, ?_⟩
  convert hprime using 1 <;> omega

#print axioms prime_of_wpm2
#print axioms of_gmR
#print axioms offset_window

end LeanLab.DtRS1998.CoverUpper342Bitmap
