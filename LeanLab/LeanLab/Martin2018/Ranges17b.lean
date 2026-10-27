/-
Conj 1.7 of Martin 2018, P0084, kernel-checked further, in chunks: every odd n with
5 < n ≤ 20501 is p + q + r with primes p ≡ q ≡ 2 mod 3.
The search loops over p and over the third prime r, so q = n - p - r is determined; when
n ≡ 1 mod 3 the third prime must be 3, which the old checker in Ranges17 reached only after
scanning all q. Trial division fuel 400 covers every n below 160000.
AI-written Lean code, Claude, run 20261016T2204Z-20593. Checked only by the Lean kernel.
The conjecture is OPEN in general.
-/
import Mathlib
import LeanLab.Martin2018.Ranges17

namespace LeanLab.Martin2018

/-- Trial division with explicit fuel; sound for every fuel. -/
def primeF (f n : ℕ) : Bool := 2 ≤ n && noDivFrom n f 2

theorem primeF_sound {f n : ℕ} (h : primeF f n = true) : n.Prime := by
  simp only [primeF, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hnd⟩ := h
  rw [Nat.prime_def_le_sqrt]
  exact ⟨h2, fun m hm hms hdiv => noDivFrom_sound n f 2 hnd m hm (Nat.le_sqrt.mp hms) hdiv⟩

/-- The goal for one `n`. -/
def Rep17 (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p % 3 = 2 ∧ q % 3 = 2 ∧ p + q + r = n

/-- Search the third prime `r` for fixed `p`. -/
def rF (n p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, r => if n < p + r then false
      else if primeF 400 r && primeF 400 (n - p - r) && (n - p - r) % 3 == 2 then true
      else rF n p fuel (r + 1)

/-- Search `p`. -/
def pF (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, p => if n < p then false
      else if primeF 400 p && p % 3 == 2 && rF n p 60 2 then true
      else pF n fuel (p + 1)

theorem rF_sound (n p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 2) :
    ∀ fuel r, rF n p fuel r = true → Rep17 n := by
  intro fuel
  induction fuel with
  | zero => intro r h; simp [rF] at h
  | succ k ih =>
    intro r h
    simp only [rF] at h
    by_cases h1 : n < p + r
    · rw [if_pos h1] at h; exact absurd h (by simp)
    · rw [if_neg h1] at h
      by_cases h2 : (primeF 400 r && primeF 400 (n - p - r) && (n - p - r) % 3 == 2) = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at h2
        exact ⟨p, n - p - r, r, hp, primeF_sound h2.1.2, primeF_sound h2.1.1, hp3, h2.2,
          by omega⟩
      · rw [if_neg h2] at h; exact ih (r + 1) h

theorem pF_sound (n : ℕ) : ∀ fuel p, pF n fuel p = true → Rep17 n := by
  intro fuel
  induction fuel with
  | zero => intro p h; simp [pF] at h
  | succ k ih =>
    intro p h
    simp only [pF] at h
    by_cases h1 : n < p
    · rw [if_pos h1] at h; exact absurd h (by simp)
    · rw [if_neg h1] at h
      by_cases h2 : (primeF 400 p && p % 3 == 2 && rF n p 60 2) = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at h2
        exact rF_sound n p (primeF_sound h2.1.1) h2.1.2 60 2 h2.2
      · rw [if_neg h2] at h; exact ih (p + 1) h

/-- Check `lo, lo + 2, ..., lo + 2 (k - 1)`. -/
def oddChunk (lo : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => pF (lo + 2 * k) 300 2 && oddChunk lo k

theorem oddChunk_sound (lo : ℕ) : ∀ k, oddChunk lo k = true → ∀ i, i < k → Rep17 (lo + 2 * i) := by
  intro k
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro h i hi
    rw [oddChunk, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge i k with hlt | hge
    · exact ih h.2 i hlt
    · have : i = k := by omega
      subst this; exact pF_sound _ _ _ h.1

/-- Chunk `c` covers the odd numbers from `503 + 1000 c` to `1501 + 1000 c`. -/
def chunkOK (c : ℕ) : Prop := oddChunk (503 + 1000 * c) 500 = true

theorem chunk_0 : chunkOK 0 := by unfold chunkOK; decide +kernel
theorem chunk_1 : chunkOK 1 := by unfold chunkOK; decide +kernel
theorem chunk_2 : chunkOK 2 := by unfold chunkOK; decide +kernel
theorem chunk_3 : chunkOK 3 := by unfold chunkOK; decide +kernel
theorem chunk_4 : chunkOK 4 := by unfold chunkOK; decide +kernel
theorem chunk_5 : chunkOK 5 := by unfold chunkOK; decide +kernel
theorem chunk_6 : chunkOK 6 := by unfold chunkOK; decide +kernel
theorem chunk_7 : chunkOK 7 := by unfold chunkOK; decide +kernel
theorem chunk_8 : chunkOK 8 := by unfold chunkOK; decide +kernel
theorem chunk_9 : chunkOK 9 := by unfold chunkOK; decide +kernel
theorem chunk_10 : chunkOK 10 := by unfold chunkOK; decide +kernel
theorem chunk_11 : chunkOK 11 := by unfold chunkOK; decide +kernel
theorem chunk_12 : chunkOK 12 := by unfold chunkOK; decide +kernel
theorem chunk_13 : chunkOK 13 := by unfold chunkOK; decide +kernel
theorem chunk_14 : chunkOK 14 := by unfold chunkOK; decide +kernel
theorem chunk_15 : chunkOK 15 := by unfold chunkOK; decide +kernel
theorem chunk_16 : chunkOK 16 := by unfold chunkOK; decide +kernel
theorem chunk_17 : chunkOK 17 := by unfold chunkOK; decide +kernel
theorem chunk_18 : chunkOK 18 := by unfold chunkOK; decide +kernel
theorem chunk_19 : chunkOK 19 := by unfold chunkOK; decide +kernel

theorem chunkOK_all : ∀ c, c < 20 → chunkOK c := by
  intro c hc
  interval_cases c
  · exact chunk_0
  · exact chunk_1
  · exact chunk_2
  · exact chunk_3
  · exact chunk_4
  · exact chunk_5
  · exact chunk_6
  · exact chunk_7
  · exact chunk_8
  · exact chunk_9
  · exact chunk_10
  · exact chunk_11
  · exact chunk_12
  · exact chunk_13
  · exact chunk_14
  · exact chunk_15
  · exact chunk_16
  · exact chunk_17
  · exact chunk_18
  · exact chunk_19

/-- Conj 1.7 for every odd `n` with `5 < n ≤ 20501`, zero sorry. -/
theorem conj1_7_upTo_big : ∀ n, n ≤ 20501 → Odd n → 5 < n → Rep17 n := by
  intro n hn ho h5
  have ho' := ho
  obtain ⟨m, rfl⟩ := ho'
  rcases Nat.lt_or_ge (2 * m + 1) 503 with hlt | hge
  · exact conj1_7_upTo _ (by omega) ho h5
  · have hc : (2 * m + 1 - 503) / 1000 < 20 := by omega
    have := oddChunk_sound _ 500 (chunkOK_all _ hc) (((2 * m + 1 - 503) % 1000) / 2) (by omega)
    have e : 503 + 1000 * ((2 * m + 1 - 503) / 1000) + 2 * (((2 * m + 1 - 503) % 1000) / 2)
        = 2 * m + 1 := by omega
    rw [e] at this; exact this

end LeanLab.Martin2018
