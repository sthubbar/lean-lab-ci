/-
P0017 Richstein 2001, Sections 2, 3 and 5, pages 1746 to 1747: the arithmetic of the segmented
sieve, checked in Lean. Read in Claude in Chrome 2026-10-18, run 20261018T1103Z-12430, U-0937.
Π5 is the product of the first five odd primes. The interval [1, 4·10^14] is split into
intervals I_k of length 2^26 Π5, about 10^12, with 0 ≤ k ≤ 396; each I_k into segments of length
2^t Π5, mapped onto 32-bit words, bit j of word m standing for the odd number 2^6 m + 2j + 1
inside the segment. Multiples l p of a sieving prime are visited by the step cycle
2p, 4p, 6p, 2p, 6p, 4p, 2p, 4p. With 9 ≤ t ≤ 11 the arrays A and C take at most 4 MB.
Every statement below is PROVED, zero sorry; none is a mathematical result of the paper, they
check that its printed bookkeeping is consistent.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Richstein2001

/-- Π5, the product of the first five odd primes. -/
def Pi5 : ℕ := 3 * 5 * 7 * 11 * 13

theorem Pi5_eq : Pi5 = 15015 := rfl

/-- The interval length 2^26 Π5. -/
def lenI : ℕ := 2 ^ 26 * Pi5

/-- 2^26 Π5 is about 10^12, within 0.8 percent. -/
theorem lenI_approx : lenI = 1007639592960 ∧ 10 ^ 12 < lenI ∧ lenI < 1008 * 10 ^ 9 := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-- 0 ≤ k ≤ 396 is exactly what is needed: 396 intervals fall short of 4·10^14, 397 cover it. -/
theorem k_range : 396 * lenI < 4 * 10 ^ 14 ∧ 4 * 10 ^ 14 ≤ 397 * lenI := by
  constructor <;> decide

/-- Segments of length 2^t Π5, t ≤ 26, tile I_k: there are 2^(26 - t) of them. -/
theorem segments_tile (t : ℕ) (ht : t ≤ 26) : 2 ^ (26 - t) * (2 ^ t * Pi5) = lenI := by
  unfold lenI
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel ht]

/-- The bit map: for 6 ≤ t, bit j < 32 of word m < 2^(t-6) Π5 stands for 2^6 m + 2j + 1, and
this hits every odd number below 2^t Π5 exactly once. -/
theorem bitmap_bij (t : ℕ) (ht : 6 ≤ t) (x : ℕ) (hx : x < 2 ^ t * Pi5) (hodd : x % 2 = 1) :
    ∃! mj : ℕ × ℕ, mj.1 < 2 ^ (t - 6) * Pi5 ∧ mj.2 < 32 ∧ 2 ^ 6 * mj.1 + 2 * mj.2 + 1 = x := by
  have h64 : 2 ^ t * Pi5 = 64 * (2 ^ (t - 6) * Pi5) := by
    rw [← mul_assoc]; congr 1
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_add, Nat.add_sub_cancel' ht]
  refine ⟨(x / 64, (x % 64) / 2), ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [h64] at hx
    exact Nat.div_lt_of_lt_mul (by simpa [mul_comm] using hx)
  · omega
  · have := Nat.div_add_mod x 64
    have : x % 64 % 2 = 1 := by omega
    norm_num
    omega
  · rintro ⟨m, j⟩ ⟨_, hj, he⟩
    simp only at hj he
    simp only [Prod.mk.injEq]
    norm_num at he
    omega

/-- The wheel: from l ≡ 17 mod 30 the steps 2, 4, 6, 2, 6, 4, 2, 4 in l run through exactly the
eight residues prime to 30, so the multiples l p skipped are those with 3, 5 or 2 dividing l. -/
def wheel : List ℕ := [2, 4, 6, 2, 6, 4, 2, 4]

def wheelRes : List ℕ := (List.range 8).map (fun i => (17 + ((wheel.take i).sum)) % 30)

theorem wheel_sum : wheel.sum = 30 := rfl

theorem wheelRes_eq : wheelRes = [17, 19, 23, 29, 1, 7, 11, 13] := by decide

theorem wheel_units : wheelRes.toFinset = (Finset.range 30).filter (fun l => Nat.Coprime l 30) := by
  decide

/-- Memory, Section 5: with t ≤ 11, A and C each have 2^(t-6) Π5 words of 4 bytes, together at
most 3843840 bytes, below 4·10^6 and below 4·2^20. -/
theorem memory_bound (t : ℕ) (ht : t ≤ 11) :
    2 * (4 * (2 ^ (t - 6) * Pi5)) ≤ 3843840 ∧ 3843840 < 4 * 10 ^ 6 ∧ 3843840 < 4 * 2 ^ 20 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  have : 2 ^ (t - 6) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold Pi5
  omega

/-- Throughput, Section 5: about 10^7 even numbers a second for about 130 days. The even numbers
below 4·10^14 are 2·10^14, which at 130 days needs between 1.7·10^7 and 1.8·10^7 a second. -/
theorem throughput : 17 * 10 ^ 6 * (130 * 86400) < 2 * 10 ^ 14 ∧
    2 * 10 ^ 14 < 18 * 10 ^ 6 * (130 * 86400) := by
  constructor <;> norm_num

end LeanLab.Richstein2001
