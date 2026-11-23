/-
AI wrote this Lean code, Claude, ROUTE BURST S76, burst-20261122, step xi_1e8_split.
Schoenfeld 1976, Math. Comp. 30, p. 340 line 1: ξ = 10⁸ in display 6.19b.
This file splits the three numerical LEAFs of SchoenfeldXiS70 into smaller faithful
numerical LEAFs and proves the glue:
* π 10⁸ is a sum of 100 block prime counts over [k·10⁶, k·10⁶ + 10⁶), each a LEAF.
* θ 10⁸ is a sum of 100 block sums of log p over the same blocks, each an enclosure LEAF
  of width 10⁻⁶.
* li 10⁸ is li 2 plus ∫ dt / log t over [2, 10] and the decades [10^j, 10^(j+1)],
  j from 1 to 7, each an enclosure LEAF of width 10⁻⁶.
Block values computed with Python, numpy and mpmath at 40 digits, script in
notes/burst-20261122/BS2022GRH-xi_1e8_split.md. Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.SchoenfeldXiS70

namespace LeanLab.BS2022GRH.SchoenfeldXiBlocksS76
open Real Finset LeanLab.BS2022GRH.PaperInputs148 LeanLab.BS2022GRH

/-- The number of primes `p` with `a ≤ p < b`, a block of the count π 10⁸ of
Schoenfeld 1976 p. 340 line 1. -/
def blockPrimes (a b : ℕ) : ℕ := ((Ico a b).filter Nat.Prime).card

/-- The sum of `log p` over primes `a ≤ p < b`, a block of θ 10⁸ of
Schoenfeld 1976 p. 340 line 1. -/
noncomputable def thetaBlock (a b : ℕ) : ℝ := ∑ p ∈ (Ico a b).filter Nat.Prime, log p

/-- PROVED: block counts are additive. -/
lemma blockPrimes_add {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) :
    blockPrimes a b + blockPrimes b c = blockPrimes a c := by
  unfold blockPrimes
  rw [card_filter, card_filter, card_filter]
  exact Finset.sum_Ico_consecutive _ h1 h2

/-- PROVED: block log sums are additive. -/
lemma thetaBlock_add {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) :
    thetaBlock a b + thetaBlock b c = thetaBlock a c := by
  unfold thetaBlock
  rw [sum_filter, sum_filter, sum_filter]
  exact Finset.sum_Ico_consecutive _ h1 h2

/-- PROVED: a sum of consecutive equal blocks. -/
lemma blockPrimes_sum (S n : ℕ) :
    ∑ k ∈ range n, blockPrimes (k * S) ((k + 1) * S) = blockPrimes 0 (n * S) := by
  induction n with
  | zero => simp [blockPrimes]
  | succ n ih =>
    rw [sum_range_succ, ih, blockPrimes_add (Nat.zero_le _) (Nat.mul_le_mul_right _ (by omega))]

/-- PROVED: a sum of consecutive equal blocks. -/
lemma thetaBlock_sum (S n : ℕ) :
    ∑ k ∈ range n, thetaBlock (k * S) ((k + 1) * S) = thetaBlock 0 (n * S) := by
  induction n with
  | zero => simp [thetaBlock]
  | succ n ih =>
    rw [sum_range_succ, ih, thetaBlock_add (Nat.zero_le _) (Nat.mul_le_mul_right _ (by omega))]

attribute [local irreducible] blockPrimes thetaBlock

/-- PROVED: `10⁸` is not prime. -/
lemma not_prime_1e8 : ¬ Nat.Prime 100000000 := by
  intro h
  have := h.eq_one_or_self_of_dvd 2 (by norm_num)
  omega

/-- PROVED: the singleton block at `10⁸` holds no prime. -/
lemma filter_last : (Ico 100000000 100000001).filter Nat.Prime = ∅ := by
  rw [Nat.Ico_succ_singleton, filter_singleton, if_neg not_prime_1e8]

/-- PROVED: arithmetic glue for the last singleton block. -/
lemma glue_last {B B1 L s : ℕ} (hall : B + L = B1) (hlast : L = 0) (hsum : s = B) : B1 = s := by
  subst hlast; subst hsum; simpa using hall.symm

/-- PROVED: `⌊10⁸⌋₊ = 10⁸`. -/
lemma floor_1e8 : ⌊(10 ^ 8 : ℝ)⌋₊ = 100000000 := by
  rw [show (10 ^ 8 : ℝ) = ((100000000 : ℕ) : ℝ) by norm_num, Nat.floor_natCast]

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 0: the number of
primes in [0, 1000000) is 78498, computed by sieve. MEDIUM -/
theorem blockPrimes_0 : blockPrimes 0 1000000 = 78498 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 1: the number of
primes in [1000000, 2000000) is 70435, computed by sieve. MEDIUM -/
theorem blockPrimes_1 : blockPrimes 1000000 2000000 = 70435 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 2: the number of
primes in [2000000, 3000000) is 67883, computed by sieve. MEDIUM -/
theorem blockPrimes_2 : blockPrimes 2000000 3000000 = 67883 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 3: the number of
primes in [3000000, 4000000) is 66330, computed by sieve. MEDIUM -/
theorem blockPrimes_3 : blockPrimes 3000000 4000000 = 66330 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 4: the number of
primes in [4000000, 5000000) is 65367, computed by sieve. MEDIUM -/
theorem blockPrimes_4 : blockPrimes 4000000 5000000 = 65367 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 5: the number of
primes in [5000000, 6000000) is 64336, computed by sieve. MEDIUM -/
theorem blockPrimes_5 : blockPrimes 5000000 6000000 = 64336 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 6: the number of
primes in [6000000, 7000000) is 63799, computed by sieve. MEDIUM -/
theorem blockPrimes_6 : blockPrimes 6000000 7000000 = 63799 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 7: the number of
primes in [7000000, 8000000) is 63129, computed by sieve. MEDIUM -/
theorem blockPrimes_7 : blockPrimes 7000000 8000000 = 63129 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 8: the number of
primes in [8000000, 9000000) is 62712, computed by sieve. MEDIUM -/
theorem blockPrimes_8 : blockPrimes 8000000 9000000 = 62712 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 9: the number of
primes in [9000000, 10000000) is 62090, computed by sieve. MEDIUM -/
theorem blockPrimes_9 : blockPrimes 9000000 10000000 = 62090 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 10: the number of
primes in [10000000, 11000000) is 61938, computed by sieve. MEDIUM -/
theorem blockPrimes_10 : blockPrimes 10000000 11000000 = 61938 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 11: the number of
primes in [11000000, 12000000) is 61543, computed by sieve. MEDIUM -/
theorem blockPrimes_11 : blockPrimes 11000000 12000000 = 61543 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 12: the number of
primes in [12000000, 13000000) is 61192, computed by sieve. MEDIUM -/
theorem blockPrimes_12 : blockPrimes 12000000 13000000 = 61192 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 13: the number of
primes in [13000000, 14000000) is 60825, computed by sieve. MEDIUM -/
theorem blockPrimes_13 : blockPrimes 13000000 14000000 = 60825 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 14: the number of
primes in [14000000, 15000000) is 60627, computed by sieve. MEDIUM -/
theorem blockPrimes_14 : blockPrimes 14000000 15000000 = 60627 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 15: the number of
primes in [15000000, 16000000) is 60426, computed by sieve. MEDIUM -/
theorem blockPrimes_15 : blockPrimes 15000000 16000000 = 60426 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 16: the number of
primes in [16000000, 17000000) is 60184, computed by sieve. MEDIUM -/
theorem blockPrimes_16 : blockPrimes 16000000 17000000 = 60184 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 17: the number of
primes in [17000000, 18000000) is 60053, computed by sieve. MEDIUM -/
theorem blockPrimes_17 : blockPrimes 17000000 18000000 = 60053 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 18: the number of
primes in [18000000, 19000000) is 59683, computed by sieve. MEDIUM -/
theorem blockPrimes_18 : blockPrimes 18000000 19000000 = 59683 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 19: the number of
primes in [19000000, 20000000) is 59557, computed by sieve. MEDIUM -/
theorem blockPrimes_19 : blockPrimes 19000000 20000000 = 59557 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 20: the number of
primes in [20000000, 21000000) is 59336, computed by sieve. MEDIUM -/
theorem blockPrimes_20 : blockPrimes 20000000 21000000 = 59336 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 21: the number of
primes in [21000000, 22000000) is 59318, computed by sieve. MEDIUM -/
theorem blockPrimes_21 : blockPrimes 21000000 22000000 = 59318 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 22: the number of
primes in [22000000, 23000000) is 58960, computed by sieve. MEDIUM -/
theorem blockPrimes_22 : blockPrimes 22000000 23000000 = 58960 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 23: the number of
primes in [23000000, 24000000) is 58901, computed by sieve. MEDIUM -/
theorem blockPrimes_23 : blockPrimes 23000000 24000000 = 58901 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 24: the number of
primes in [24000000, 25000000) is 58805, computed by sieve. MEDIUM -/
theorem blockPrimes_24 : blockPrimes 24000000 25000000 = 58805 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 25: the number of
primes in [25000000, 26000000) is 58600, computed by sieve. MEDIUM -/
theorem blockPrimes_25 : blockPrimes 25000000 26000000 = 58600 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 26: the number of
primes in [26000000, 27000000) is 58538, computed by sieve. MEDIUM -/
theorem blockPrimes_26 : blockPrimes 26000000 27000000 = 58538 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 27: the number of
primes in [27000000, 28000000) is 58365, computed by sieve. MEDIUM -/
theorem blockPrimes_27 : blockPrimes 27000000 28000000 = 58365 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 28: the number of
primes in [28000000, 29000000) is 58246, computed by sieve. MEDIUM -/
theorem blockPrimes_28 : blockPrimes 28000000 29000000 = 58246 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 29: the number of
primes in [29000000, 30000000) is 58183, computed by sieve. MEDIUM -/
theorem blockPrimes_29 : blockPrimes 29000000 30000000 = 58183 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 30: the number of
primes in [30000000, 31000000) is 58120, computed by sieve. MEDIUM -/
theorem blockPrimes_30 : blockPrimes 30000000 31000000 = 58120 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 31: the number of
primes in [31000000, 32000000) is 57836, computed by sieve. MEDIUM -/
theorem blockPrimes_31 : blockPrimes 31000000 32000000 = 57836 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 32: the number of
primes in [32000000, 33000000) is 57852, computed by sieve. MEDIUM -/
theorem blockPrimes_32 : blockPrimes 32000000 33000000 = 57852 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 33: the number of
primes in [33000000, 34000000) is 57712, computed by sieve. MEDIUM -/
theorem blockPrimes_33 : blockPrimes 33000000 34000000 = 57712 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 34: the number of
primes in [34000000, 35000000) is 57396, computed by sieve. MEDIUM -/
theorem blockPrimes_34 : blockPrimes 34000000 35000000 = 57396 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 35: the number of
primes in [35000000, 36000000) is 57487, computed by sieve. MEDIUM -/
theorem blockPrimes_35 : blockPrimes 35000000 36000000 = 57487 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 36: the number of
primes in [36000000, 37000000) is 57361, computed by sieve. MEDIUM -/
theorem blockPrimes_36 : blockPrimes 36000000 37000000 = 57361 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 37: the number of
primes in [37000000, 38000000) is 57343, computed by sieve. MEDIUM -/
theorem blockPrimes_37 : blockPrimes 37000000 38000000 = 57343 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 38: the number of
primes in [38000000, 39000000) is 57436, computed by sieve. MEDIUM -/
theorem blockPrimes_38 : blockPrimes 38000000 39000000 = 57436 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 39: the number of
primes in [39000000, 40000000) is 57252, computed by sieve. MEDIUM -/
theorem blockPrimes_39 : blockPrimes 39000000 40000000 = 57252 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 40: the number of
primes in [40000000, 41000000) is 57102, computed by sieve. MEDIUM -/
theorem blockPrimes_40 : blockPrimes 40000000 41000000 = 57102 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 41: the number of
primes in [41000000, 42000000) is 56864, computed by sieve. MEDIUM -/
theorem blockPrimes_41 : blockPrimes 41000000 42000000 = 56864 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 42: the number of
primes in [42000000, 43000000) is 56915, computed by sieve. MEDIUM -/
theorem blockPrimes_42 : blockPrimes 42000000 43000000 = 56915 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 43: the number of
primes in [43000000, 44000000) is 56849, computed by sieve. MEDIUM -/
theorem blockPrimes_43 : blockPrimes 43000000 44000000 = 56849 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 44: the number of
primes in [44000000, 45000000) is 56776, computed by sieve. MEDIUM -/
theorem blockPrimes_44 : blockPrimes 44000000 45000000 = 56776 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 45: the number of
primes in [45000000, 46000000) is 56893, computed by sieve. MEDIUM -/
theorem blockPrimes_45 : blockPrimes 45000000 46000000 = 56893 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 46: the number of
primes in [46000000, 47000000) is 56640, computed by sieve. MEDIUM -/
theorem blockPrimes_46 : blockPrimes 46000000 47000000 = 56640 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 47: the number of
primes in [47000000, 48000000) is 56451, computed by sieve. MEDIUM -/
theorem blockPrimes_47 : blockPrimes 47000000 48000000 = 56451 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 48: the number of
primes in [48000000, 49000000) is 56387, computed by sieve. MEDIUM -/
theorem blockPrimes_48 : blockPrimes 48000000 49000000 = 56387 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 49: the number of
primes in [49000000, 50000000) is 56603, computed by sieve. MEDIUM -/
theorem blockPrimes_49 : blockPrimes 49000000 50000000 = 56603 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 50: the number of
primes in [50000000, 51000000) is 56360, computed by sieve. MEDIUM -/
theorem blockPrimes_50 : blockPrimes 50000000 51000000 = 56360 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 51: the number of
primes in [51000000, 52000000) is 56349, computed by sieve. MEDIUM -/
theorem blockPrimes_51 : blockPrimes 51000000 52000000 = 56349 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 52: the number of
primes in [52000000, 53000000) is 56209, computed by sieve. MEDIUM -/
theorem blockPrimes_52 : blockPrimes 52000000 53000000 = 56209 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 53: the number of
primes in [53000000, 54000000) is 56151, computed by sieve. MEDIUM -/
theorem blockPrimes_53 : blockPrimes 53000000 54000000 = 56151 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 54: the number of
primes in [54000000, 55000000) is 55997, computed by sieve. MEDIUM -/
theorem blockPrimes_54 : blockPrimes 54000000 55000000 = 55997 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 55: the number of
primes in [55000000, 56000000) is 56130, computed by sieve. MEDIUM -/
theorem blockPrimes_55 : blockPrimes 55000000 56000000 = 56130 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 56: the number of
primes in [56000000, 57000000) is 56105, computed by sieve. MEDIUM -/
theorem blockPrimes_56 : blockPrimes 56000000 57000000 = 56105 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 57: the number of
primes in [57000000, 58000000) is 55901, computed by sieve. MEDIUM -/
theorem blockPrimes_57 : blockPrimes 57000000 58000000 = 55901 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 58: the number of
primes in [58000000, 59000000) is 55978, computed by sieve. MEDIUM -/
theorem blockPrimes_58 : blockPrimes 58000000 59000000 = 55978 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 59: the number of
primes in [59000000, 60000000) is 55801, computed by sieve. MEDIUM -/
theorem blockPrimes_59 : blockPrimes 59000000 60000000 = 55801 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 60: the number of
primes in [60000000, 61000000) is 55930, computed by sieve. MEDIUM -/
theorem blockPrimes_60 : blockPrimes 60000000 61000000 = 55930 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 61: the number of
primes in [61000000, 62000000) is 55555, computed by sieve. MEDIUM -/
theorem blockPrimes_61 : blockPrimes 61000000 62000000 = 55555 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 62: the number of
primes in [62000000, 63000000) is 55706, computed by sieve. MEDIUM -/
theorem blockPrimes_62 : blockPrimes 62000000 63000000 = 55706 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 63: the number of
primes in [63000000, 64000000) is 55780, computed by sieve. MEDIUM -/
theorem blockPrimes_63 : blockPrimes 63000000 64000000 = 55780 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 64: the number of
primes in [64000000, 65000000) is 55468, computed by sieve. MEDIUM -/
theorem blockPrimes_64 : blockPrimes 64000000 65000000 = 55468 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 65: the number of
primes in [65000000, 66000000) is 55569, computed by sieve. MEDIUM -/
theorem blockPrimes_65 : blockPrimes 65000000 66000000 = 55569 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 66: the number of
primes in [66000000, 67000000) is 55644, computed by sieve. MEDIUM -/
theorem blockPrimes_66 : blockPrimes 66000000 67000000 = 55644 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 67: the number of
primes in [67000000, 68000000) is 55575, computed by sieve. MEDIUM -/
theorem blockPrimes_67 : blockPrimes 67000000 68000000 = 55575 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 68: the number of
primes in [68000000, 69000000) is 55332, computed by sieve. MEDIUM -/
theorem blockPrimes_68 : blockPrimes 68000000 69000000 = 55332 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 69: the number of
primes in [69000000, 70000000) is 55390, computed by sieve. MEDIUM -/
theorem blockPrimes_69 : blockPrimes 69000000 70000000 = 55390 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 70: the number of
primes in [70000000, 71000000) is 55309, computed by sieve. MEDIUM -/
theorem blockPrimes_70 : blockPrimes 70000000 71000000 = 55309 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 71: the number of
primes in [71000000, 72000000) is 55285, computed by sieve. MEDIUM -/
theorem blockPrimes_71 : blockPrimes 71000000 72000000 = 55285 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 72: the number of
primes in [72000000, 73000000) is 55431, computed by sieve. MEDIUM -/
theorem blockPrimes_72 : blockPrimes 72000000 73000000 = 55431 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 73: the number of
primes in [73000000, 74000000) is 55165, computed by sieve. MEDIUM -/
theorem blockPrimes_73 : blockPrimes 73000000 74000000 = 55165 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 74: the number of
primes in [74000000, 75000000) is 55050, computed by sieve. MEDIUM -/
theorem blockPrimes_74 : blockPrimes 74000000 75000000 = 55050 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 75: the number of
primes in [75000000, 76000000) is 55307, computed by sieve. MEDIUM -/
theorem blockPrimes_75 : blockPrimes 75000000 76000000 = 55307 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 76: the number of
primes in [76000000, 77000000) is 54924, computed by sieve. MEDIUM -/
theorem blockPrimes_76 : blockPrimes 76000000 77000000 = 54924 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 77: the number of
primes in [77000000, 78000000) is 55009, computed by sieve. MEDIUM -/
theorem blockPrimes_77 : blockPrimes 77000000 78000000 = 55009 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 78: the number of
primes in [78000000, 79000000) is 54900, computed by sieve. MEDIUM -/
theorem blockPrimes_78 : blockPrimes 78000000 79000000 = 54900 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 79: the number of
primes in [79000000, 80000000) is 54938, computed by sieve. MEDIUM -/
theorem blockPrimes_79 : blockPrimes 79000000 80000000 = 54938 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 80: the number of
primes in [80000000, 81000000) is 55027, computed by sieve. MEDIUM -/
theorem blockPrimes_80 : blockPrimes 80000000 81000000 = 55027 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 81: the number of
primes in [81000000, 82000000) is 55021, computed by sieve. MEDIUM -/
theorem blockPrimes_81 : blockPrimes 81000000 82000000 = 55021 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 82: the number of
primes in [82000000, 83000000) is 54887, computed by sieve. MEDIUM -/
theorem blockPrimes_82 : blockPrimes 82000000 83000000 = 54887 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 83: the number of
primes in [83000000, 84000000) is 54822, computed by sieve. MEDIUM -/
theorem blockPrimes_83 : blockPrimes 83000000 84000000 = 54822 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 84: the number of
primes in [84000000, 85000000) is 54592, computed by sieve. MEDIUM -/
theorem blockPrimes_84 : blockPrimes 84000000 85000000 = 54592 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 85: the number of
primes in [85000000, 86000000) is 54739, computed by sieve. MEDIUM -/
theorem blockPrimes_85 : blockPrimes 85000000 86000000 = 54739 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 86: the number of
primes in [86000000, 87000000) is 54710, computed by sieve. MEDIUM -/
theorem blockPrimes_86 : blockPrimes 86000000 87000000 = 54710 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 87: the number of
primes in [87000000, 88000000) is 54652, computed by sieve. MEDIUM -/
theorem blockPrimes_87 : blockPrimes 87000000 88000000 = 54652 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 88: the number of
primes in [88000000, 89000000) is 54733, computed by sieve. MEDIUM -/
theorem blockPrimes_88 : blockPrimes 88000000 89000000 = 54733 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 89: the number of
primes in [89000000, 90000000) is 54389, computed by sieve. MEDIUM -/
theorem blockPrimes_89 : blockPrimes 89000000 90000000 = 54389 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 90: the number of
primes in [90000000, 91000000) is 54705, computed by sieve. MEDIUM -/
theorem blockPrimes_90 : blockPrimes 90000000 91000000 = 54705 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 91: the number of
primes in [91000000, 92000000) is 54578, computed by sieve. MEDIUM -/
theorem blockPrimes_91 : blockPrimes 91000000 92000000 = 54578 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 92: the number of
primes in [92000000, 93000000) is 54444, computed by sieve. MEDIUM -/
theorem blockPrimes_92 : blockPrimes 92000000 93000000 = 54444 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 93: the number of
primes in [93000000, 94000000) is 54423, computed by sieve. MEDIUM -/
theorem blockPrimes_93 : blockPrimes 93000000 94000000 = 54423 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 94: the number of
primes in [94000000, 95000000) is 54645, computed by sieve. MEDIUM -/
theorem blockPrimes_94 : blockPrimes 94000000 95000000 = 54645 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 95: the number of
primes in [95000000, 96000000) is 54452, computed by sieve. MEDIUM -/
theorem blockPrimes_95 : blockPrimes 95000000 96000000 = 54452 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 96: the number of
primes in [96000000, 97000000) is 54364, computed by sieve. MEDIUM -/
theorem blockPrimes_96 : blockPrimes 96000000 97000000 = 54364 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 97: the number of
primes in [97000000, 98000000) is 54431, computed by sieve. MEDIUM -/
theorem blockPrimes_97 : blockPrimes 97000000 98000000 = 54431 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 98: the number of
primes in [98000000, 99000000) is 54127, computed by sieve. MEDIUM -/
theorem blockPrimes_98 : blockPrimes 98000000 99000000 = 54127 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, π 10⁸ = 5761455, block 99: the number of
primes in [99000000, 100000000) is 54332, computed by sieve. MEDIUM -/
theorem blockPrimes_99 : blockPrimes 99000000 100000000 = 54332 := by
  sorry

set_option maxRecDepth 100000 in
/-- PROVED from the 100 block LEAFs: `π 10⁸ = 5761455`. -/
theorem primeCount_1e8_S76 : primeCount (10 ^ 8) = 5761455 := by
  have hlast : blockPrimes 100000000 100000001 = 0 := by
    unfold blockPrimes; rw [filter_last]; rfl
  have hall : blockPrimes 0 100000000 + blockPrimes 100000000 100000001 =
      blockPrimes 0 100000001 := blockPrimes_add (by norm_num) (by norm_num)
  have s0 : blockPrimes 0 1000000 = 78498 := blockPrimes_0
  have s1 : blockPrimes 0 2000000 = 148933 := by
    have h : blockPrimes 0 1000000 + blockPrimes 1000000 2000000 = blockPrimes 0 2000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s0, blockPrimes_1]
  have s2 : blockPrimes 0 3000000 = 216816 := by
    have h : blockPrimes 0 2000000 + blockPrimes 2000000 3000000 = blockPrimes 0 3000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s1, blockPrimes_2]
  have s3 : blockPrimes 0 4000000 = 283146 := by
    have h : blockPrimes 0 3000000 + blockPrimes 3000000 4000000 = blockPrimes 0 4000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s2, blockPrimes_3]
  have s4 : blockPrimes 0 5000000 = 348513 := by
    have h : blockPrimes 0 4000000 + blockPrimes 4000000 5000000 = blockPrimes 0 5000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s3, blockPrimes_4]
  have s5 : blockPrimes 0 6000000 = 412849 := by
    have h : blockPrimes 0 5000000 + blockPrimes 5000000 6000000 = blockPrimes 0 6000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s4, blockPrimes_5]
  have s6 : blockPrimes 0 7000000 = 476648 := by
    have h : blockPrimes 0 6000000 + blockPrimes 6000000 7000000 = blockPrimes 0 7000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s5, blockPrimes_6]
  have s7 : blockPrimes 0 8000000 = 539777 := by
    have h : blockPrimes 0 7000000 + blockPrimes 7000000 8000000 = blockPrimes 0 8000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s6, blockPrimes_7]
  have s8 : blockPrimes 0 9000000 = 602489 := by
    have h : blockPrimes 0 8000000 + blockPrimes 8000000 9000000 = blockPrimes 0 9000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s7, blockPrimes_8]
  have s9 : blockPrimes 0 10000000 = 664579 := by
    have h : blockPrimes 0 9000000 + blockPrimes 9000000 10000000 = blockPrimes 0 10000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s8, blockPrimes_9]
  have s10 : blockPrimes 0 11000000 = 726517 := by
    have h : blockPrimes 0 10000000 + blockPrimes 10000000 11000000 = blockPrimes 0 11000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s9, blockPrimes_10]
  have s11 : blockPrimes 0 12000000 = 788060 := by
    have h : blockPrimes 0 11000000 + blockPrimes 11000000 12000000 = blockPrimes 0 12000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s10, blockPrimes_11]
  have s12 : blockPrimes 0 13000000 = 849252 := by
    have h : blockPrimes 0 12000000 + blockPrimes 12000000 13000000 = blockPrimes 0 13000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s11, blockPrimes_12]
  have s13 : blockPrimes 0 14000000 = 910077 := by
    have h : blockPrimes 0 13000000 + blockPrimes 13000000 14000000 = blockPrimes 0 14000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s12, blockPrimes_13]
  have s14 : blockPrimes 0 15000000 = 970704 := by
    have h : blockPrimes 0 14000000 + blockPrimes 14000000 15000000 = blockPrimes 0 15000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s13, blockPrimes_14]
  have s15 : blockPrimes 0 16000000 = 1031130 := by
    have h : blockPrimes 0 15000000 + blockPrimes 15000000 16000000 = blockPrimes 0 16000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s14, blockPrimes_15]
  have s16 : blockPrimes 0 17000000 = 1091314 := by
    have h : blockPrimes 0 16000000 + blockPrimes 16000000 17000000 = blockPrimes 0 17000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s15, blockPrimes_16]
  have s17 : blockPrimes 0 18000000 = 1151367 := by
    have h : blockPrimes 0 17000000 + blockPrimes 17000000 18000000 = blockPrimes 0 18000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s16, blockPrimes_17]
  have s18 : blockPrimes 0 19000000 = 1211050 := by
    have h : blockPrimes 0 18000000 + blockPrimes 18000000 19000000 = blockPrimes 0 19000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s17, blockPrimes_18]
  have s19 : blockPrimes 0 20000000 = 1270607 := by
    have h : blockPrimes 0 19000000 + blockPrimes 19000000 20000000 = blockPrimes 0 20000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s18, blockPrimes_19]
  have s20 : blockPrimes 0 21000000 = 1329943 := by
    have h : blockPrimes 0 20000000 + blockPrimes 20000000 21000000 = blockPrimes 0 21000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s19, blockPrimes_20]
  have s21 : blockPrimes 0 22000000 = 1389261 := by
    have h : blockPrimes 0 21000000 + blockPrimes 21000000 22000000 = blockPrimes 0 22000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s20, blockPrimes_21]
  have s22 : blockPrimes 0 23000000 = 1448221 := by
    have h : blockPrimes 0 22000000 + blockPrimes 22000000 23000000 = blockPrimes 0 23000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s21, blockPrimes_22]
  have s23 : blockPrimes 0 24000000 = 1507122 := by
    have h : blockPrimes 0 23000000 + blockPrimes 23000000 24000000 = blockPrimes 0 24000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s22, blockPrimes_23]
  have s24 : blockPrimes 0 25000000 = 1565927 := by
    have h : blockPrimes 0 24000000 + blockPrimes 24000000 25000000 = blockPrimes 0 25000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s23, blockPrimes_24]
  have s25 : blockPrimes 0 26000000 = 1624527 := by
    have h : blockPrimes 0 25000000 + blockPrimes 25000000 26000000 = blockPrimes 0 26000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s24, blockPrimes_25]
  have s26 : blockPrimes 0 27000000 = 1683065 := by
    have h : blockPrimes 0 26000000 + blockPrimes 26000000 27000000 = blockPrimes 0 27000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s25, blockPrimes_26]
  have s27 : blockPrimes 0 28000000 = 1741430 := by
    have h : blockPrimes 0 27000000 + blockPrimes 27000000 28000000 = blockPrimes 0 28000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s26, blockPrimes_27]
  have s28 : blockPrimes 0 29000000 = 1799676 := by
    have h : blockPrimes 0 28000000 + blockPrimes 28000000 29000000 = blockPrimes 0 29000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s27, blockPrimes_28]
  have s29 : blockPrimes 0 30000000 = 1857859 := by
    have h : blockPrimes 0 29000000 + blockPrimes 29000000 30000000 = blockPrimes 0 30000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s28, blockPrimes_29]
  have s30 : blockPrimes 0 31000000 = 1915979 := by
    have h : blockPrimes 0 30000000 + blockPrimes 30000000 31000000 = blockPrimes 0 31000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s29, blockPrimes_30]
  have s31 : blockPrimes 0 32000000 = 1973815 := by
    have h : blockPrimes 0 31000000 + blockPrimes 31000000 32000000 = blockPrimes 0 32000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s30, blockPrimes_31]
  have s32 : blockPrimes 0 33000000 = 2031667 := by
    have h : blockPrimes 0 32000000 + blockPrimes 32000000 33000000 = blockPrimes 0 33000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s31, blockPrimes_32]
  have s33 : blockPrimes 0 34000000 = 2089379 := by
    have h : blockPrimes 0 33000000 + blockPrimes 33000000 34000000 = blockPrimes 0 34000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s32, blockPrimes_33]
  have s34 : blockPrimes 0 35000000 = 2146775 := by
    have h : blockPrimes 0 34000000 + blockPrimes 34000000 35000000 = blockPrimes 0 35000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s33, blockPrimes_34]
  have s35 : blockPrimes 0 36000000 = 2204262 := by
    have h : blockPrimes 0 35000000 + blockPrimes 35000000 36000000 = blockPrimes 0 36000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s34, blockPrimes_35]
  have s36 : blockPrimes 0 37000000 = 2261623 := by
    have h : blockPrimes 0 36000000 + blockPrimes 36000000 37000000 = blockPrimes 0 37000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s35, blockPrimes_36]
  have s37 : blockPrimes 0 38000000 = 2318966 := by
    have h : blockPrimes 0 37000000 + blockPrimes 37000000 38000000 = blockPrimes 0 38000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s36, blockPrimes_37]
  have s38 : blockPrimes 0 39000000 = 2376402 := by
    have h : blockPrimes 0 38000000 + blockPrimes 38000000 39000000 = blockPrimes 0 39000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s37, blockPrimes_38]
  have s39 : blockPrimes 0 40000000 = 2433654 := by
    have h : blockPrimes 0 39000000 + blockPrimes 39000000 40000000 = blockPrimes 0 40000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s38, blockPrimes_39]
  have s40 : blockPrimes 0 41000000 = 2490756 := by
    have h : blockPrimes 0 40000000 + blockPrimes 40000000 41000000 = blockPrimes 0 41000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s39, blockPrimes_40]
  have s41 : blockPrimes 0 42000000 = 2547620 := by
    have h : blockPrimes 0 41000000 + blockPrimes 41000000 42000000 = blockPrimes 0 42000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s40, blockPrimes_41]
  have s42 : blockPrimes 0 43000000 = 2604535 := by
    have h : blockPrimes 0 42000000 + blockPrimes 42000000 43000000 = blockPrimes 0 43000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s41, blockPrimes_42]
  have s43 : blockPrimes 0 44000000 = 2661384 := by
    have h : blockPrimes 0 43000000 + blockPrimes 43000000 44000000 = blockPrimes 0 44000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s42, blockPrimes_43]
  have s44 : blockPrimes 0 45000000 = 2718160 := by
    have h : blockPrimes 0 44000000 + blockPrimes 44000000 45000000 = blockPrimes 0 45000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s43, blockPrimes_44]
  have s45 : blockPrimes 0 46000000 = 2775053 := by
    have h : blockPrimes 0 45000000 + blockPrimes 45000000 46000000 = blockPrimes 0 46000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s44, blockPrimes_45]
  have s46 : blockPrimes 0 47000000 = 2831693 := by
    have h : blockPrimes 0 46000000 + blockPrimes 46000000 47000000 = blockPrimes 0 47000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s45, blockPrimes_46]
  have s47 : blockPrimes 0 48000000 = 2888144 := by
    have h : blockPrimes 0 47000000 + blockPrimes 47000000 48000000 = blockPrimes 0 48000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s46, blockPrimes_47]
  have s48 : blockPrimes 0 49000000 = 2944531 := by
    have h : blockPrimes 0 48000000 + blockPrimes 48000000 49000000 = blockPrimes 0 49000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s47, blockPrimes_48]
  have s49 : blockPrimes 0 50000000 = 3001134 := by
    have h : blockPrimes 0 49000000 + blockPrimes 49000000 50000000 = blockPrimes 0 50000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s48, blockPrimes_49]
  have s50 : blockPrimes 0 51000000 = 3057494 := by
    have h : blockPrimes 0 50000000 + blockPrimes 50000000 51000000 = blockPrimes 0 51000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s49, blockPrimes_50]
  have s51 : blockPrimes 0 52000000 = 3113843 := by
    have h : blockPrimes 0 51000000 + blockPrimes 51000000 52000000 = blockPrimes 0 52000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s50, blockPrimes_51]
  have s52 : blockPrimes 0 53000000 = 3170052 := by
    have h : blockPrimes 0 52000000 + blockPrimes 52000000 53000000 = blockPrimes 0 53000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s51, blockPrimes_52]
  have s53 : blockPrimes 0 54000000 = 3226203 := by
    have h : blockPrimes 0 53000000 + blockPrimes 53000000 54000000 = blockPrimes 0 54000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s52, blockPrimes_53]
  have s54 : blockPrimes 0 55000000 = 3282200 := by
    have h : blockPrimes 0 54000000 + blockPrimes 54000000 55000000 = blockPrimes 0 55000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s53, blockPrimes_54]
  have s55 : blockPrimes 0 56000000 = 3338330 := by
    have h : blockPrimes 0 55000000 + blockPrimes 55000000 56000000 = blockPrimes 0 56000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s54, blockPrimes_55]
  have s56 : blockPrimes 0 57000000 = 3394435 := by
    have h : blockPrimes 0 56000000 + blockPrimes 56000000 57000000 = blockPrimes 0 57000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s55, blockPrimes_56]
  have s57 : blockPrimes 0 58000000 = 3450336 := by
    have h : blockPrimes 0 57000000 + blockPrimes 57000000 58000000 = blockPrimes 0 58000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s56, blockPrimes_57]
  have s58 : blockPrimes 0 59000000 = 3506314 := by
    have h : blockPrimes 0 58000000 + blockPrimes 58000000 59000000 = blockPrimes 0 59000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s57, blockPrimes_58]
  have s59 : blockPrimes 0 60000000 = 3562115 := by
    have h : blockPrimes 0 59000000 + blockPrimes 59000000 60000000 = blockPrimes 0 60000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s58, blockPrimes_59]
  have s60 : blockPrimes 0 61000000 = 3618045 := by
    have h : blockPrimes 0 60000000 + blockPrimes 60000000 61000000 = blockPrimes 0 61000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s59, blockPrimes_60]
  have s61 : blockPrimes 0 62000000 = 3673600 := by
    have h : blockPrimes 0 61000000 + blockPrimes 61000000 62000000 = blockPrimes 0 62000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s60, blockPrimes_61]
  have s62 : blockPrimes 0 63000000 = 3729306 := by
    have h : blockPrimes 0 62000000 + blockPrimes 62000000 63000000 = blockPrimes 0 63000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s61, blockPrimes_62]
  have s63 : blockPrimes 0 64000000 = 3785086 := by
    have h : blockPrimes 0 63000000 + blockPrimes 63000000 64000000 = blockPrimes 0 64000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s62, blockPrimes_63]
  have s64 : blockPrimes 0 65000000 = 3840554 := by
    have h : blockPrimes 0 64000000 + blockPrimes 64000000 65000000 = blockPrimes 0 65000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s63, blockPrimes_64]
  have s65 : blockPrimes 0 66000000 = 3896123 := by
    have h : blockPrimes 0 65000000 + blockPrimes 65000000 66000000 = blockPrimes 0 66000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s64, blockPrimes_65]
  have s66 : blockPrimes 0 67000000 = 3951767 := by
    have h : blockPrimes 0 66000000 + blockPrimes 66000000 67000000 = blockPrimes 0 67000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s65, blockPrimes_66]
  have s67 : blockPrimes 0 68000000 = 4007342 := by
    have h : blockPrimes 0 67000000 + blockPrimes 67000000 68000000 = blockPrimes 0 68000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s66, blockPrimes_67]
  have s68 : blockPrimes 0 69000000 = 4062674 := by
    have h : blockPrimes 0 68000000 + blockPrimes 68000000 69000000 = blockPrimes 0 69000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s67, blockPrimes_68]
  have s69 : blockPrimes 0 70000000 = 4118064 := by
    have h : blockPrimes 0 69000000 + blockPrimes 69000000 70000000 = blockPrimes 0 70000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s68, blockPrimes_69]
  have s70 : blockPrimes 0 71000000 = 4173373 := by
    have h : blockPrimes 0 70000000 + blockPrimes 70000000 71000000 = blockPrimes 0 71000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s69, blockPrimes_70]
  have s71 : blockPrimes 0 72000000 = 4228658 := by
    have h : blockPrimes 0 71000000 + blockPrimes 71000000 72000000 = blockPrimes 0 72000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s70, blockPrimes_71]
  have s72 : blockPrimes 0 73000000 = 4284089 := by
    have h : blockPrimes 0 72000000 + blockPrimes 72000000 73000000 = blockPrimes 0 73000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s71, blockPrimes_72]
  have s73 : blockPrimes 0 74000000 = 4339254 := by
    have h : blockPrimes 0 73000000 + blockPrimes 73000000 74000000 = blockPrimes 0 74000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s72, blockPrimes_73]
  have s74 : blockPrimes 0 75000000 = 4394304 := by
    have h : blockPrimes 0 74000000 + blockPrimes 74000000 75000000 = blockPrimes 0 75000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s73, blockPrimes_74]
  have s75 : blockPrimes 0 76000000 = 4449611 := by
    have h : blockPrimes 0 75000000 + blockPrimes 75000000 76000000 = blockPrimes 0 76000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s74, blockPrimes_75]
  have s76 : blockPrimes 0 77000000 = 4504535 := by
    have h : blockPrimes 0 76000000 + blockPrimes 76000000 77000000 = blockPrimes 0 77000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s75, blockPrimes_76]
  have s77 : blockPrimes 0 78000000 = 4559544 := by
    have h : blockPrimes 0 77000000 + blockPrimes 77000000 78000000 = blockPrimes 0 78000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s76, blockPrimes_77]
  have s78 : blockPrimes 0 79000000 = 4614444 := by
    have h : blockPrimes 0 78000000 + blockPrimes 78000000 79000000 = blockPrimes 0 79000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s77, blockPrimes_78]
  have s79 : blockPrimes 0 80000000 = 4669382 := by
    have h : blockPrimes 0 79000000 + blockPrimes 79000000 80000000 = blockPrimes 0 80000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s78, blockPrimes_79]
  have s80 : blockPrimes 0 81000000 = 4724409 := by
    have h : blockPrimes 0 80000000 + blockPrimes 80000000 81000000 = blockPrimes 0 81000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s79, blockPrimes_80]
  have s81 : blockPrimes 0 82000000 = 4779430 := by
    have h : blockPrimes 0 81000000 + blockPrimes 81000000 82000000 = blockPrimes 0 82000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s80, blockPrimes_81]
  have s82 : blockPrimes 0 83000000 = 4834317 := by
    have h : blockPrimes 0 82000000 + blockPrimes 82000000 83000000 = blockPrimes 0 83000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s81, blockPrimes_82]
  have s83 : blockPrimes 0 84000000 = 4889139 := by
    have h : blockPrimes 0 83000000 + blockPrimes 83000000 84000000 = blockPrimes 0 84000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s82, blockPrimes_83]
  have s84 : blockPrimes 0 85000000 = 4943731 := by
    have h : blockPrimes 0 84000000 + blockPrimes 84000000 85000000 = blockPrimes 0 85000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s83, blockPrimes_84]
  have s85 : blockPrimes 0 86000000 = 4998470 := by
    have h : blockPrimes 0 85000000 + blockPrimes 85000000 86000000 = blockPrimes 0 86000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s84, blockPrimes_85]
  have s86 : blockPrimes 0 87000000 = 5053180 := by
    have h : blockPrimes 0 86000000 + blockPrimes 86000000 87000000 = blockPrimes 0 87000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s85, blockPrimes_86]
  have s87 : blockPrimes 0 88000000 = 5107832 := by
    have h : blockPrimes 0 87000000 + blockPrimes 87000000 88000000 = blockPrimes 0 88000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s86, blockPrimes_87]
  have s88 : blockPrimes 0 89000000 = 5162565 := by
    have h : blockPrimes 0 88000000 + blockPrimes 88000000 89000000 = blockPrimes 0 89000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s87, blockPrimes_88]
  have s89 : blockPrimes 0 90000000 = 5216954 := by
    have h : blockPrimes 0 89000000 + blockPrimes 89000000 90000000 = blockPrimes 0 90000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s88, blockPrimes_89]
  have s90 : blockPrimes 0 91000000 = 5271659 := by
    have h : blockPrimes 0 90000000 + blockPrimes 90000000 91000000 = blockPrimes 0 91000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s89, blockPrimes_90]
  have s91 : blockPrimes 0 92000000 = 5326237 := by
    have h : blockPrimes 0 91000000 + blockPrimes 91000000 92000000 = blockPrimes 0 92000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s90, blockPrimes_91]
  have s92 : blockPrimes 0 93000000 = 5380681 := by
    have h : blockPrimes 0 92000000 + blockPrimes 92000000 93000000 = blockPrimes 0 93000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s91, blockPrimes_92]
  have s93 : blockPrimes 0 94000000 = 5435104 := by
    have h : blockPrimes 0 93000000 + blockPrimes 93000000 94000000 = blockPrimes 0 94000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s92, blockPrimes_93]
  have s94 : blockPrimes 0 95000000 = 5489749 := by
    have h : blockPrimes 0 94000000 + blockPrimes 94000000 95000000 = blockPrimes 0 95000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s93, blockPrimes_94]
  have s95 : blockPrimes 0 96000000 = 5544201 := by
    have h : blockPrimes 0 95000000 + blockPrimes 95000000 96000000 = blockPrimes 0 96000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s94, blockPrimes_95]
  have s96 : blockPrimes 0 97000000 = 5598565 := by
    have h : blockPrimes 0 96000000 + blockPrimes 96000000 97000000 = blockPrimes 0 97000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s95, blockPrimes_96]
  have s97 : blockPrimes 0 98000000 = 5652996 := by
    have h : blockPrimes 0 97000000 + blockPrimes 97000000 98000000 = blockPrimes 0 98000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s96, blockPrimes_97]
  have s98 : blockPrimes 0 99000000 = 5707123 := by
    have h : blockPrimes 0 98000000 + blockPrimes 98000000 99000000 = blockPrimes 0 99000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s97, blockPrimes_98]
  have s99 : blockPrimes 0 100000000 = 5761455 := by
    have h : blockPrimes 0 99000000 + blockPrimes 99000000 100000000 = blockPrimes 0 100000000 :=
      blockPrimes_add (by norm_num) (by norm_num)
    rw [← h, s98, blockPrimes_99]
  have htot : blockPrimes 0 100000001 = 5761455 := glue_last hall hlast s99.symm
  have e : primeCount (10 ^ 8) = ((blockPrimes 0 100000001 : ℕ) : ℝ) := by
    unfold primeCount blockPrimes
    rw [floor_1e8, card_filter, card_filter]
    refine congrArg (fun n : ℕ => (n : ℝ)) (Finset.sum_congr (by rw [range_eq_Ico]) ?_)
    intro i _
    split_ifs <;> rfl
  rw [e]
  exact_mod_cast htot

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 0: the sum
of log p over primes p in [0, 1000000) is 998484.1750256343 to ten places. MEDIUM -/
theorem thetaBlock_0 : (998484.175025 : ℝ) ≤ thetaBlock 0 1000000 ∧
    thetaBlock 0 1000000 ≤ 998484.175026 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 1: the sum
of log p over primes p in [1000000, 2000000) is 1000103.5471116545 to ten places. MEDIUM -/
theorem thetaBlock_1 : (1000103.547111 : ℝ) ≤ thetaBlock 1000000 2000000 ∧
    thetaBlock 1000000 2000000 ≤ 1000103.547112 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 2: the sum
of log p over primes p in [2000000, 3000000) is 999519.8083143822 to ten places. MEDIUM -/
theorem thetaBlock_2 : (999519.808314 : ℝ) ≤ thetaBlock 2000000 3000000 ∧
    thetaBlock 2000000 3000000 ≤ 999519.808315 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 3: the sum
of log p over primes p in [3000000, 4000000) is 999215.9616322073 to ten places. MEDIUM -/
theorem thetaBlock_3 : (999215.961632 : ℝ) ≤ thetaBlock 3000000 4000000 ∧
    thetaBlock 3000000 4000000 ≤ 999215.961633 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 4: the sum
of log p over primes p in [4000000, 5000000) is 1001247.5947166981 to ten places. MEDIUM -/
theorem thetaBlock_4 : (1001247.594716 : ℝ) ≤ thetaBlock 4000000 5000000 ∧
    thetaBlock 4000000 5000000 ≤ 1001247.594717 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 5: the sum
of log p over primes p in [5000000, 6000000) is 998412.7051978914 to ten places. MEDIUM -/
theorem thetaBlock_5 : (998412.705197 : ℝ) ≤ thetaBlock 5000000 6000000 ∧
    thetaBlock 5000000 6000000 ≤ 998412.705198 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 6: the sum
of log p over primes p in [6000000, 7000000) is 1000768.2065365707 to ten places. MEDIUM -/
theorem thetaBlock_6 : (1000768.206536 : ℝ) ≤ thetaBlock 6000000 7000000 ∧
    thetaBlock 6000000 7000000 ≤ 1000768.206537 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 7: the sum
of log p over primes p in [7000000, 8000000) is 999305.2477564705 to ten places. MEDIUM -/
theorem thetaBlock_7 : (999305.247756 : ℝ) ≤ thetaBlock 7000000 8000000 ∧
    thetaBlock 7000000 8000000 ≤ 999305.247757 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 8: the sum
of log p over primes p in [8000000, 9000000) is 1000568.3237739253 to ten places. MEDIUM -/
theorem thetaBlock_8 : (1000568.323773 : ℝ) ≤ thetaBlock 8000000 9000000 ∧
    thetaBlock 8000000 9000000 ≤ 1000568.323774 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 9: the sum
of log p over primes p in [9000000, 10000000) is 997553.7477908776 to ten places. MEDIUM -/
theorem thetaBlock_9 : (997553.74779 : ℝ) ≤ thetaBlock 9000000 10000000 ∧
    thetaBlock 9000000 10000000 ≤ 997553.747791 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 10: the sum
of log p over primes p in [10000000, 11000000) is 1001317.9226571966 to ten places. MEDIUM -/
theorem thetaBlock_10 : (1001317.922657 : ℝ) ≤ thetaBlock 10000000 11000000 ∧
    thetaBlock 10000000 11000000 ≤ 1001317.922658 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 11: the sum
of log p over primes p in [11000000, 12000000) is 1000536.5208256307 to ten places. MEDIUM -/
theorem thetaBlock_11 : (1000536.520825 : ℝ) ≤ thetaBlock 11000000 12000000 ∧
    thetaBlock 11000000 12000000 ≤ 1000536.520826 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 12: the sum
of log p over primes p in [12000000, 13000000) is 999934.1104398302 to ten places. MEDIUM -/
theorem thetaBlock_12 : (999934.110439 : ℝ) ≤ thetaBlock 12000000 13000000 ∧
    thetaBlock 12000000 13000000 ≤ 999934.110440 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 13: the sum
of log p over primes p in [13000000, 14000000) is 998623.4920801491 to ten places. MEDIUM -/
theorem thetaBlock_13 : (998623.49208 : ℝ) ≤ thetaBlock 13000000 14000000 ∧
    thetaBlock 13000000 14000000 ≤ 998623.492081 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 14: the sum
of log p over primes p in [14000000, 15000000) is 999703.4266492258 to ten places. MEDIUM -/
theorem thetaBlock_14 : (999703.426649 : ℝ) ≤ thetaBlock 14000000 15000000 ∧
    thetaBlock 14000000 15000000 ≤ 999703.426650 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 15: the sum
of log p over primes p in [15000000, 16000000) is 1000423.8493834756 to ten places. MEDIUM -/
theorem thetaBlock_15 : (1000423.849383 : ℝ) ≤ thetaBlock 15000000 16000000 ∧
    thetaBlock 15000000 16000000 ≤ 1000423.849384 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 16: the sum
of log p over primes p in [16000000, 17000000) is 1000183.2266342126 to ten places. MEDIUM -/
theorem thetaBlock_16 : (1000183.226634 : ℝ) ≤ thetaBlock 16000000 17000000 ∧
    thetaBlock 16000000 17000000 ≤ 1000183.226635 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 17: the sum
of log p over primes p in [17000000, 18000000) is 1001538.7211669477 to ten places. MEDIUM -/
theorem thetaBlock_17 : (1001538.721166 : ℝ) ≤ thetaBlock 17000000 18000000 ∧
    thetaBlock 17000000 18000000 ≤ 1001538.721167 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 18: the sum
of log p over primes p in [18000000, 19000000) is 998686.5149922697 to ten places. MEDIUM -/
theorem thetaBlock_18 : (998686.514992 : ℝ) ≤ thetaBlock 18000000 19000000 ∧
    thetaBlock 18000000 19000000 ≤ 998686.514993 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 19: the sum
of log p over primes p in [19000000, 20000000) is 999713.7794677012 to ten places. MEDIUM -/
theorem thetaBlock_19 : (999713.779467 : ℝ) ≤ thetaBlock 19000000 20000000 ∧
    thetaBlock 19000000 20000000 ≤ 999713.779468 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 20: the sum
of log p over primes p in [20000000, 21000000) is 998970.4931691671 to ten places. MEDIUM -/
theorem thetaBlock_20 : (998970.493169 : ℝ) ≤ thetaBlock 20000000 21000000 ∧
    thetaBlock 20000000 21000000 ≤ 998970.493170 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 21: the sum
of log p over primes p in [21000000, 22000000) is 1001494.4399860739 to ten places. MEDIUM -/
theorem thetaBlock_21 : (1001494.439986 : ℝ) ≤ thetaBlock 21000000 22000000 ∧
    thetaBlock 21000000 22000000 ≤ 1001494.439987 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 22: the sum
of log p over primes p in [22000000, 23000000) is 998132.0605352160 to ten places. MEDIUM -/
theorem thetaBlock_22 : (998132.060535 : ℝ) ≤ thetaBlock 22000000 23000000 ∧
    thetaBlock 22000000 23000000 ≤ 998132.060536 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 23: the sum
of log p over primes p in [23000000, 24000000) is 999692.1310789097 to ten places. MEDIUM -/
theorem thetaBlock_23 : (999692.131078 : ℝ) ≤ thetaBlock 23000000 24000000 ∧
    thetaBlock 23000000 24000000 ≤ 999692.131079 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 24: the sum
of log p over primes p in [24000000, 25000000) is 1000513.1410773732 to ten places. MEDIUM -/
theorem thetaBlock_24 : (1000513.141077 : ℝ) ≤ thetaBlock 24000000 25000000 ∧
    thetaBlock 24000000 25000000 ≤ 1000513.141078 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 25: the sum
of log p over primes p in [25000000, 26000000) is 999372.7869393146 to ten places. MEDIUM -/
theorem thetaBlock_25 : (999372.786939 : ℝ) ≤ thetaBlock 25000000 26000000 ∧
    thetaBlock 25000000 26000000 ≤ 999372.786940 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 26: the sum
of log p over primes p in [26000000, 27000000) is 1000566.7577925899 to ten places. MEDIUM -/
theorem thetaBlock_26 : (1000566.757792 : ℝ) ≤ thetaBlock 26000000 27000000 ∧
    thetaBlock 26000000 27000000 ≤ 1000566.757793 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 27: the sum
of log p over primes p in [27000000, 28000000) is 999771.2740179797 to ten places. MEDIUM -/
theorem thetaBlock_27 : (999771.274017 : ℝ) ≤ thetaBlock 27000000 28000000 ∧
    thetaBlock 27000000 28000000 ≤ 999771.274018 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 28: the sum
of log p over primes p in [28000000, 29000000) is 999812.5882427904 to ten places. MEDIUM -/
theorem thetaBlock_28 : (999812.588242 : ℝ) ≤ thetaBlock 28000000 29000000 ∧
    thetaBlock 28000000 29000000 ≤ 999812.588243 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 29: the sum
of log p over primes p in [29000000, 30000000) is 1000740.6851595751 to ten places. MEDIUM -/
theorem thetaBlock_29 : (1000740.685159 : ℝ) ≤ thetaBlock 29000000 30000000 ∧
    thetaBlock 29000000 30000000 ≤ 1000740.685160 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 30: the sum
of log p over primes p in [30000000, 31000000) is 1001591.4471108076 to ten places. MEDIUM -/
theorem thetaBlock_30 : (1001591.44711 : ℝ) ≤ thetaBlock 30000000 31000000 ∧
    thetaBlock 30000000 31000000 ≤ 1001591.447111 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 31: the sum
of log p over primes p in [31000000, 32000000) is 998566.0312590071 to ten places. MEDIUM -/
theorem thetaBlock_31 : (998566.031259 : ℝ) ≤ thetaBlock 31000000 32000000 ∧
    thetaBlock 31000000 32000000 ≤ 998566.031260 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 32: the sum
of log p over primes p in [32000000, 33000000) is 1000649.5817441864 to ten places. MEDIUM -/
theorem thetaBlock_32 : (1000649.581744 : ℝ) ≤ thetaBlock 32000000 33000000 ∧
    thetaBlock 32000000 33000000 ≤ 1000649.581745 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 33: the sum
of log p over primes p in [33000000, 34000000) is 999976.3598494799 to ten places. MEDIUM -/
theorem thetaBlock_33 : (999976.359849 : ℝ) ≤ thetaBlock 33000000 34000000 ∧
    thetaBlock 33000000 34000000 ≤ 999976.359850 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 34: the sum
of log p over primes p in [34000000, 35000000) is 996191.5494695490 to ten places. MEDIUM -/
theorem thetaBlock_34 : (996191.549469 : ℝ) ≤ thetaBlock 34000000 35000000 ∧
    thetaBlock 34000000 35000000 ≤ 996191.549470 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 35: the sum
of log p over primes p in [35000000, 36000000) is 999412.1345463400 to ten places. MEDIUM -/
theorem thetaBlock_35 : (999412.134546 : ℝ) ≤ thetaBlock 35000000 36000000 ∧
    thetaBlock 35000000 36000000 ≤ 999412.134547 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 36: the sum
of log p over primes p in [36000000, 37000000) is 998813.8823735330 to ten places. MEDIUM -/
theorem thetaBlock_36 : (998813.882373 : ℝ) ≤ thetaBlock 36000000 37000000 ∧
    thetaBlock 36000000 37000000 ≤ 998813.882374 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 37: the sum
of log p over primes p in [37000000, 38000000) is 1000050.1432096160 to ten places. MEDIUM -/
theorem thetaBlock_37 : (1000050.143209 : ℝ) ≤ thetaBlock 37000000 38000000 ∧
    thetaBlock 37000000 38000000 ≤ 1000050.143210 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 38: the sum
of log p over primes p in [38000000, 39000000) is 1003184.3707555212 to ten places. MEDIUM -/
theorem thetaBlock_38 : (1003184.370755 : ℝ) ≤ thetaBlock 38000000 39000000 ∧
    thetaBlock 38000000 39000000 ≤ 1003184.370756 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 39: the sum
of log p over primes p in [39000000, 40000000) is 1001438.2737178375 to ten places. MEDIUM -/
theorem thetaBlock_39 : (1001438.273717 : ℝ) ≤ thetaBlock 39000000 40000000 ∧
    thetaBlock 39000000 40000000 ≤ 1001438.273718 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 40: the sum
of log p over primes p in [40000000, 41000000) is 1000243.0866651839 to ten places. MEDIUM -/
theorem thetaBlock_40 : (1000243.086665 : ℝ) ≤ thetaBlock 40000000 41000000 ∧
    thetaBlock 40000000 41000000 ≤ 1000243.086666 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 41: the sum
of log p over primes p in [41000000, 42000000) is 997460.7596723534 to ten places. MEDIUM -/
theorem thetaBlock_41 : (997460.759672 : ℝ) ≤ thetaBlock 41000000 42000000 ∧
    thetaBlock 41000000 42000000 ≤ 997460.759673 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 42: the sum
of log p over primes p in [42000000, 43000000) is 999710.0536499260 to ten places. MEDIUM -/
theorem thetaBlock_42 : (999710.053649 : ℝ) ≤ thetaBlock 42000000 43000000 ∧
    thetaBlock 42000000 43000000 ≤ 999710.053650 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 43: the sum
of log p over primes p in [43000000, 44000000) is 999874.4654441304 to ten places. MEDIUM -/
theorem thetaBlock_43 : (999874.465444 : ℝ) ≤ thetaBlock 43000000 44000000 ∧
    thetaBlock 43000000 44000000 ≤ 999874.465445 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 44: the sum
of log p over primes p in [44000000, 45000000) is 999881.0867996115 to ten places. MEDIUM -/
theorem thetaBlock_44 : (999881.086799 : ℝ) ≤ thetaBlock 44000000 45000000 ∧
    thetaBlock 44000000 45000000 ≤ 999881.086800 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 45: the sum
of log p over primes p in [45000000, 46000000) is 1003204.8478867699 to ten places. MEDIUM -/
theorem thetaBlock_45 : (1003204.847886 : ℝ) ≤ thetaBlock 45000000 46000000 ∧
    thetaBlock 45000000 46000000 ≤ 1003204.847887 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 46: the sum
of log p over primes p in [46000000, 47000000) is 999976.5196550004 to ten places. MEDIUM -/
theorem thetaBlock_46 : (999976.519655 : ℝ) ≤ thetaBlock 46000000 47000000 ∧
    thetaBlock 46000000 47000000 ≤ 999976.519656 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 47: the sum
of log p over primes p in [47000000, 48000000) is 997840.2599369369 to ten places. MEDIUM -/
theorem thetaBlock_47 : (997840.259936 : ℝ) ≤ thetaBlock 47000000 48000000 ∧
    thetaBlock 47000000 48000000 ≤ 997840.259937 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 48: the sum
of log p over primes p in [48000000, 49000000) is 997884.1090161343 to ten places. MEDIUM -/
theorem thetaBlock_48 : (997884.109016 : ℝ) ≤ thetaBlock 48000000 49000000 ∧
    thetaBlock 48000000 49000000 ≤ 997884.109017 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 49: the sum
of log p over primes p in [49000000, 50000000) is 1002861.6588058724 to ten places. MEDIUM -/
theorem thetaBlock_49 : (1002861.658805 : ℝ) ≤ thetaBlock 49000000 50000000 ∧
    thetaBlock 49000000 50000000 ≤ 1002861.658806 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 50: the sum
of log p over primes p in [50000000, 51000000) is 999683.8153583489 to ten places. MEDIUM -/
theorem thetaBlock_50 : (999683.815358 : ℝ) ≤ thetaBlock 50000000 51000000 ∧
    thetaBlock 50000000 51000000 ≤ 999683.815359 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 51: the sum
of log p over primes p in [51000000, 52000000) is 1000594.0746704464 to ten places. MEDIUM -/
theorem thetaBlock_51 : (1000594.07467 : ℝ) ≤ thetaBlock 51000000 52000000 ∧
    thetaBlock 51000000 52000000 ≤ 1000594.074671 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 52: the sum
of log p over primes p in [52000000, 53000000) is 999188.7479076886 to ten places. MEDIUM -/
theorem thetaBlock_52 : (999188.747907 : ℝ) ≤ thetaBlock 52000000 53000000 ∧
    thetaBlock 52000000 53000000 ≤ 999188.747908 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 53: the sum
of log p over primes p in [53000000, 54000000) is 999216.9976231337 to ten places. MEDIUM -/
theorem thetaBlock_53 : (999216.997623 : ℝ) ≤ thetaBlock 53000000 54000000 ∧
    thetaBlock 53000000 54000000 ≤ 999216.997624 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 54: the sum
of log p over primes p in [54000000, 55000000) is 997513.9150744383 to ten places. MEDIUM -/
theorem thetaBlock_54 : (997513.915074 : ℝ) ≤ thetaBlock 54000000 55000000 ∧
    thetaBlock 54000000 55000000 ≤ 997513.915075 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 55: the sum
of log p over primes p in [55000000, 56000000) is 1000903.2991617160 to ten places. MEDIUM -/
theorem thetaBlock_55 : (1000903.299161 : ℝ) ≤ thetaBlock 55000000 56000000 ∧
    thetaBlock 55000000 56000000 ≤ 1000903.299162 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 56: the sum
of log p over primes p in [56000000, 57000000) is 1001459.3258477646 to ten places. MEDIUM -/
theorem thetaBlock_56 : (1001459.325847 : ℝ) ≤ thetaBlock 56000000 57000000 ∧
    thetaBlock 56000000 57000000 ≤ 1001459.325848 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 57: the sum
of log p over primes p in [57000000, 58000000) is 998797.9739412555 to ten places. MEDIUM -/
theorem thetaBlock_57 : (998797.973941 : ℝ) ≤ thetaBlock 57000000 58000000 ∧
    thetaBlock 57000000 58000000 ≤ 998797.973942 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 58: the sum
of log p over primes p in [58000000, 59000000) is 1001139.5984437956 to ten places. MEDIUM -/
theorem thetaBlock_58 : (1001139.598443 : ℝ) ≤ thetaBlock 58000000 59000000 ∧
    thetaBlock 58000000 59000000 ≤ 1001139.598444 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 59: the sum
of log p over primes p in [59000000, 60000000) is 998920.5244259466 to ten places. MEDIUM -/
theorem thetaBlock_59 : (998920.524425 : ℝ) ≤ thetaBlock 59000000 60000000 ∧
    thetaBlock 59000000 60000000 ≤ 998920.524426 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 60: the sum
of log p over primes p in [60000000, 61000000) is 1002162.3421422760 to ten places. MEDIUM -/
theorem thetaBlock_60 : (1002162.342142 : ℝ) ≤ thetaBlock 60000000 61000000 ∧
    thetaBlock 60000000 61000000 ≤ 1002162.342143 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 61: the sum
of log p over primes p in [61000000, 62000000) is 996353.8960123640 to ten places. MEDIUM -/
theorem thetaBlock_61 : (996353.896012 : ℝ) ≤ thetaBlock 61000000 62000000 ∧
    thetaBlock 61000000 62000000 ≤ 996353.896013 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 62: the sum
of log p over primes p in [62000000, 63000000) is 999959.4741933208 to ten places. MEDIUM -/
theorem thetaBlock_62 : (999959.474193 : ℝ) ≤ thetaBlock 62000000 63000000 ∧
    thetaBlock 62000000 63000000 ≤ 999959.474194 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 63: the sum
of log p over primes p in [63000000, 64000000) is 1002174.0289879606 to ten places. MEDIUM -/
theorem thetaBlock_63 : (1002174.028987 : ℝ) ≤ thetaBlock 63000000 64000000 ∧
    thetaBlock 63000000 64000000 ≤ 1002174.028988 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 64: the sum
of log p over primes p in [64000000, 65000000) is 997434.4441155430 to ten places. MEDIUM -/
theorem thetaBlock_64 : (997434.444115 : ℝ) ≤ thetaBlock 64000000 65000000 ∧
    thetaBlock 64000000 65000000 ≤ 997434.444116 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 65: the sum
of log p over primes p in [65000000, 66000000) is 1000106.2140201709 to ten places. MEDIUM -/
theorem thetaBlock_65 : (1000106.21402 : ℝ) ≤ thetaBlock 65000000 66000000 ∧
    thetaBlock 65000000 66000000 ≤ 1000106.214021 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 66: the sum
of log p over primes p in [66000000, 67000000) is 1002298.1033095358 to ten places. MEDIUM -/
theorem thetaBlock_66 : (1002298.103309 : ℝ) ≤ thetaBlock 66000000 67000000 ∧
    thetaBlock 66000000 67000000 ≤ 1002298.103310 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 67: the sum
of log p over primes p in [67000000, 68000000) is 1001885.5219314111 to ten places. MEDIUM -/
theorem thetaBlock_67 : (1001885.521931 : ℝ) ≤ thetaBlock 67000000 68000000 ∧
    thetaBlock 67000000 68000000 ≤ 1001885.521932 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 68: the sum
of log p over primes p in [68000000, 69000000) is 998318.5954157563 to ten places. MEDIUM -/
theorem thetaBlock_68 : (998318.595415 : ℝ) ≤ thetaBlock 68000000 69000000 ∧
    thetaBlock 68000000 69000000 ≤ 998318.595416 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 69: the sum
of log p over primes p in [69000000, 70000000) is 1000167.5946775121 to ten places. MEDIUM -/
theorem thetaBlock_69 : (1000167.594677 : ℝ) ≤ thetaBlock 69000000 70000000 ∧
    thetaBlock 69000000 70000000 ≤ 1000167.594678 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 70: the sum
of log p over primes p in [70000000, 71000000) is 999494.8812099165 to ten places. MEDIUM -/
theorem thetaBlock_70 : (999494.881209 : ℝ) ≤ thetaBlock 70000000 71000000 ∧
    thetaBlock 70000000 71000000 ≤ 999494.881210 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 71: the sum
of log p over primes p in [71000000, 72000000) is 999839.7518547045 to ten places. MEDIUM -/
theorem thetaBlock_71 : (999839.751854 : ℝ) ≤ thetaBlock 71000000 72000000 ∧
    thetaBlock 71000000 72000000 ≤ 999839.751855 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 72: the sum
of log p over primes p in [72000000, 73000000) is 1003250.1550543783 to ten places. MEDIUM -/
theorem thetaBlock_72 : (1003250.155054 : ℝ) ≤ thetaBlock 72000000 73000000 ∧
    thetaBlock 72000000 73000000 ≤ 1003250.155055 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 73: the sum
of log p over primes p in [73000000, 74000000) is 999192.3710611035 to ten places. MEDIUM -/
theorem thetaBlock_73 : (999192.371061 : ℝ) ≤ thetaBlock 73000000 74000000 ∧
    thetaBlock 73000000 74000000 ≤ 999192.371062 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 74: the sum
of log p over primes p in [74000000, 75000000) is 997853.5236496970 to ten places. MEDIUM -/
theorem thetaBlock_74 : (997853.523649 : ℝ) ≤ thetaBlock 74000000 75000000 ∧
    thetaBlock 74000000 75000000 ≤ 997853.523650 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 75: the sum
of log p over primes p in [75000000, 76000000) is 1003249.1085991833 to ten places. MEDIUM -/
theorem thetaBlock_75 : (1003249.108599 : ℝ) ≤ thetaBlock 75000000 76000000 ∧
    thetaBlock 75000000 76000000 ≤ 1003249.108600 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 76: the sum
of log p over primes p in [76000000, 77000000) is 997024.4597583873 to ten places. MEDIUM -/
theorem thetaBlock_76 : (997024.459758 : ℝ) ≤ thetaBlock 76000000 77000000 ∧
    thetaBlock 76000000 77000000 ≤ 997024.459759 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 77: the sum
of log p over primes p in [77000000, 78000000) is 999281.3665147131 to ten places. MEDIUM -/
theorem thetaBlock_77 : (999281.366514 : ℝ) ≤ thetaBlock 77000000 78000000 ∧
    thetaBlock 77000000 78000000 ≤ 999281.366515 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 78: the sum
of log p over primes p in [78000000, 79000000) is 998005.1564512302 to ten places. MEDIUM -/
theorem thetaBlock_78 : (998005.156451 : ℝ) ≤ thetaBlock 78000000 79000000 ∧
    thetaBlock 78000000 79000000 ≤ 998005.156452 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 79: the sum
of log p over primes p in [79000000, 80000000) is 999391.0743273432 to ten places. MEDIUM -/
theorem thetaBlock_79 : (999391.074327 : ℝ) ≤ thetaBlock 79000000 80000000 ∧
    thetaBlock 79000000 80000000 ≤ 999391.074328 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 80: the sum
of log p over primes p in [80000000, 81000000) is 1001698.6988344647 to ten places. MEDIUM -/
theorem thetaBlock_80 : (1001698.698834 : ℝ) ≤ thetaBlock 80000000 81000000 ∧
    thetaBlock 80000000 81000000 ≤ 1001698.698835 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 81: the sum
of log p over primes p in [81000000, 82000000) is 1002267.8757284292 to ten places. MEDIUM -/
theorem thetaBlock_81 : (1002267.875728 : ℝ) ≤ thetaBlock 81000000 82000000 ∧
    thetaBlock 81000000 82000000 ≤ 1002267.875729 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 82: the sum
of log p over primes p in [82000000, 83000000) is 1000497.3566065721 to ten places. MEDIUM -/
theorem thetaBlock_82 : (1000497.356606 : ℝ) ≤ thetaBlock 82000000 83000000 ∧
    thetaBlock 82000000 83000000 ≤ 1000497.356607 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 83: the sum
of log p over primes p in [83000000, 84000000) is 999973.6902130720 to ten places. MEDIUM -/
theorem thetaBlock_83 : (999973.690213 : ℝ) ≤ thetaBlock 83000000 84000000 ∧
    thetaBlock 83000000 84000000 ≤ 999973.690214 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 84: the sum
of log p over primes p in [84000000, 85000000) is 996427.5554332209 to ten places. MEDIUM -/
theorem thetaBlock_84 : (996427.555433 : ℝ) ≤ thetaBlock 84000000 85000000 ∧
    thetaBlock 84000000 85000000 ≤ 996427.555434 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 85: the sum
of log p over primes p in [85000000, 86000000) is 999754.4216825970 to ten places. MEDIUM -/
theorem thetaBlock_85 : (999754.421682 : ℝ) ≤ thetaBlock 85000000 86000000 ∧
    thetaBlock 85000000 86000000 ≤ 999754.421683 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 86: the sum
of log p over primes p in [86000000, 87000000) is 999860.6363604067 to ten places. MEDIUM -/
theorem thetaBlock_86 : (999860.63636 : ℝ) ≤ thetaBlock 86000000 87000000 ∧
    thetaBlock 86000000 87000000 ≤ 999860.636361 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 87: the sum
of log p over primes p in [87000000, 88000000) is 999429.0647713324 to ten places. MEDIUM -/
theorem thetaBlock_87 : (999429.064771 : ℝ) ≤ thetaBlock 87000000 88000000 ∧
    thetaBlock 87000000 88000000 ≤ 999429.064772 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 88: the sum
of log p over primes p in [88000000, 89000000) is 1001532.1318132852 to ten places. MEDIUM -/
theorem thetaBlock_88 : (1001532.131813 : ℝ) ≤ thetaBlock 88000000 89000000 ∧
    thetaBlock 88000000 89000000 ≤ 1001532.131814 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 89: the sum
of log p over primes p in [89000000, 90000000) is 995848.3116772657 to ten places. MEDIUM -/
theorem thetaBlock_89 : (995848.311677 : ℝ) ≤ thetaBlock 89000000 90000000 ∧
    thetaBlock 89000000 90000000 ≤ 995848.311678 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 90: the sum
of log p over primes p in [90000000, 91000000) is 1002241.8410319417 to ten places. MEDIUM -/
theorem thetaBlock_90 : (1002241.841031 : ℝ) ≤ thetaBlock 90000000 91000000 ∧
    thetaBlock 90000000 91000000 ≤ 1002241.841032 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 91: the sum
of log p over primes p in [91000000, 92000000) is 1000515.1800977151 to ten places. MEDIUM -/
theorem thetaBlock_91 : (1000515.180097 : ℝ) ≤ thetaBlock 91000000 92000000 ∧
    thetaBlock 91000000 92000000 ≤ 1000515.180098 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 92: the sum
of log p over primes p in [92000000, 93000000) is 998650.5876426485 to ten places. MEDIUM -/
theorem thetaBlock_92 : (998650.587642 : ℝ) ≤ thetaBlock 92000000 93000000 ∧
    thetaBlock 92000000 93000000 ≤ 998650.587643 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 93: the sum
of log p over primes p in [93000000, 94000000) is 998850.7648799694 to ten places. MEDIUM -/
theorem thetaBlock_93 : (998850.764879 : ℝ) ≤ thetaBlock 93000000 94000000 ∧
    thetaBlock 93000000 94000000 ≤ 998850.764880 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 94: the sum
of log p over primes p in [94000000, 95000000) is 1003506.8547716066 to ten places. MEDIUM -/
theorem thetaBlock_94 : (1003506.854771 : ℝ) ≤ thetaBlock 94000000 95000000 ∧
    thetaBlock 94000000 95000000 ≤ 1003506.854772 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 95: the sum
of log p over primes p in [95000000, 96000000) is 1000535.8453449993 to ten places. MEDIUM -/
theorem thetaBlock_95 : (1000535.845344 : ℝ) ≤ thetaBlock 95000000 96000000 ∧
    thetaBlock 95000000 96000000 ≤ 1000535.845345 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 96: the sum
of log p over primes p in [96000000, 97000000) is 999485.3768047778 to ten places. MEDIUM -/
theorem thetaBlock_96 : (999485.376804 : ℝ) ≤ thetaBlock 96000000 97000000 ∧
    thetaBlock 96000000 97000000 ≤ 999485.376805 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 97: the sum
of log p over primes p in [97000000, 98000000) is 1001278.1122462954 to ten places. MEDIUM -/
theorem thetaBlock_97 : (1001278.112246 : ℝ) ≤ thetaBlock 97000000 98000000 ∧
    thetaBlock 97000000 98000000 ≤ 1001278.112247 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 98: the sum
of log p over primes p in [98000000, 99000000) is 996237.6052237299 to ten places. MEDIUM -/
theorem thetaBlock_98 : (996237.605223 : ℝ) ≤ thetaBlock 98000000 99000000 ∧
    thetaBlock 98000000 99000000 ≤ 996237.605224 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, θ 10⁸ = 99987730.0180, block 99: the sum
of log p over primes p in [99000000, 100000000) is 1000559.9093968951 to ten places. MEDIUM -/
theorem thetaBlock_99 : (1000559.909396 : ℝ) ≤ thetaBlock 99000000 100000000 ∧
    thetaBlock 99000000 100000000 ≤ 1000559.909397 := by
  sorry

set_option maxRecDepth 100000 in
/-- PROVED from the 100 block LEAFs: `99987730.01 ≤ θ 10⁸ ≤ 99987730.03`. -/
theorem theta_1e8_S76 : 99987730.01 ≤ Chebyshev.theta (10 ^ 8) ∧
    Chebyshev.theta (10 ^ 8) ≤ 99987730.03 := by
  have hsum := thetaBlock_sum 1000000 100
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceMul, Nat.reduceAdd] at hsum
  have hlast : thetaBlock 100000000 100000001 = 0 := by
    unfold thetaBlock; rw [filter_last]; rfl
  have hall : thetaBlock 0 100000000 + thetaBlock 100000000 100000001 =
      thetaBlock 0 100000001 := thetaBlock_add (by norm_num) (by norm_num)
  rw [hlast, add_zero] at hall
  have heq : Chebyshev.theta (10 ^ 8) = thetaBlock 0 100000001 := by
    rw [Chebyshev.theta_eq_sum_Icc, floor_1e8]
    unfold thetaBlock
    congr 1
  rw [heq, ← hall, ← hsum]
  have L := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (thetaBlock_0.1) thetaBlock_1.1) thetaBlock_2.1) thetaBlock_3.1) thetaBlock_4.1) thetaBlock_5.1) thetaBlock_6.1) thetaBlock_7.1) thetaBlock_8.1) thetaBlock_9.1) thetaBlock_10.1) thetaBlock_11.1) thetaBlock_12.1) thetaBlock_13.1) thetaBlock_14.1) thetaBlock_15.1) thetaBlock_16.1) thetaBlock_17.1) thetaBlock_18.1) thetaBlock_19.1) thetaBlock_20.1) thetaBlock_21.1) thetaBlock_22.1) thetaBlock_23.1) thetaBlock_24.1) thetaBlock_25.1) thetaBlock_26.1) thetaBlock_27.1) thetaBlock_28.1) thetaBlock_29.1) thetaBlock_30.1) thetaBlock_31.1) thetaBlock_32.1) thetaBlock_33.1) thetaBlock_34.1) thetaBlock_35.1) thetaBlock_36.1) thetaBlock_37.1) thetaBlock_38.1) thetaBlock_39.1) thetaBlock_40.1) thetaBlock_41.1) thetaBlock_42.1) thetaBlock_43.1) thetaBlock_44.1) thetaBlock_45.1) thetaBlock_46.1) thetaBlock_47.1) thetaBlock_48.1) thetaBlock_49.1) thetaBlock_50.1) thetaBlock_51.1) thetaBlock_52.1) thetaBlock_53.1) thetaBlock_54.1) thetaBlock_55.1) thetaBlock_56.1) thetaBlock_57.1) thetaBlock_58.1) thetaBlock_59.1) thetaBlock_60.1) thetaBlock_61.1) thetaBlock_62.1) thetaBlock_63.1) thetaBlock_64.1) thetaBlock_65.1) thetaBlock_66.1) thetaBlock_67.1) thetaBlock_68.1) thetaBlock_69.1) thetaBlock_70.1) thetaBlock_71.1) thetaBlock_72.1) thetaBlock_73.1) thetaBlock_74.1) thetaBlock_75.1) thetaBlock_76.1) thetaBlock_77.1) thetaBlock_78.1) thetaBlock_79.1) thetaBlock_80.1) thetaBlock_81.1) thetaBlock_82.1) thetaBlock_83.1) thetaBlock_84.1) thetaBlock_85.1) thetaBlock_86.1) thetaBlock_87.1) thetaBlock_88.1) thetaBlock_89.1) thetaBlock_90.1) thetaBlock_91.1) thetaBlock_92.1) thetaBlock_93.1) thetaBlock_94.1) thetaBlock_95.1) thetaBlock_96.1) thetaBlock_97.1) thetaBlock_98.1) thetaBlock_99.1
  have U := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (thetaBlock_0.2) thetaBlock_1.2) thetaBlock_2.2) thetaBlock_3.2) thetaBlock_4.2) thetaBlock_5.2) thetaBlock_6.2) thetaBlock_7.2) thetaBlock_8.2) thetaBlock_9.2) thetaBlock_10.2) thetaBlock_11.2) thetaBlock_12.2) thetaBlock_13.2) thetaBlock_14.2) thetaBlock_15.2) thetaBlock_16.2) thetaBlock_17.2) thetaBlock_18.2) thetaBlock_19.2) thetaBlock_20.2) thetaBlock_21.2) thetaBlock_22.2) thetaBlock_23.2) thetaBlock_24.2) thetaBlock_25.2) thetaBlock_26.2) thetaBlock_27.2) thetaBlock_28.2) thetaBlock_29.2) thetaBlock_30.2) thetaBlock_31.2) thetaBlock_32.2) thetaBlock_33.2) thetaBlock_34.2) thetaBlock_35.2) thetaBlock_36.2) thetaBlock_37.2) thetaBlock_38.2) thetaBlock_39.2) thetaBlock_40.2) thetaBlock_41.2) thetaBlock_42.2) thetaBlock_43.2) thetaBlock_44.2) thetaBlock_45.2) thetaBlock_46.2) thetaBlock_47.2) thetaBlock_48.2) thetaBlock_49.2) thetaBlock_50.2) thetaBlock_51.2) thetaBlock_52.2) thetaBlock_53.2) thetaBlock_54.2) thetaBlock_55.2) thetaBlock_56.2) thetaBlock_57.2) thetaBlock_58.2) thetaBlock_59.2) thetaBlock_60.2) thetaBlock_61.2) thetaBlock_62.2) thetaBlock_63.2) thetaBlock_64.2) thetaBlock_65.2) thetaBlock_66.2) thetaBlock_67.2) thetaBlock_68.2) thetaBlock_69.2) thetaBlock_70.2) thetaBlock_71.2) thetaBlock_72.2) thetaBlock_73.2) thetaBlock_74.2) thetaBlock_75.2) thetaBlock_76.2) thetaBlock_77.2) thetaBlock_78.2) thetaBlock_79.2) thetaBlock_80.2) thetaBlock_81.2) thetaBlock_82.2) thetaBlock_83.2) thetaBlock_84.2) thetaBlock_85.2) thetaBlock_86.2) thetaBlock_87.2) thetaBlock_88.2) thetaBlock_89.2) thetaBlock_90.2) thetaBlock_91.2) thetaBlock_92.2) thetaBlock_93.2) thetaBlock_94.2) thetaBlock_95.2) thetaBlock_96.2) thetaBlock_97.2) thetaBlock_98.2) thetaBlock_99.2
  constructor
  · refine le_trans ?_ L; norm_num
  · refine le_trans U ?_; norm_num

/-- LEAF: Schoenfeld 1976 p. 340 line 1, li 10⁸ = 5762209.3754, the start value
li 2 = 1.045163780117 to twelve places, li the principal value of [10]. MEDIUM -/
theorem liPV_two_encl : (1.045163 : ℝ) ≤ liPV 2 ∧ liPV 2 ≤ 1.045164 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, li 10⁸ = 5762209.3754, the piece
∫ dt / log t over [2, 10], value 5.120435724670 to twelve places. MEDIUM -/
theorem liPiece_0 : (5.120435 : ℝ) ≤ ∫ t in (2 : ℝ)..10, 1 / log t ∧
    ∫ t in (2 : ℝ)..10, 1 / log t ≤ 5.120436 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, li 10⁸ = 5762209.3754, the piece
∫ dt / log t over [10, 100], value 23.960542079292 to twelve places. MEDIUM -/
theorem liPiece_1 : (23.960542 : ℝ) ≤ ∫ t in (10 : ℝ)..100, 1 / log t ∧
    ∫ t in (10 : ℝ)..100, 1 / log t ≤ 23.960543 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, li 10⁸ = 5762209.3754, the piece
∫ dt / log t over [100, 1000], value 147.483516406073 to twelve places. MEDIUM -/
theorem liPiece_2 : (147.483516 : ℝ) ≤ ∫ t in (100 : ℝ)..1000, 1 / log t ∧
    ∫ t in (100 : ℝ)..1000, 1 / log t ≤ 147.483517 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, li 10⁸ = 5762209.3754, the piece
∫ dt / log t over [1000, 10000], value 1068.527557909236 to twelve places. MEDIUM -/
theorem liPiece_3 : (1068.527557 : ℝ) ≤ ∫ t in (1000 : ℝ)..10000, 1 / log t ∧
    ∫ t in (1000 : ℝ)..10000, 1 / log t ≤ 1068.527558 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, li 10⁸ = 5762209.3754, the piece
∫ dt / log t over [10000, 100000], value 8383.671785151410 to twelve places. MEDIUM -/
theorem liPiece_4 : (8383.671785 : ℝ) ≤ ∫ t in (10000 : ℝ)..100000, 1 / log t ∧
    ∫ t in (10000 : ℝ)..100000, 1 / log t ≤ 8383.671786 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, li 10⁸ = 5762209.3754, the piece
∫ dt / log t over [100000, 1000000], value 68997.740158411384 to twelve places. MEDIUM -/
theorem liPiece_5 : (68997.740158 : ℝ) ≤ ∫ t in (100000 : ℝ)..1000000, 1 / log t ∧
    ∫ t in (100000 : ℝ)..1000000, 1 / log t ≤ 68997.740159 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, li 10⁸ = 5762209.3754, the piece
∫ dt / log t over [1000000, 10000000], value 586290.855889106730 to twelve places. MEDIUM -/
theorem liPiece_6 : (586290.855889 : ℝ) ≤ ∫ t in (1000000 : ℝ)..10000000, 1 / log t ∧
    ∫ t in (1000000 : ℝ)..10000000, 1 / log t ≤ 586290.855890 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340 line 1, li 10⁸ = 5762209.3754, the piece
∫ dt / log t over [10000000, 100000000], value 5097290.970399462555 to twelve places. MEDIUM -/
theorem liPiece_7 : (5097290.970399 : ℝ) ≤ ∫ t in (10000000 : ℝ)..100000000, 1 / log t ∧
    ∫ t in (10000000 : ℝ)..100000000, 1 / log t ≤ 5097290.970400 := by
  sorry

/-- PROVED: `1 / log t` is interval integrable on any interval inside `[2, ∞)`. -/
lemma ii (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have h2 : ∀ t ∈ Set.uIcc a b, 2 ≤ t := fun t ht => le_trans (le_min ha hb) ht.1
  apply ContinuousOn.div continuousOn_const
  · exact continuousOn_log.mono (fun t ht => by
      have := h2 t ht
      exact Set.mem_compl_singleton_iff.mpr (by linarith : (0 : ℝ) < t).ne')
  · intro t ht
    have := h2 t ht
    exact (log_pos (by linarith)).ne'

/-- PROVED from the nine LEAFs: `5762209.37 ≤ li 10⁸ ≤ 5762209.38`. -/
theorem liPV_1e8_S76 : 5762209.37 ≤ liPV (10 ^ 8) ∧ liPV (10 ^ 8) ≤ 5762209.38 := by
  rw [show (10 : ℝ) ^ 8 = 100000000 by norm_num, liPV_eq_add (by norm_num)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii 2 10000000 (by norm_num) (by norm_num))
      (ii 10000000 _ (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii 2 1000000 (by norm_num) (by norm_num))
      (ii 1000000 _ (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii 2 100000 (by norm_num) (by norm_num))
      (ii 100000 _ (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii 2 10000 (by norm_num) (by norm_num))
      (ii 10000 _ (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii 2 1000 (by norm_num) (by norm_num))
      (ii 1000 _ (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii 2 100 (by norm_num) (by norm_num))
      (ii 100 _ (by norm_num) (by norm_num))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii 2 10 (by norm_num) (by norm_num))
      (ii 10 _ (by norm_num) (by norm_num))]
  have := liPV_two_encl
  have := liPiece_0
  have := liPiece_1
  have := liPiece_2
  have := liPiece_3
  have := liPiece_4
  have := liPiece_5
  have := liPiece_6
  have := liPiece_7
  constructor <;> linarith

end LeanLab.BS2022GRH.SchoenfeldXiBlocksS76

#print axioms LeanLab.BS2022GRH.SchoenfeldXiBlocksS76.primeCount_1e8_S76
#print axioms LeanLab.BS2022GRH.SchoenfeldXiBlocksS76.theta_1e8_S76
#print axioms LeanLab.BS2022GRH.SchoenfeldXiBlocksS76.liPV_1e8_S76
