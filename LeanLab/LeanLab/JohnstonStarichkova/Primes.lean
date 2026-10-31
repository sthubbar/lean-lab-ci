/-
The primes from 17 to 2579 as an explicit list, with nth identified, unit U-0342,
run 20261017T1803Z-21479. P17 is "prime and at least 17", the primes coprime to 30030.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.JohnstonStarichkova

open Nat

/-- The 370 primes from 17 to 2579, so `Q.getD i 0` is the prime p with index i + 7. -/
def Q : List ℕ := [17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579]

/-! ### `primeB` is complete, so it decides primality -/

theorem noDivFrom_complete {n : ℕ} (hn : n.Prime) : ∀ fuel d, 2 ≤ d → 1 ≤ fuel →
    n < (d + fuel - 1) * (d + fuel - 1) → noDivFrom n fuel d = true := by
  intro fuel
  induction fuel with
  | zero => intro d _ h; omega
  | succ f ih =>
    intro d hd _ hlt
    simp only [noDivFrom]
    by_cases h1 : n < d * d
    · simp [h1]
    · rw [if_neg h1]
      have hdn : d < n := by nlinarith
      have hmod : ¬ n % d = 0 := by
        intro h0
        rcases hn.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h0) with h | h <;> omega
      rw [if_neg hmod]
      rcases Nat.eq_zero_or_pos f with rfl | hf
      · have : d + (0 + 1) - 1 = d := by omega
        rw [this] at hlt
        exact absurd hlt h1
      · apply ih (d + 1) (by omega) hf
        have : d + 1 + f - 1 = d + (f + 1) - 1 := by omega
        rw [this]; exact hlt

theorem primeB_complete {n : ℕ} (hn : n.Prime) : primeB n = true := by
  have h2 := hn.two_le
  have hf : noDivFrom n n 2 = true := by
    apply noDivFrom_complete hn n 2 le_rfl (by omega)
    have : 2 + n - 1 = n + 1 := by omega
    rw [this]; nlinarith
  simp [primeB, h2, hf]

theorem primeB_iff {n : ℕ} : primeB n = true ↔ n.Prime := ⟨primeB_sound, primeB_complete⟩

/-- Primes at least 17. -/
def P17 (p : ℕ) : Prop := p.Prime ∧ 17 ≤ p

instance : DecidablePred P17 := fun p => by unfold P17; infer_instance

/-- Boolean form of `P17`. -/
def b17 (n : ℕ) : Bool := decide (17 ≤ n) && primeB n

theorem b17_iff {n : ℕ} : b17 n = true ↔ P17 n := by
  simp only [b17, Bool.and_eq_true, decide_eq_true_eq, primeB_iff, P17]; tauto

theorem P17_infinite : (Set.ofPred P17).Infinite := by
  refine (Nat.infinite_setOf_prime.diff (Set.finite_lt_nat 17)).mono ?_
  intro p hp
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_lt] at hp
  exact ⟨hp.1, hp.2⟩

theorem count_congr' {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] (h : ∀ n, p n ↔ q n)
    (n : ℕ) : count p n = count q n := by
  simp only [count_eq_card_filter_range]
  congr 1
  ext x
  simp [h x]

/-! ### A walker: counts at consecutive list entries -/

/-- Each entry passes `b`, entries increase, and the gap up to the next holds exactly one `b`. -/
def stepB (b : ℕ → Bool) : List ℕ → Bool
  | a :: c :: t => (decide (a < c) && b a && decide (count (fun k => b (a + k) = true) (c - a) = 1))
      && stepB b (c :: t)
  | _ => true

theorem walk (b : ℕ → Bool) : ∀ (t : List ℕ) (a i : ℕ), stepB b (a :: t) = true →
    count (fun k => b k = true) a = i →
    ∀ j, j < (a :: t).length → count (fun k => b k = true) ((a :: t).getD j 0) = i + j := by
  intro t
  induction t with
  | nil =>
    intro a i _ hc j hj
    simp only [List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    simpa using hc
  | cons c t ih =>
    intro a i h hc j hj
    simp only [stepB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hac, _⟩, hgap⟩, hrest⟩ := h
    have hcc : count (fun k => b k = true) c = i + 1 := by
      have : c = a + (c - a) := by omega
      rw [this, count_add, hc, hgap]
    rcases j with _ | j
    · simpa using hc
    · have := ih c (i + 1) hrest hcc j (by simp at hj ⊢; omega)
      simp only [List.getD_cons_succ]
      rw [this]; ring

theorem stepB_17 : stepB b17 Q = true := by decide +kernel

theorem stepB_prime : stepB primeB Q = true := by decide +kernel

theorem Q_b17 : ∀ i < 370, b17 (Q.getD i 0) = true := by
  have h : (List.range 370).all (fun i => b17 (Q.getD i 0)) = true := by decide +kernel
  intro i hi
  exact List.all_eq_true.mp h i (List.mem_range.mpr hi)

theorem Q_length : Q.length = 370 := by decide +kernel

theorem Q_head : Q = 17 :: Q.tail := by decide +kernel

/-- `nth P17 i` is the i-th entry of Q, for i < 370. -/
theorem nth_P17 {i : ℕ} (hi : i < 370) : nth P17 i = Q.getD i 0 := by
  have hb : count (fun k => b17 k = true) 17 = 0 := by decide +kernel
  have hw := walk b17 Q.tail 17 0 (by rw [← Q_head]; exact stepB_17) hb i
    (by rw [← Q_head, Q_length]; exact hi)
  rw [← Q_head, zero_add] at hw
  have hc : count P17 (Q.getD i 0) = i := by
    rw [count_congr' (fun n => b17_iff.symm)]; exact hw
  calc nth P17 i = nth P17 (count P17 (Q.getD i 0)) := by rw [hc]
    _ = Q.getD i 0 := nth_count (b17_iff.mp (Q_b17 i hi))

/-- `nth Nat.Prime (i + 6)` is the i-th entry of Q: Q lists p_7 to p_376, one-indexed. -/
theorem nth_prime_Q {i : ℕ} (hi : i < 370) : nth Nat.Prime (i + 6) = Q.getD i 0 := by
  have hb : count (fun k => primeB k = true) 17 = 6 := by decide +kernel
  have hw := walk primeB Q.tail 17 6 (by rw [← Q_head]; exact stepB_prime) hb i
    (by rw [← Q_head, Q_length]; exact hi)
  rw [← Q_head] at hw
  have hc : count Nat.Prime (Q.getD i 0) = i + 6 := by
    rw [count_congr' (fun n => primeB_iff.symm)]; rw [hw]; ring
  calc nth Nat.Prime (i + 6) = nth Nat.Prime (count Nat.Prime (Q.getD i 0)) := by rw [hc]
    _ = Q.getD i 0 := nth_count ((b17_iff.mp (Q_b17 i hi)).1)

end LeanLab.JohnstonStarichkova
