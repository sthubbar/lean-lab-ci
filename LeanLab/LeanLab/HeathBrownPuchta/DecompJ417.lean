import LeanLab.HeathBrownPuchta.Assembly
import LeanLab.HeathBrownPuchta.Lemma8Const
import LeanLab.HeathBrownPuchta.Decomp130

/-!
# Heath-Brown and Puchta (2002), displays 40 and 41

`DecompJ417.lean` leaves two constants of the paper: the twin prime product
`C₀ = ∏_{p > 2} (1 - 1/(p-1)²)` and `C₂ = Σ_d k(d)/ε(d)`.

`c0_bound` (`66/100 ≤ C₀`) is proved here unconditionally.  The paper's own value is
`C₀ = 0.6601618158…`, so the claim is a numerical computation with a relative margin of
`2.5 · 10⁻⁴`: no argument from prime number theory supplies it, it is checked by multiplying
the factors out.  The product is split into the blocks `[500j, 500(j+1))` below; inside a
block the set of odd primes is an explicit literal, checked by `decide`, and the block's
value is a truncation of the exact rational product, checked by `norm_num`.  The tail beyond
`5000` is bounded by `∏(1-a) ≥ 1 - Σa` and the telescoping estimate
`Σ_{n ≥ 5000} 1/(n-1)² ≤ 1/4999`.

`c2_bound` is not touched: it reduces exactly to the Liu, Liu and Wang input `LLW`
(`SReduction.LLW`), which no file in this import closure proves.
-/

open Real Filter Topology

namespace LeanLab.HeathBrownPuchta.DecompJ417

/-- The deficit of the `n`-th factor of `C₀` from `1`; nonzero only at odd primes. -/
private noncomputable def GG (n : ℕ) : ℝ :=
  if n.Prime ∧ 2 < n then 1 / ((n : ℝ) - 1) ^ 2 else 0

private lemma GG_nonneg (n : ℕ) : 0 ≤ GG n := by
  unfold GG
  split_ifs with h
  · have h3n : 3 ≤ n := by
      have := h.1.two_le
      omega
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3n
    exact div_nonneg zero_le_one (by nlinarith)
  · exact le_rfl

private lemma GG_le_one (n : ℕ) : GG n ≤ 1 := by
  unfold GG
  split_ifs with h
  · have h3n : 3 ≤ n := by
      have := h.1.two_le
      omega
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3n
    rw [div_le_one (by nlinarith)]
    nlinarith
  · exact zero_le_one

/-- `Σ (n+1)⁻²` converges, so `Σ GG` converges as well. -/
private lemma summable_GG : Summable GG := by
  rw [← summable_nat_add_iff 2]
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
      (summable_one_div_nat_pow (p := 2)).2 (by norm_num)
    have h3 := (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ)) ^ 2) 1).2 h2
    simpa only [Nat.cast_add, Nat.cast_one] using h3
  refine Summable.of_nonneg_of_le (fun n => GG_nonneg (n + 2)) (fun n => ?_) hbase
  unfold GG
  split_ifs with h
  · have e : (((n + 2 : ℕ)) : ℝ) - 1 = (n : ℝ) + 1 := by push_cast; ring
    rw [e]
  · exact div_nonneg zero_le_one (sq_nonneg _)

/-- Every partial product of the factors `1 - GG` is at most `1`. -/
private lemma prod_one_le (s : Finset ℕ) : ∏ i ∈ s, (1 - GG i) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have h1 : 0 ≤ 1 - GG a := by linarith [GG_le_one a]
      have h2 : 1 - GG a ≤ 1 := by linarith [GG_nonneg a]
      have h3 : 0 ≤ ∏ i ∈ s, (1 - GG i) :=
        Finset.prod_nonneg fun i _ => by linarith [GG_le_one i]
      nlinarith [ih, h1, h2, h3]

/-- A finite product of factors `1 - a` with `0 ≤ a ≤ 1` is at least `1 - Σ a`. -/
private lemma one_sub_sum_le_prod (s : Finset ℕ) :
    1 - ∑ i ∈ s, GG i ≤ ∏ i ∈ s, (1 - GG i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hP0 : 0 ≤ ∏ i ∈ s, (1 - GG i) :=
        Finset.prod_nonneg fun i _ => by linarith [GG_le_one i]
      have hP1 : ∏ i ∈ s, (1 - GG i) ≤ 1 := prod_one_le s
      have ha0 : 0 ≤ GG a := GG_nonneg a
      have hkey : 0 ≤ GG a * (1 - ∏ i ∈ s, (1 - GG i)) :=
        mul_nonneg ha0 (by linarith)
      have h2 : (∏ i ∈ s, (1 - GG i)) - GG a ≤
          (∏ i ∈ s, (1 - GG i)) * (1 - GG a) := by nlinarith [hkey]
      linarith [ih]

/-- The tail sum: `Σ_{M < i < n} GG i ≤ 1/(M-1)`, by telescoping with `1/(i-2) - 1/(i-1)`. -/
private lemma tail_sum_le (M : ℕ) (hM : 3 ≤ M) (n : ℕ) :
    ∑ i ∈ Finset.Ico (M + 1) n, GG i ≤ 1 / ((M : ℝ) - 1) := by
  have hpt : ∀ i ∈ Finset.Ico (M + 1) n,
      GG i ≤ 1 / ((i : ℝ) - 2) - 1 / ((i : ℝ) - 1) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have h3 : (3 : ℝ) ≤ (i : ℝ) := by
      have : 3 ≤ i := by omega
      exact_mod_cast this
    have hA : 0 < ((i : ℝ) - 1) ^ 2 := by nlinarith
    have hB : 0 < ((i : ℝ) - 2) * ((i : ℝ) - 1) := by nlinarith
    have hle : ((i : ℝ) - 2) * ((i : ℝ) - 1) ≤ ((i : ℝ) - 1) ^ 2 := by nlinarith
    have h1 : GG i ≤ 1 / ((i : ℝ) - 1) ^ 2 := by
      unfold GG
      split_ifs with h
      · exact le_rfl
      · exact div_nonneg zero_le_one (le_of_lt hA)
    have h2 : 1 / ((i : ℝ) - 1) ^ 2 ≤ 1 / (((i : ℝ) - 2) * ((i : ℝ) - 1)) :=
      one_div_le_one_div_of_le hB hle
    have h3' : 1 / (((i : ℝ) - 2) * ((i : ℝ) - 1)) =
        1 / ((i : ℝ) - 2) - 1 / ((i : ℝ) - 1) := by
      have hb1 : ((i : ℝ) - 2) ≠ 0 := by linarith
      have hb2 : ((i : ℝ) - 1) ≠ 0 := by linarith
      field_simp
      ring
    linarith [h1, h2, h3']
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_Ico_eq_sum_range]
  have hcongr : ∀ k : ℕ,
      1 / ((((M + 1 + k : ℕ)) : ℝ) - 2) - 1 / ((((M + 1 + k : ℕ)) : ℝ) - 1) =
        1 / ((k : ℝ) + ((M : ℝ) - 1)) - 1 / (((k + 1 : ℕ) : ℝ) + ((M : ℝ) - 1)) := by
    intro k
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun k _ => hcongr k)]
  rw [Finset.sum_range_sub' (fun k : ℕ => 1 / ((k : ℝ) + ((M : ℝ) - 1)))]
  simp only [Nat.cast_zero, zero_add]
  have hM1 : (0 : ℝ) ≤ (M : ℝ) - 1 := by
    have h3 : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hnn : 0 ≤ 1 / (((n - (M + 1) : ℕ) : ℝ) + ((M : ℝ) - 1)) :=
    div_nonneg zero_le_one (by positivity)
  linarith [hnn]

/-- A product of the factors `1 - GG` equals the same product restricted to the odd primes:
off the odd primes the factor is `1`. -/
private lemma prod_sub_one_GG (s : Finset ℕ) :
    ∏ i ∈ s, (1 - GG i) = ∏ i ∈ s.filter (fun n => n.Prime ∧ 2 < n), (1 - GG i) := by
  classical
  rw [Finset.prod_filter]
  exact (Finset.prod_congr rfl (fun x _ => by
    by_cases h : x.Prime ∧ 2 < x
    · simp [GG, h]
    · simp [GG, h])).symm

/-- A primality test for `n < 5001`: `n` is prime iff no `m` with `2 ≤ m ≤ 70` other than `n`
itself divides `n`.  This is what makes the blocks below checkable by `decide`: Lean's own
`Nat.Prime` instance runs the trial division in the kernel, which does not fit in memory for
`5000` numbers at once, while a `69`-element divisor test does. -/
private lemma prime_iff_small (n : ℕ) (hn : n < 5001) :
    n.Prime ↔ 2 ≤ n ∧ ∀ m ∈ Finset.Ico 2 71, n % m ≠ 0 ∨ m = n := by
  constructor
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    intro m hm
    have hm2 : 2 ≤ m := (Finset.mem_Ico.mp hm).1
    by_cases hd : m ∣ n
    · rcases hp.eq_one_or_self_of_dvd m hd with h1 | h1
      · omega
      · exact Or.inr h1
    · exact Or.inl (fun h => hd (Nat.dvd_of_mod_eq_zero h))
  · rintro ⟨h2, h⟩
    rw [Nat.prime_def_lt']
    refine ⟨h2, ?_⟩
    intro m hm2 hmn hdvd
    by_cases hms : m ≤ 70
    · have hmem : m ∈ Finset.Ico 2 71 := by rw [Finset.mem_Ico]; omega
      rcases h m hmem with hk | hk
      · exact absurd (Nat.dvd_iff_mod_eq_zero.mp hdvd) hk
      · omega
    · push Not at hms
      have hq : n / m * m = n := Nat.div_mul_cancel hdvd
      have hq2 : 2 ≤ n / m := by
        rcases Nat.lt_or_ge (n / m) 2 with hlt | hge
        · interval_cases hj : n / m
          · simp at hq; omega
          · simp at hq; omega
        · exact hge
      have hq70 : n / m ≤ 70 := by
        by_contra hcon
        push Not at hcon
        have hA : 71 * (n / m) ≤ m * (n / m) := Nat.mul_le_mul_right _ (by omega : 71 ≤ m)
        rw [Nat.mul_comm m (n / m), hq] at hA
        have hB : 71 * 71 ≤ 71 * (n / m) := Nat.mul_le_mul_left 71 hcon
        have hC : 71 * 71 ≤ n := le_trans hB hA
        omega
      have hmem : n / m ∈ Finset.Ico 2 71 := by rw [Finset.mem_Ico]; omega
      have hdvd' : (n / m) ∣ n := ⟨m, hq.symm⟩
      rcases h (n / m) hmem with hk | hk
      · exact absurd (Nat.dvd_iff_mod_eq_zero.mp hdvd') hk
      · rw [hk] at hq
        have hm1 : m = 1 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < n) (by rw [Nat.mul_one]; exact hq)
        omega


/-- The odd primes in `[0, 500)`. -/
private def PR0 : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private lemma PR0_eq :
    (Finset.Ico 0 500).filter (fun n => n.Prime ∧ 2 < n) = PR0 := by
  have h : (Finset.Ico 0 500).filter (fun n => n.Prime ∧ 2 < n) =
      (Finset.Ico 0 500).filter (fun n => (2 ≤ n ∧ ∀ m ∈ Finset.Ico 2 71, n % m ≠ 0 ∨ m = n) ∧ 2 < n) := by
    apply Finset.filter_congr
    intro n hn
    have hn' : n < 5001 := by
      have := (Finset.mem_Ico.mp hn).2; omega
    rw [prime_iff_small n hn']
  rw [h]
  decide

private lemma PR0_prime : ∀ p ∈ PR0, p.Prime ∧ 2 < p := by
  intro p hp
  have h : p ∈ (Finset.Ico 0 500).filter (fun n => n.Prime ∧ 2 < n) := by
    rw [PR0_eq]; exact hp
  exact (Finset.mem_filter.mp h).2

set_option maxHeartbeats 1600000 in
private lemma PR0_ge : (0.660342594355313889 : ℝ) ≤
    ∏ p ∈ PR0, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [PR0]
  norm_num

/-- The odd primes in `[500, 1000)`. -/
private def PR1 : Finset ℕ := {503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private lemma PR1_eq :
    (Finset.Ico 500 1000).filter (fun n => n.Prime ∧ 2 < n) = PR1 := by
  have h : (Finset.Ico 500 1000).filter (fun n => n.Prime ∧ 2 < n) =
      (Finset.Ico 500 1000).filter (fun n => (2 ≤ n ∧ ∀ m ∈ Finset.Ico 2 71, n % m ≠ 0 ∨ m = n) ∧ 2 < n) := by
    apply Finset.filter_congr
    intro n hn
    have hn' : n < 5001 := by
      have := (Finset.mem_Ico.mp hn).2; omega
    rw [prime_iff_small n hn']
  rw [h]
  decide

private lemma PR1_prime : ∀ p ∈ PR1, p.Prime ∧ 2 < p := by
  intro p hp
  have h : p ∈ (Finset.Ico 500 1000).filter (fun n => n.Prime ∧ 2 < n) := by
    rw [PR1_eq]; exact hp
  exact (Finset.mem_filter.mp h).2

set_option maxHeartbeats 1600000 in
private lemma PR1_ge : (0.999853333125348759 : ℝ) ≤
    ∏ p ∈ PR1, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [PR1]
  norm_num

/-- The odd primes in `[1000, 1500)`. -/
private def PR2 : Finset ℕ := {1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private lemma PR2_eq :
    (Finset.Ico 1000 1500).filter (fun n => n.Prime ∧ 2 < n) = PR2 := by
  have h : (Finset.Ico 1000 1500).filter (fun n => n.Prime ∧ 2 < n) =
      (Finset.Ico 1000 1500).filter (fun n => (2 ≤ n ∧ ∀ m ∈ Finset.Ico 2 71, n % m ≠ 0 ∨ m = n) ∧ 2 < n) := by
    apply Finset.filter_congr
    intro n hn
    have hn' : n < 5001 := by
      have := (Finset.mem_Ico.mp hn).2; omega
    rw [prime_iff_small n hn']
  rw [h]
  decide

private lemma PR2_prime : ∀ p ∈ PR2, p.Prime ∧ 2 < p := by
  intro p hp
  have h : p ∈ (Finset.Ico 1000 1500).filter (fun n => n.Prime ∧ 2 < n) := by
    rw [PR2_eq]; exact hp
  exact (Finset.mem_filter.mp h).2

set_option maxHeartbeats 1600000 in
private lemma PR2_ge : (0.999952574699081837 : ℝ) ≤
    ∏ p ∈ PR2, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [PR2]
  norm_num

/-- The odd primes in `[1500, 2000)`. -/
private def PR3 : Finset ℕ := {1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private lemma PR3_eq :
    (Finset.Ico 1500 2000).filter (fun n => n.Prime ∧ 2 < n) = PR3 := by
  have h : (Finset.Ico 1500 2000).filter (fun n => n.Prime ∧ 2 < n) =
      (Finset.Ico 1500 2000).filter (fun n => (2 ≤ n ∧ ∀ m ∈ Finset.Ico 2 71, n % m ≠ 0 ∨ m = n) ∧ 2 < n) := by
    apply Finset.filter_congr
    intro n hn
    have hn' : n < 5001 := by
      have := (Finset.mem_Ico.mp hn).2; omega
    rw [prime_iff_small n hn']
  rw [h]
  decide

private lemma PR3_prime : ∀ p ∈ PR3, p.Prime ∧ 2 < p := by
  intro p hp
  have h : p ∈ (Finset.Ico 1500 2000).filter (fun n => n.Prime ∧ 2 < n) := by
    rw [PR3_eq]; exact hp
  exact (Finset.mem_filter.mp h).2

set_option maxHeartbeats 1600000 in
private lemma PR3_ge : (0.999978646811342536 : ℝ) ≤
    ∏ p ∈ PR3, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [PR3]
  norm_num

/-- The odd primes in `[2000, 2500)`. -/
private def PR4 : Finset ℕ := {2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private lemma PR4_eq :
    (Finset.Ico 2000 2500).filter (fun n => n.Prime ∧ 2 < n) = PR4 := by
  have h : (Finset.Ico 2000 2500).filter (fun n => n.Prime ∧ 2 < n) =
      (Finset.Ico 2000 2500).filter (fun n => (2 ≤ n ∧ ∀ m ∈ Finset.Ico 2 71, n % m ≠ 0 ∨ m = n) ∧ 2 < n) := by
    apply Finset.filter_congr
    intro n hn
    have hn' : n < 5001 := by
      have := (Finset.mem_Ico.mp hn).2; omega
    rw [prime_iff_small n hn']
  rw [h]
  decide

private lemma PR4_prime : ∀ p ∈ PR4, p.Prime ∧ 2 < p := by
  intro p hp
  have h : p ∈ (Finset.Ico 2000 2500).filter (fun n => n.Prime ∧ 2 < n) := by
    rw [PR4_eq]; exact hp
  exact (Finset.mem_filter.mp h).2

set_option maxHeartbeats 1600000 in
private lemma PR4_ge : (0.999987152532912506 : ℝ) ≤
    ∏ p ∈ PR4, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [PR4]
  norm_num

/-- The odd primes in `[2500, 3000)`. -/
private def PR5 : Finset ℕ := {2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private lemma PR5_eq :
    (Finset.Ico 2500 3000).filter (fun n => n.Prime ∧ 2 < n) = PR5 := by
  have h : (Finset.Ico 2500 3000).filter (fun n => n.Prime ∧ 2 < n) =
      (Finset.Ico 2500 3000).filter (fun n => (2 ≤ n ∧ ∀ m ∈ Finset.Ico 2 71, n % m ≠ 0 ∨ m = n) ∧ 2 < n) := by
    apply Finset.filter_congr
    intro n hn
    have hn' : n < 5001 := by
      have := (Finset.mem_Ico.mp hn).2; omega
    rw [prime_iff_small n hn']
  rw [h]
  decide

private lemma PR5_prime : ∀ p ∈ PR5, p.Prime ∧ 2 < p := by
  intro p hp
  have h : p ∈ (Finset.Ico 2500 3000).filter (fun n => n.Prime ∧ 2 < n) := by
    rw [PR5_eq]; exact hp
  exact (Finset.mem_filter.mp h).2

set_option maxHeartbeats 1600000 in
private lemma PR5_ge : (0.999991579558463738 : ℝ) ≤
    ∏ p ∈ PR5, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [PR5]
  norm_num

/-- The odd primes in `[3000, 3500)`. -/
private def PR6 : Finset ℕ := {3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private lemma PR6_eq :
    (Finset.Ico 3000 3500).filter (fun n => n.Prime ∧ 2 < n) = PR6 := by
  have h : (Finset.Ico 3000 3500).filter (fun n => n.Prime ∧ 2 < n) =
      (Finset.Ico 3000 3500).filter (fun n => (2 ≤ n ∧ ∀ m ∈ Finset.Ico 2 71, n % m ≠ 0 ∨ m = n) ∧ 2 < n) := by
    apply Finset.filter_congr
    intro n hn
    have hn' : n < 5001 := by
      have := (Finset.mem_Ico.mp hn).2; omega
    rw [prime_iff_small n hn']
  rw [h]
  decide

private lemma PR6_prime : ∀ p ∈ PR6, p.Prime ∧ 2 < p := by
  intro p hp
  have h : p ∈ (Finset.Ico 3000 3500).filter (fun n => n.Prime ∧ 2 < n) := by
    rw [PR6_eq]; exact hp
  exact (Finset.mem_filter.mp h).2

set_option maxHeartbeats 1600000 in
private lemma PR6_ge : (0.999994388437512587 : ℝ) ≤
    ∏ p ∈ PR6, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [PR6]
  norm_num

/-- The odd primes in `[3500, 4000)`. -/
private def PR7 : Finset ℕ := {3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private lemma PR7_eq :
    (Finset.Ico 3500 4000).filter (fun n => n.Prime ∧ 2 < n) = PR7 := by
  have h : (Finset.Ico 3500 4000).filter (fun n => n.Prime ∧ 2 < n) =
      (Finset.Ico 3500 4000).filter (fun n => (2 ≤ n ∧ ∀ m ∈ Finset.Ico 2 71, n % m ≠ 0 ∨ m = n) ∧ 2 < n) := by
    apply Finset.filter_congr
    intro n hn
    have hn' : n < 5001 := by
      have := (Finset.mem_Ico.mp hn).2; omega
    rw [prime_iff_small n hn']
  rw [h]
  decide

private lemma PR7_prime : ∀ p ∈ PR7, p.Prime ∧ 2 < p := by
  intro p hp
  have h : p ∈ (Finset.Ico 3500 4000).filter (fun n => n.Prime ∧ 2 < n) := by
    rw [PR7_eq]; exact hp
  exact (Finset.mem_filter.mp h).2

set_option maxHeartbeats 1600000 in
private lemma PR7_ge : (0.999995602805418470 : ℝ) ≤
    ∏ p ∈ PR7, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [PR7]
  norm_num

/-- The odd primes in `[4000, 4500)`. -/
private def PR8 : Finset ℕ := {4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private lemma PR8_eq :
    (Finset.Ico 4000 4500).filter (fun n => n.Prime ∧ 2 < n) = PR8 := by
  have h : (Finset.Ico 4000 4500).filter (fun n => n.Prime ∧ 2 < n) =
      (Finset.Ico 4000 4500).filter (fun n => (2 ≤ n ∧ ∀ m ∈ Finset.Ico 2 71, n % m ≠ 0 ∨ m = n) ∧ 2 < n) := by
    apply Finset.filter_congr
    intro n hn
    have hn' : n < 5001 := by
      have := (Finset.mem_Ico.mp hn).2; omega
    rw [prime_iff_small n hn']
  rw [h]
  decide

private lemma PR8_prime : ∀ p ∈ PR8, p.Prime ∧ 2 < p := by
  intro p hp
  have h : p ∈ (Finset.Ico 4000 4500).filter (fun n => n.Prime ∧ 2 < n) := by
    rw [PR8_eq]; exact hp
  exact (Finset.mem_filter.mp h).2

set_option maxHeartbeats 1600000 in
private lemma PR8_ge : (0.999996642008212886 : ℝ) ≤
    ∏ p ∈ PR8, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [PR8]
  norm_num

/-- The odd primes in `[4500, 5000)`. -/
private def PR9 : Finset ℕ := {4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private lemma PR9_eq :
    (Finset.Ico 4500 5000).filter (fun n => n.Prime ∧ 2 < n) = PR9 := by
  have h : (Finset.Ico 4500 5000).filter (fun n => n.Prime ∧ 2 < n) =
      (Finset.Ico 4500 5000).filter (fun n => (2 ≤ n ∧ ∀ m ∈ Finset.Ico 2 71, n % m ≠ 0 ∨ m = n) ∧ 2 < n) := by
    apply Finset.filter_congr
    intro n hn
    have hn' : n < 5001 := by
      have := (Finset.mem_Ico.mp hn).2; omega
    rw [prime_iff_small n hn']
  rw [h]
  decide

private lemma PR9_prime : ∀ p ∈ PR9, p.Prime ∧ 2 < p := by
  intro p hp
  have h : p ∈ (Finset.Ico 4500 5000).filter (fun n => n.Prime ∧ 2 < n) := by
    rw [PR9_eq]; exact hp
  exact (Finset.mem_filter.mp h).2

set_option maxHeartbeats 1600000 in
private lemma PR9_ge : (0.999997380356563408 : ℝ) ≤
    ∏ p ∈ PR9, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [PR9]
  norm_num

/-- The odd primes in `[5000, 5001)`. -/
private def PR10 : Finset ℕ := ∅

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private lemma PR10_eq :
    (Finset.Ico 5000 5001).filter (fun n => n.Prime ∧ 2 < n) = PR10 := by
  have h : (Finset.Ico 5000 5001).filter (fun n => n.Prime ∧ 2 < n) =
      (Finset.Ico 5000 5001).filter (fun n => (2 ≤ n ∧ ∀ m ∈ Finset.Ico 2 71, n % m ≠ 0 ∨ m = n) ∧ 2 < n) := by
    apply Finset.filter_congr
    intro n hn
    have hn' : n < 5001 := by
      have := (Finset.mem_Ico.mp hn).2; omega
    rw [prime_iff_small n hn']
  rw [h]
  decide

private lemma PR10_prime : ∀ p ∈ PR10, p.Prime ∧ 2 < p := by
  intro p hp
  have h : p ∈ (Finset.Ico 5000 5001).filter (fun n => n.Prime ∧ 2 < n) := by
    rw [PR10_eq]; exact hp
  exact (Finset.mem_filter.mp h).2

set_option maxHeartbeats 1600000 in
private lemma PR10_ge : (1.000000000000000000 : ℝ) ≤
    ∏ p ∈ PR10, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [PR10]
  norm_num

private lemma blk0 : (0.660342594355313889 : ℝ) ≤ ∏ i ∈ Finset.Ico 0 500, (1 - GG i) := by
  rw [prod_sub_one_GG, PR0_eq]
  have hPQ : (∏ p ∈ PR0, (1 - GG p)) = ∏ p ∈ PR0, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
    Finset.prod_congr rfl (fun p hp => by
      have h := PR0_prime p hp
      unfold GG
      rw [ite_eq_left h])
  rw [hPQ]
  exact PR0_ge

private lemma blk1 : (0.999853333125348759 : ℝ) ≤ ∏ i ∈ Finset.Ico 500 1000, (1 - GG i) := by
  rw [prod_sub_one_GG, PR1_eq]
  have hPQ : (∏ p ∈ PR1, (1 - GG p)) = ∏ p ∈ PR1, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
    Finset.prod_congr rfl (fun p hp => by
      have h := PR1_prime p hp
      unfold GG
      rw [ite_eq_left h])
  rw [hPQ]
  exact PR1_ge

private lemma blk2 : (0.999952574699081837 : ℝ) ≤ ∏ i ∈ Finset.Ico 1000 1500, (1 - GG i) := by
  rw [prod_sub_one_GG, PR2_eq]
  have hPQ : (∏ p ∈ PR2, (1 - GG p)) = ∏ p ∈ PR2, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
    Finset.prod_congr rfl (fun p hp => by
      have h := PR2_prime p hp
      unfold GG
      rw [ite_eq_left h])
  rw [hPQ]
  exact PR2_ge

private lemma blk3 : (0.999978646811342536 : ℝ) ≤ ∏ i ∈ Finset.Ico 1500 2000, (1 - GG i) := by
  rw [prod_sub_one_GG, PR3_eq]
  have hPQ : (∏ p ∈ PR3, (1 - GG p)) = ∏ p ∈ PR3, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
    Finset.prod_congr rfl (fun p hp => by
      have h := PR3_prime p hp
      unfold GG
      rw [ite_eq_left h])
  rw [hPQ]
  exact PR3_ge

private lemma blk4 : (0.999987152532912506 : ℝ) ≤ ∏ i ∈ Finset.Ico 2000 2500, (1 - GG i) := by
  rw [prod_sub_one_GG, PR4_eq]
  have hPQ : (∏ p ∈ PR4, (1 - GG p)) = ∏ p ∈ PR4, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
    Finset.prod_congr rfl (fun p hp => by
      have h := PR4_prime p hp
      unfold GG
      rw [ite_eq_left h])
  rw [hPQ]
  exact PR4_ge

private lemma blk5 : (0.999991579558463738 : ℝ) ≤ ∏ i ∈ Finset.Ico 2500 3000, (1 - GG i) := by
  rw [prod_sub_one_GG, PR5_eq]
  have hPQ : (∏ p ∈ PR5, (1 - GG p)) = ∏ p ∈ PR5, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
    Finset.prod_congr rfl (fun p hp => by
      have h := PR5_prime p hp
      unfold GG
      rw [ite_eq_left h])
  rw [hPQ]
  exact PR5_ge

private lemma blk6 : (0.999994388437512587 : ℝ) ≤ ∏ i ∈ Finset.Ico 3000 3500, (1 - GG i) := by
  rw [prod_sub_one_GG, PR6_eq]
  have hPQ : (∏ p ∈ PR6, (1 - GG p)) = ∏ p ∈ PR6, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
    Finset.prod_congr rfl (fun p hp => by
      have h := PR6_prime p hp
      unfold GG
      rw [ite_eq_left h])
  rw [hPQ]
  exact PR6_ge

private lemma blk7 : (0.999995602805418470 : ℝ) ≤ ∏ i ∈ Finset.Ico 3500 4000, (1 - GG i) := by
  rw [prod_sub_one_GG, PR7_eq]
  have hPQ : (∏ p ∈ PR7, (1 - GG p)) = ∏ p ∈ PR7, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
    Finset.prod_congr rfl (fun p hp => by
      have h := PR7_prime p hp
      unfold GG
      rw [ite_eq_left h])
  rw [hPQ]
  exact PR7_ge

private lemma blk8 : (0.999996642008212886 : ℝ) ≤ ∏ i ∈ Finset.Ico 4000 4500, (1 - GG i) := by
  rw [prod_sub_one_GG, PR8_eq]
  have hPQ : (∏ p ∈ PR8, (1 - GG p)) = ∏ p ∈ PR8, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
    Finset.prod_congr rfl (fun p hp => by
      have h := PR8_prime p hp
      unfold GG
      rw [ite_eq_left h])
  rw [hPQ]
  exact PR8_ge

private lemma blk9 : (0.999997380356563408 : ℝ) ≤ ∏ i ∈ Finset.Ico 4500 5000, (1 - GG i) := by
  rw [prod_sub_one_GG, PR9_eq]
  have hPQ : (∏ p ∈ PR9, (1 - GG p)) = ∏ p ∈ PR9, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
    Finset.prod_congr rfl (fun p hp => by
      have h := PR9_prime p hp
      unfold GG
      rw [ite_eq_left h])
  rw [hPQ]
  exact PR9_ge

private lemma blk10 : (1.000000000000000000 : ℝ) ≤ ∏ i ∈ Finset.Ico 5000 5001, (1 - GG i) := by
  rw [prod_sub_one_GG, PR10_eq]
  have hPQ : (∏ p ∈ PR10, (1 - GG p)) = ∏ p ∈ PR10, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
    Finset.prod_congr rfl (fun p hp => by
      have h := PR10_prime p hp
      unfold GG
      rw [ite_eq_left h])
  rw [hPQ]
  exact PR10_ge

set_option maxHeartbeats 1600000 in
private lemma fin_prod_ge : (66017 / 100000 : ℝ) ≤ ∏ i ∈ Finset.range 5001, (1 - GG i) := by
  rw [Finset.range_eq_Ico]
  have sp0 : ∏ i ∈ Finset.Ico 0 5001, (1 - GG i) =
      (∏ i ∈ Finset.Ico 0 500, (1 - GG i)) * ∏ i ∈ Finset.Ico 500 5001, (1 - GG i) :=
    (Finset.prod_Ico_consecutive (fun i : ℕ => (1 - GG i : ℝ)) (by norm_num) (by norm_num)).symm
  have sp1 : ∏ i ∈ Finset.Ico 500 5001, (1 - GG i) =
      (∏ i ∈ Finset.Ico 500 1000, (1 - GG i)) * ∏ i ∈ Finset.Ico 1000 5001, (1 - GG i) :=
    (Finset.prod_Ico_consecutive (fun i : ℕ => (1 - GG i : ℝ)) (by norm_num) (by norm_num)).symm
  have sp2 : ∏ i ∈ Finset.Ico 1000 5001, (1 - GG i) =
      (∏ i ∈ Finset.Ico 1000 1500, (1 - GG i)) * ∏ i ∈ Finset.Ico 1500 5001, (1 - GG i) :=
    (Finset.prod_Ico_consecutive (fun i : ℕ => (1 - GG i : ℝ)) (by norm_num) (by norm_num)).symm
  have sp3 : ∏ i ∈ Finset.Ico 1500 5001, (1 - GG i) =
      (∏ i ∈ Finset.Ico 1500 2000, (1 - GG i)) * ∏ i ∈ Finset.Ico 2000 5001, (1 - GG i) :=
    (Finset.prod_Ico_consecutive (fun i : ℕ => (1 - GG i : ℝ)) (by norm_num) (by norm_num)).symm
  have sp4 : ∏ i ∈ Finset.Ico 2000 5001, (1 - GG i) =
      (∏ i ∈ Finset.Ico 2000 2500, (1 - GG i)) * ∏ i ∈ Finset.Ico 2500 5001, (1 - GG i) :=
    (Finset.prod_Ico_consecutive (fun i : ℕ => (1 - GG i : ℝ)) (by norm_num) (by norm_num)).symm
  have sp5 : ∏ i ∈ Finset.Ico 2500 5001, (1 - GG i) =
      (∏ i ∈ Finset.Ico 2500 3000, (1 - GG i)) * ∏ i ∈ Finset.Ico 3000 5001, (1 - GG i) :=
    (Finset.prod_Ico_consecutive (fun i : ℕ => (1 - GG i : ℝ)) (by norm_num) (by norm_num)).symm
  have sp6 : ∏ i ∈ Finset.Ico 3000 5001, (1 - GG i) =
      (∏ i ∈ Finset.Ico 3000 3500, (1 - GG i)) * ∏ i ∈ Finset.Ico 3500 5001, (1 - GG i) :=
    (Finset.prod_Ico_consecutive (fun i : ℕ => (1 - GG i : ℝ)) (by norm_num) (by norm_num)).symm
  have sp7 : ∏ i ∈ Finset.Ico 3500 5001, (1 - GG i) =
      (∏ i ∈ Finset.Ico 3500 4000, (1 - GG i)) * ∏ i ∈ Finset.Ico 4000 5001, (1 - GG i) :=
    (Finset.prod_Ico_consecutive (fun i : ℕ => (1 - GG i : ℝ)) (by norm_num) (by norm_num)).symm
  have sp8 : ∏ i ∈ Finset.Ico 4000 5001, (1 - GG i) =
      (∏ i ∈ Finset.Ico 4000 4500, (1 - GG i)) * ∏ i ∈ Finset.Ico 4500 5001, (1 - GG i) :=
    (Finset.prod_Ico_consecutive (fun i : ℕ => (1 - GG i : ℝ)) (by norm_num) (by norm_num)).symm
  have sp9 : ∏ i ∈ Finset.Ico 4500 5001, (1 - GG i) =
      (∏ i ∈ Finset.Ico 4500 5000, (1 - GG i)) * ∏ i ∈ Finset.Ico 5000 5001, (1 - GG i) :=
    (Finset.prod_Ico_consecutive (fun i : ℕ => (1 - GG i : ℝ)) (by norm_num) (by norm_num)).symm
  rw [sp0, sp1, sp2, sp3, sp4, sp5, sp6, sp7, sp8, sp9]
  have m10 : ((1.000000000000000000 : ℝ)) ≤ (∏ i ∈ Finset.Ico 5000 5001, (1 - GG i)) := blk10
  have m9 : ((0.999997380356563408 : ℝ) * ((1.000000000000000000 : ℝ))) ≤ (∏ i ∈ Finset.Ico 4500 5000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 5000 5001, (1 - GG i))) :=
    mul_le_mul (blk9) m10 (by norm_num) (le_trans (by norm_num) (blk9))
  have m8 : ((0.999996642008212886 : ℝ) * ((0.999997380356563408 : ℝ) * ((1.000000000000000000 : ℝ)))) ≤ (∏ i ∈ Finset.Ico 4000 4500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4500 5000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 5000 5001, (1 - GG i)))) :=
    mul_le_mul (blk8) m9 (by norm_num) (le_trans (by norm_num) (blk8))
  have m7 : ((0.999995602805418470 : ℝ) * ((0.999996642008212886 : ℝ) * ((0.999997380356563408 : ℝ) * ((1.000000000000000000 : ℝ))))) ≤ (∏ i ∈ Finset.Ico 3500 4000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4000 4500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4500 5000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 5000 5001, (1 - GG i))))) :=
    mul_le_mul (blk7) m8 (by norm_num) (le_trans (by norm_num) (blk7))
  have m6 : ((0.999994388437512587 : ℝ) * ((0.999995602805418470 : ℝ) * ((0.999996642008212886 : ℝ) * ((0.999997380356563408 : ℝ) * ((1.000000000000000000 : ℝ)))))) ≤ (∏ i ∈ Finset.Ico 3000 3500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 3500 4000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4000 4500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4500 5000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 5000 5001, (1 - GG i)))))) :=
    mul_le_mul (blk6) m7 (by norm_num) (le_trans (by norm_num) (blk6))
  have m5 : ((0.999991579558463738 : ℝ) * ((0.999994388437512587 : ℝ) * ((0.999995602805418470 : ℝ) * ((0.999996642008212886 : ℝ) * ((0.999997380356563408 : ℝ) * ((1.000000000000000000 : ℝ))))))) ≤ (∏ i ∈ Finset.Ico 2500 3000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 3000 3500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 3500 4000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4000 4500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4500 5000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 5000 5001, (1 - GG i))))))) :=
    mul_le_mul (blk5) m6 (by norm_num) (le_trans (by norm_num) (blk5))
  have m4 : ((0.999987152532912506 : ℝ) * ((0.999991579558463738 : ℝ) * ((0.999994388437512587 : ℝ) * ((0.999995602805418470 : ℝ) * ((0.999996642008212886 : ℝ) * ((0.999997380356563408 : ℝ) * ((1.000000000000000000 : ℝ)))))))) ≤ (∏ i ∈ Finset.Ico 2000 2500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 2500 3000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 3000 3500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 3500 4000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4000 4500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4500 5000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 5000 5001, (1 - GG i)))))))) :=
    mul_le_mul (blk4) m5 (by norm_num) (le_trans (by norm_num) (blk4))
  have m3 : ((0.999978646811342536 : ℝ) * ((0.999987152532912506 : ℝ) * ((0.999991579558463738 : ℝ) * ((0.999994388437512587 : ℝ) * ((0.999995602805418470 : ℝ) * ((0.999996642008212886 : ℝ) * ((0.999997380356563408 : ℝ) * ((1.000000000000000000 : ℝ))))))))) ≤ (∏ i ∈ Finset.Ico 1500 2000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 2000 2500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 2500 3000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 3000 3500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 3500 4000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4000 4500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4500 5000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 5000 5001, (1 - GG i))))))))) :=
    mul_le_mul (blk3) m4 (by norm_num) (le_trans (by norm_num) (blk3))
  have m2 : ((0.999952574699081837 : ℝ) * ((0.999978646811342536 : ℝ) * ((0.999987152532912506 : ℝ) * ((0.999991579558463738 : ℝ) * ((0.999994388437512587 : ℝ) * ((0.999995602805418470 : ℝ) * ((0.999996642008212886 : ℝ) * ((0.999997380356563408 : ℝ) * ((1.000000000000000000 : ℝ)))))))))) ≤ (∏ i ∈ Finset.Ico 1000 1500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 1500 2000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 2000 2500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 2500 3000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 3000 3500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 3500 4000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4000 4500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4500 5000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 5000 5001, (1 - GG i)))))))))) :=
    mul_le_mul (blk2) m3 (by norm_num) (le_trans (by norm_num) (blk2))
  have m1 : ((0.999853333125348759 : ℝ) * ((0.999952574699081837 : ℝ) * ((0.999978646811342536 : ℝ) * ((0.999987152532912506 : ℝ) * ((0.999991579558463738 : ℝ) * ((0.999994388437512587 : ℝ) * ((0.999995602805418470 : ℝ) * ((0.999996642008212886 : ℝ) * ((0.999997380356563408 : ℝ) * ((1.000000000000000000 : ℝ))))))))))) ≤ (∏ i ∈ Finset.Ico 500 1000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 1000 1500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 1500 2000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 2000 2500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 2500 3000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 3000 3500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 3500 4000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4000 4500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4500 5000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 5000 5001, (1 - GG i))))))))))) :=
    mul_le_mul (blk1) m2 (by norm_num) (le_trans (by norm_num) (blk1))
  have m0 : ((0.660342594355313889 : ℝ) * ((0.999853333125348759 : ℝ) * ((0.999952574699081837 : ℝ) * ((0.999978646811342536 : ℝ) * ((0.999987152532912506 : ℝ) * ((0.999991579558463738 : ℝ) * ((0.999994388437512587 : ℝ) * ((0.999995602805418470 : ℝ) * ((0.999996642008212886 : ℝ) * ((0.999997380356563408 : ℝ) * ((1.000000000000000000 : ℝ)))))))))))) ≤ (∏ i ∈ Finset.Ico 0 500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 500 1000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 1000 1500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 1500 2000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 2000 2500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 2500 3000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 3000 3500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 3500 4000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4000 4500, (1 - GG i)) * ((∏ i ∈ Finset.Ico 4500 5000, (1 - GG i)) * ((∏ i ∈ Finset.Ico 5000 5001, (1 - GG i)))))))))))) :=
    mul_le_mul (blk0) m1 (by norm_num) (le_trans (by norm_num) (blk0))
  exact le_trans (by norm_num) m0

set_option maxHeartbeats 800000 in
/-- LEAF. Paper page 25, display 40, lower bound for C0. -/
theorem c0_bound : 66 / 100 ≤ LeanLab.HeathBrownPuchta.Decomp130.C0 := by
  have hpt : ∀ n : ℕ, (1 - GG n) =
      (if n.Prime ∧ 2 < n then 1 - 1 / ((n : ℝ) - 1) ^ 2 else 1) := by
    intro n
    unfold GG
    split_ifs with h <;> ring
  have hC0 : LeanLab.HeathBrownPuchta.Decomp130.C0 = ∏' n : ℕ, (1 - GG n) := by
    rw [LeanLab.HeathBrownPuchta.Decomp130.C0]
    exact (tprod_congr hpt).symm
  have hsum : Summable (fun n : ℕ => -GG n) := summable_GG.neg
  have hmult : Multipliable (fun n : ℕ => 1 - GG n) := by
    have h := Real.multipliable_one_add_of_summable hsum
    simpa only [sub_eq_add_neg] using h
  rw [hC0]
  refine ge_of_tendsto hmult.tendsto_prod_tprod_nat ?_
  filter_upwards [Filter.eventually_ge_atTop 5001] with n hn
  have hsplit : ∏ i ∈ Finset.range n, (1 - GG i) =
      (∏ i ∈ Finset.range 5001, (1 - GG i)) * ∏ i ∈ Finset.Ico 5001 n, (1 - GG i) := by
    rw [Finset.range_eq_Ico (a := 5001), Finset.range_eq_Ico (a := n)]
    exact (Finset.prod_Ico_consecutive (fun i : ℕ => (1 - GG i : ℝ)) (by norm_num) hn).symm
  rw [hsplit]
  have h1 : (66017 / 100000 : ℝ) ≤ ∏ i ∈ Finset.range 5001, (1 - GG i) := fin_prod_ge
  have h2 : 1 - 1 / 4999 ≤ ∏ i ∈ Finset.Ico 5001 n, (1 - GG i) := by
    have hA := one_sub_sum_le_prod (Finset.Ico 5001 n)
    have hB := tail_sum_le 5000 (by norm_num) n
    have hC : (1 : ℝ) / ((5000 : ℝ) - 1) = 1 / 4999 := by norm_num
    linarith
  have h3 : (0 : ℝ) ≤ 1 - 1 / 4999 := by norm_num
  have h4 : (0 : ℝ) ≤ ∏ i ∈ Finset.range 5001, (1 - GG i) := le_trans (by norm_num) h1
  have h5 := mul_le_mul h1 h2 h3 h4
  nlinarith [h5]

/-- LEAF. Paper page 26, display 41, upper bound for C2 using Liu, Liu and Wang. -/
theorem c2_bound : LeanLab.HeathBrownPuchta.Lemma8Const.C2 ≤ 22141 / 10000 := by
  sorry

theorem constants_assembly : 66 / 100 ≤ LeanLab.HeathBrownPuchta.Decomp130.C0 ∧
    LeanLab.HeathBrownPuchta.Lemma8Const.C2 ≤ 22141 / 10000 :=
  ⟨c0_bound, c2_bound⟩

end LeanLab.HeathBrownPuchta.DecompJ417
