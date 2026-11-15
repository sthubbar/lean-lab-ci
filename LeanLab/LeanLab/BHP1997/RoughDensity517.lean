/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character.
The paper proves 5.17 with the words "a straightforward consequence of the prime number
theorem". For the rough cofactor `n3` or `n5` of display 5.15 that consequence is an induction
on the number of prime factors through the finite Buchstab identity, page 27 identity 4.14.
This file holds the finite, combinatorial half: `rough_sum_decomp`, the identity summed over an
interval by the least prime factor, with the reindexing and splitting lemmas it needs.
Nothing is left open in this file.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Rough308
import LeanLab.ChenDoubleSieve.I2Range

namespace LeanLab.BHP1997.LowerShortC165
open Classical
open scoped BigOperators
open LeanLab.BHP1997.Task308 (roughIndicator)

/-- P0069 page 51, display 5.17, with page 27 identity 4.14: an integer `n ≥ 2` with no prime
factor below `z` is counted exactly once as `n = p * m` with `p ≥ z` its least prime factor and
`m` free of prime factors below `p`. This is the Buchstab identity that the consequence of the
prime number theorem is iterated through. -/
theorem rough_minfac_sum {z b n : ℕ} (hn : 2 ≤ n) (hnb : n ≤ b) :
    roughIndicator n z = ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
      if p ∣ n then roughIndicator (n / p) p else 0 := by
  have h1 : ∀ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
      (if p ∣ n then roughIndicator (n / p) p else 0) = if p = n.minFac then (1 : ℝ) else 0 := by
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2.1
    by_cases hd : p ∣ n
    · rw [ite_eq_left hd, Task308.rough_quotient_at_prime hpp hd]
    · rw [ite_eq_right hd, ite_eq_right]
      rintro rfl
      exact hd (Nat.minFac_dvd n)
  rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq']
  have hn1 : n ≠ 1 := by omega
  have hmp := Nat.minFac_prime hn1
  have hle := Nat.minFac_le (by omega : 0 < n)
  have h2 : 1 ≤ n.minFac ∧ n.minFac ≤ b := ⟨hmp.one_le, hle.trans hnb⟩
  simp only [roughIndicator, hn1, false_or, Finset.mem_filter, Finset.mem_Icc, hmp, true_and, h2]

/-- P0069 page 51, display 5.17: reindexing of the multiples of `d` in `(L, U]` by the cofactor
in `(L / d, U / d]`, real valued form of `Rough514.sum_dvd_reindex`. -/
theorem sum_dvd_reindex_real {d : ℕ} (hd : 1 ≤ d) (L U : ℕ) (g : ℕ → ℝ) :
    ∑ m ∈ Finset.Ioc L U, (if d ∣ m then g (m / d) else 0) =
      ∑ n ∈ Finset.Ioc (L / d) (U / d), g n := by
  have hd0 : 0 < d := hd
  have hinj : ∀ x ∈ Finset.Ioc (L / d) (U / d), ∀ y ∈ Finset.Ioc (L / d) (U / d),
      d * x = d * y → x = y := fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hd0 h
  have h1 : ∑ n ∈ Finset.Ioc (L / d) (U / d), g n =
      ∑ m ∈ (Finset.Ioc (L / d) (U / d)).image (fun n => d * n),
        (if d ∣ m then g (m / d) else 0) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [Nat.mul_div_cancel_left _ hd0]
  rw [h1]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro m hm
    rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨(Nat.div_lt_iff_lt_mul hd0).mp hn.1 |>.trans_eq (Nat.mul_comm n d),
      (Nat.mul_comm d n).trans_le ((Nat.le_div_iff_mul_le hd0).mp hn.2)⟩
  · intro m hm hnot
    by_cases hdm : d ∣ m
    · exfalso
      apply hnot
      rcases hdm with ⟨n, rfl⟩
      rw [Finset.mem_Ioc] at hm
      refine Finset.mem_image.mpr ⟨n, ?_, rfl⟩
      rw [Finset.mem_Ioc]
      exact ⟨(Nat.div_lt_iff_lt_mul hd0).mpr (hm.1.trans_eq (Nat.mul_comm d n)),
        (Nat.le_div_iff_mul_le hd0).mpr ((Nat.mul_comm n d).trans_le hm.2)⟩
    · simp [hdm]

/-- P0069 page 51, display 5.17, with page 27 identity 4.14 summed over an interval: the
integers of `(a, b]` free of prime factors below `z` are the products `p * m` with `p ≥ z`
prime and `m` in `(a / p, b / p]` free of prime factors below `p`. -/
theorem rough_sum_decomp (z a b : ℕ) (ha : 1 ≤ a) :
    ∑ n ∈ Finset.Ioc a b, roughIndicator n z =
      ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
        ∑ m ∈ Finset.Ioc (a / p) (b / p), roughIndicator m p := by
  rw [Finset.sum_congr rfl (fun n hn => rough_minfac_sum (z := z) (b := b)
    (by have := (Finset.mem_Ioc.mp hn).1; omega) (Finset.mem_Ioc.mp hn).2), Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  exact sum_dvd_reindex_real (Finset.mem_filter.mp hp).2.1.one_le a b (fun m => roughIndicator m p)

/-- P0069 page 51, display 5.17: in the cofactor range `(a / p, b / p]` the cofactor `1`, which
is the case that `p` itself is the integer counted, is split from the cofactors above `1`. -/
theorem cofactor_one_split {p a b : ℕ} (hp : 2 ≤ p) (hpb : p ≤ b) (f : ℕ → ℝ) :
    ∑ m ∈ Finset.Ioc (a / p) (b / p), f m =
      (if a < p then f 1 else 0) + ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p), f m := by
  have hb1 : 1 ≤ b / p := (Nat.one_le_div_iff (by omega)).mpr hpb
  by_cases h : a < p
  · rw [ite_eq_left h, Nat.div_eq_of_lt h, Nat.zero_max,
      ← Finset.sum_Ioc_consecutive f (Nat.zero_le 1) hb1]
    simp
  · rw [ite_eq_right h, zero_add, max_eq_left ((Nat.one_le_div_iff (by omega)).mpr (by omega))]

end LeanLab.BHP1997.LowerShortC165
