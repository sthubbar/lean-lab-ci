import Mathlib

/-!
The elementary square conductor count in Pintz 2021 author PDF page 17 display 5.15.
Source: https://real.mtak.hu/124681/1/Cikk2020Rivista.pdf
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.SquareDivisibility428

open Real Finset

/-- The natural numbers whose K weighted squares are divisible by q are exactly
the multiples of one positive modulus d, with q at most K d squared.
Source: Pintz 2021 author PDF page 17 displays 5.14 and 5.15, auxiliary arithmetic. -/
theorem exists_square_divisor_modulus (q K : ℕ) (hq : 0 < q) (hK : 0 < K) :
    ∃ d : ℕ, 0 < d ∧ q ≤ K * d ^ 2 ∧ ∀ m : ℕ, q ∣ K * m ^ 2 ↔ d ∣ m := by
  classical
  have hex : ∃ d : ℕ, 0 < d ∧ q ∣ K * d ^ 2 := by
    refine ⟨q, hq, ?_⟩
    exact dvd_mul_of_dvd_right (dvd_pow_self q (by norm_num : 2 ≠ 0)) K
  let d := Nat.find hex
  have hd : 0 < d := (Nat.find_spec hex).1
  have hqd : q ∣ K * d ^ 2 := (Nat.find_spec hex).2
  refine ⟨d, hd, Nat.le_of_dvd (by positivity) hqd, fun m => ?_⟩
  constructor
  · intro hm
    have hg : q ∣ K * Nat.gcd d m ^ 2 := by
      rw [← Nat.pow_gcd_pow, ← Nat.gcd_mul_left]
      exact Nat.dvd_gcd hqd hm
    have hmin : d ≤ Nat.gcd d m :=
      Nat.find_min' hex ⟨Nat.gcd_pos_of_pos_left m hd, hg⟩
    have he : Nat.gcd d m = d :=
      le_antisymm (Nat.gcd_le_left m hd) hmin
    exact Nat.gcd_eq_left_iff_dvd.mp he
  · rintro ⟨t, rfl⟩
    convert dvd_mul_of_dvd_left hqd (t ^ 2) using 1 <;> ring

/-- The number of positive m at most N with q dividing K m squared is
at most square root K times N divided by square root q.
Source: Pintz 2021 author PDF page 17 display 5.15, with an explicit constant. -/
theorem count_square_divisibility_le (q K N : ℕ) (hq : 0 < q) (hK : 0 < K) :
    (((Finset.Ioc 0 N).filter (fun m : ℕ => q ∣ K * m ^ 2)).card : ℝ) ≤
      Real.sqrt K * N / Real.sqrt q := by
  obtain ⟨d, hd, hqd, hiff⟩ := exists_square_divisor_modulus q K hq hK
  have he : (Finset.Ioc 0 N).filter (fun m : ℕ => q ∣ K * m ^ 2) =
      (Finset.Ioc 0 N).filter (fun m : ℕ => d ∣ m) := by
    ext m
    simp only [mem_filter, hiff]
  rw [he, Nat.Ioc_filter_dvd_card_eq_div]
  have hqr : (q : ℝ) ≤ K * (d : ℝ) ^ 2 := by exact_mod_cast hqd
  have hs : Real.sqrt (q : ℝ) ≤ Real.sqrt K * d := by
    calc
      _ ≤ Real.sqrt ((K : ℝ) * (d : ℝ) ^ 2) := Real.sqrt_le_sqrt hqr
      _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg K), Real.sqrt_sq (Nat.cast_nonneg d)]
  calc
    ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
    _ ≤ _ := by
      rw [div_le_div_iff₀ (by exact_mod_cast hd) (Real.sqrt_pos.mpr (by exact_mod_cast hq))]
      have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) N)
      nlinarith only [hm]

/-- A lower bound P for the conductor gives the N over square root P
bound used in the large conductor case.
Source: Pintz 2021 author PDF page 17 display 5.15. -/
theorem count_square_divisibility_le_of_ge (q K N : ℕ) (hq : 0 < q) (hK : 0 < K)
    (P : ℝ) (hP : 0 < P) (hPq : P ≤ q) :
    (((Finset.Ioc 0 N).filter (fun m : ℕ => q ∣ K * m ^ 2)).card : ℝ) ≤
      Real.sqrt K * N / Real.sqrt P := by
  exact (count_square_divisibility_le q K N hq hK).trans
    (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hP) (Real.sqrt_le_sqrt hPq))

end LeanLab.ExceptionalSet.SquareDivisibility428
