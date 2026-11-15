/-
P0069 Baker Harman Pintz 1997, Section 2, page 8, display 2.9: the large-divisor
mean square estimate on K = [x, x + H],
  Σ_{N ∈ K} (Σ_{d | N, d > P} 1/φ(d))² ≪ H ℒ^{-A-7},  P = ℒ^{2D}.
This file proves the printed bound 2.9 in raw form, for every interval length
H = x^h with 0 < h ≤ 1, with no reference to the 512 definitions, so that
Decomp512a can import it.

NOTE on faithfulness. The paper reaches 2.9 through the middle term
ℒ^{-4A+1} Σ_{j ∈ K} τ(j)² and then Σ_{j ∈ K} τ(j)² ≪ H ℒ³, which
it states without proof and which needs a short interval divisor moment that the
lab does not have. That middle term is not proved here; only the outer bound of
2.9 is. The proof here reaches the same printed bound 2.9 by a
different elementary path: split the divisors d of N at H. For P < d ≤ H expand the
square, swap the order of summation and count the multiples of the larger of two
divisors in K. For d > H use the pointwise divisor bound τ(n) ≪ n^ε together with
1/φ(d) ≪ d^{-3/4}. The price is the threshold D₀ = 2A + 14 in place of A + 7.

AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
import LeanLab.PerelliPintz1992.DivisorBound

namespace LeanLab.BHP1997.Route512
open Finset

/-- P0069 page 8 display 2.9, input: `d ≤ τ(d) φ(d)` from `Σ_{e | d} φ(e) = d`, hence
`1/φ(d) ≤ K d^{-3/4}` by the divisor bound with exponent `1/4`. -/
theorem one_div_totient_le512 :
    ∃ K : ℝ, 0 < K ∧ ∀ d : ℕ, 0 < d →
      1 / (Nat.totient d : ℝ) ≤ K * (d : ℝ) ^ (-(3 / 4) : ℝ) := by
  obtain ⟨K, hK, hKb⟩ :=
    LeanLab.PerelliPintz1992.Section6.divisors_card_le_rpow (1 / 4) (by norm_num)
  refine ⟨K, hK, fun d hd => ?_⟩
  have hφ : 0 < Nat.totient d := Nat.totient_pos.mpr hd
  have hφR : (0 : ℝ) < (Nat.totient d : ℝ) := by exact_mod_cast hφ
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h1 : d ≤ d.divisors.card * Nat.totient d := by
    calc d = ∑ e ∈ d.divisors, Nat.totient e := (Nat.sum_totient d).symm
      _ ≤ ∑ _e ∈ d.divisors, Nat.totient d := Finset.sum_le_sum (fun e he =>
          Nat.le_of_dvd hφ (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors he)))
      _ = d.divisors.card * Nat.totient d := by rw [Finset.sum_const, smul_eq_mul]
  have h2 : (d : ℝ) ≤ K * (d : ℝ) ^ (1 / 4 : ℝ) * (Nat.totient d : ℝ) := by
    have h1R : (d : ℝ) ≤ (d.divisors.card : ℝ) * (Nat.totient d : ℝ) := by exact_mod_cast h1
    exact h1R.trans (mul_le_mul_of_nonneg_right (hKb d hd.ne') hφR.le)
  have h3 : (d : ℝ) ^ (1 / 4 : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) = (d : ℝ) := by
    rw [← Real.rpow_add hdR]; norm_num
  have h4 : (d : ℝ) ^ (3 / 4 : ℝ) ≤ K * (Nat.totient d : ℝ) := by
    have hp : (0 : ℝ) < (d : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hdR _
    have h5 : (d : ℝ) ^ (1 / 4 : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤
        (d : ℝ) ^ (1 / 4 : ℝ) * (K * (Nat.totient d : ℝ)) := by
      rw [h3]
      calc (d : ℝ) ≤ K * (d : ℝ) ^ (1 / 4 : ℝ) * (Nat.totient d : ℝ) := h2
        _ = (d : ℝ) ^ (1 / 4 : ℝ) * (K * (Nat.totient d : ℝ)) := by ring
    exact le_of_mul_le_mul_left h5 hp
  have h6 : (d : ℝ) ^ (3 / 4 : ℝ) * (d : ℝ) ^ (-(3 / 4) : ℝ) = 1 := by
    rw [← Real.rpow_add hdR]; norm_num
  have hn : (0 : ℝ) ≤ (d : ℝ) ^ (-(3 / 4) : ℝ) := (Real.rpow_pos_of_pos hdR _).le
  rw [div_le_iff₀ hφR]
  calc (1 : ℝ) = (d : ℝ) ^ (3 / 4 : ℝ) * (d : ℝ) ^ (-(3 / 4) : ℝ) := h6.symm
    _ ≤ K * (Nat.totient d : ℝ) * (d : ℝ) ^ (-(3 / 4) : ℝ) :=
        mul_le_mul_of_nonneg_right h4 hn
    _ = K * (d : ℝ) ^ (-(3 / 4) : ℝ) * (Nat.totient d : ℝ) := by ring

/-- P0069 page 8 display 2.9, counting: a real interval `[u, v]` holds at most
`v - u + 1` integers. -/
private theorem card_Icc_le512 (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
    ((Finset.Icc ⌈u⌉₊ ⌊v⌋₊).card : ℝ) ≤ v - u + 1 := by
  rw [Nat.card_Icc]
  have h1 : ((⌊v⌋₊ : ℕ) : ℝ) ≤ v := Nat.floor_le (hu.trans huv)
  have h2 : u ≤ ((⌈u⌉₊ : ℕ) : ℝ) := Nat.le_ceil u
  by_cases hc : ⌈u⌉₊ ≤ ⌊v⌋₊ + 1
  · rw [Nat.cast_sub hc]; push_cast; linarith
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hc), Nat.cast_zero]; linarith

/-- P0069 page 8 display 2.9, counting: the interval K = [x, x + H] holds at most
`H / m + 1` multiples of `m`. -/
theorem card_multiples_le512 (x H : ℝ) (hx : 0 ≤ x) (hH : 0 ≤ H) (m : ℕ) (hm : 0 < m) :
    (((Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N => m ∣ N)).card : ℝ) ≤ H / m + 1 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hinj : ((Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N => m ∣ N)).card ≤
      (Finset.Icc ⌈x / m⌉₊ ⌊(x + H) / m⌋₊).card := by
    apply Finset.card_le_card_of_injOn (fun N => N / m)
    · intro N hN
      have hN' := Finset.mem_coe.mp hN
      rw [Finset.mem_filter, Finset.mem_Icc] at hN'
      obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hN'
      have hk : m * k / m = k := Nat.mul_div_cancel_left k hm
      have h1' : x ≤ ((m * k : ℕ) : ℝ) := Nat.ceil_le.mp h1
      have h2' : ((m * k : ℕ) : ℝ) ≤ x + H := (Nat.le_floor_iff (add_nonneg hx hH)).mp h2
      push_cast at h1' h2'
      show m * k / m ∈ Finset.Icc ⌈x / m⌉₊ ⌊(x + H) / m⌋₊
      rw [hk, Finset.mem_Icc]
      constructor
      · rw [Nat.ceil_le, div_le_iff₀ hmR]; linarith
      · rw [Nat.le_floor_iff (div_nonneg (add_nonneg hx hH) hmR.le), le_div_iff₀ hmR]
        linarith
    · intro N1 hN1 N2 hN2 heq
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hN1)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hN2)).2
      exact (Nat.div_left_inj h1 h2).mp heq
  calc (((Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N => m ∣ N)).card : ℝ)
      ≤ ((Finset.Icc ⌈x / m⌉₊ ⌊(x + H) / m⌋₊).card : ℝ) := by exact_mod_cast hinj
    _ ≤ (x + H) / m - x / m + 1 :=
        card_Icc_le512 _ _ (div_nonneg hx hmR.le)
          (div_le_div_of_nonneg_right (by linarith) hmR.le)
    _ = H / m + 1 := by ring

/-- P0069 page 8 display 2.9, the swapped sum: the terms attached to a pair of divisors
`d1`, `d2` are supported on the multiples of `d2`. -/
private theorem pair_sum_le512 (I : Finset ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (d1 d2 : ℕ) :
    ∑ N ∈ I, (if d1 ∣ N then a else 0) * (if d2 ∣ N then b else 0) ≤
      a * b * ((I.filter (fun N => d2 ∣ N)).card : ℝ) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  calc ∑ N ∈ I, (if d1 ∣ N then a else 0) * (if d2 ∣ N then b else 0)
      ≤ ∑ N ∈ I, (if d2 ∣ N then a * b else 0) := by
        apply Finset.sum_le_sum
        intro N _
        by_cases h1 : d1 ∣ N <;> by_cases h2 : d2 ∣ N <;> simp [h1, h2, hab]
    _ = a * b * ((I.filter (fun N => d2 ∣ N)).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- P0069 page 8 display 2.9, divisors up to H: expand the square of the divisor sum,
swap with the sum over K and count the multiples of the larger divisor. Here
`f` stands for `1/φ` and `S` for the divisors in `(P, H]`. -/
theorem small_part512 (x H : ℝ) (hx : 0 ≤ x) (hH : 1 ≤ H) (S : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ d, 0 ≤ f d) (hS : ∀ d ∈ S, 0 < d ∧ (d : ℝ) ≤ H) :
    ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊, (∑ d ∈ S, if d ∣ N then f d else 0) ^ 2 ≤
      2 * H * (∑ d ∈ S, f d * (d : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 := by
  have hH0 : 0 ≤ H := by linarith
  have hpair : ∀ d1 ∈ S, ∀ d2 ∈ S,
      ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊,
        (if d1 ∣ N then f d1 else 0) * (if d2 ∣ N then f d2 else 0) ≤
      2 * H * ((f d1 * (d1 : ℝ) ^ (-(1 / 2) : ℝ)) * (f d2 * (d2 : ℝ) ^ (-(1 / 2) : ℝ))) := by
    intro d1 h1 d2 h2
    obtain ⟨p1, q1⟩ := hS d1 h1
    obtain ⟨p2, q2⟩ := hS d2 h2
    have p1R : (0 : ℝ) < d1 := by exact_mod_cast p1
    have p2R : (0 : ℝ) < d2 := by exact_mod_cast p2
    have hff : 0 ≤ f d1 * f d2 := mul_nonneg (hf d1) (hf d2)
    have key : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ H → (d1 : ℝ) ≤ m → (d2 : ℝ) ≤ m →
        f d1 * f d2 *
          (((Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N => m ∣ N)).card : ℝ) ≤
        2 * H * ((f d1 * (d1 : ℝ) ^ (-(1 / 2) : ℝ)) *
          (f d2 * (d2 : ℝ) ^ (-(1 / 2) : ℝ))) := by
      intro m hm hmH hd1 hd2
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have hc := card_multiples_le512 x H hx hH0 m hm
      have hc2 : (((Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N => m ∣ N)).card : ℝ) ≤
          2 * H * (m : ℝ)⁻¹ := by
        have hge : (1 : ℝ) ≤ H / m := by rw [le_div_iff₀ hmR]; linarith
        calc (((Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N => m ∣ N)).card : ℝ)
            ≤ H / m + 1 := hc
          _ ≤ 2 * (H / m) := by linarith
          _ = 2 * H * (m : ℝ)⁻¹ := by ring
      have hinv : (m : ℝ)⁻¹ ≤ (d1 : ℝ) ^ (-(1 / 2) : ℝ) * (d2 : ℝ) ^ (-(1 / 2) : ℝ) := by
        have e : (m : ℝ)⁻¹ = (m : ℝ) ^ (-(1 / 2) : ℝ) * (m : ℝ) ^ (-(1 / 2) : ℝ) := by
          rw [← Real.rpow_add hmR, ← Real.rpow_neg_one]; norm_num
        rw [e]
        have a1 : (m : ℝ) ^ (-(1 / 2) : ℝ) ≤ (d1 : ℝ) ^ (-(1 / 2) : ℝ) :=
          (Real.rpow_le_rpow_iff_of_neg hmR p1R (by norm_num)).mpr hd1
        have a2 : (m : ℝ) ^ (-(1 / 2) : ℝ) ≤ (d2 : ℝ) ^ (-(1 / 2) : ℝ) :=
          (Real.rpow_le_rpow_iff_of_neg hmR p2R (by norm_num)).mpr hd2
        exact mul_le_mul a1 a2 (Real.rpow_nonneg hmR.le _) (Real.rpow_nonneg p1R.le _)
      calc f d1 * f d2 *
            (((Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N => m ∣ N)).card : ℝ)
          ≤ f d1 * f d2 * (2 * H * (m : ℝ)⁻¹) := mul_le_mul_of_nonneg_left hc2 hff
        _ ≤ f d1 * f d2 *
            (2 * H * ((d1 : ℝ) ^ (-(1 / 2) : ℝ) * (d2 : ℝ) ^ (-(1 / 2) : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hinv (by linarith)) hff
        _ = 2 * H * ((f d1 * (d1 : ℝ) ^ (-(1 / 2) : ℝ)) *
            (f d2 * (d2 : ℝ) ^ (-(1 / 2) : ℝ))) := by ring
    rcases le_total d1 d2 with h | h
    · exact (pair_sum_le512 _ _ _ (hf d1) (hf d2) d1 d2).trans
        (key d2 p2 q2 (by exact_mod_cast h) le_rfl)
    · have hsw := pair_sum_le512 (Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊) _ _ (hf d2) (hf d1) d2 d1
      calc ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊,
            (if d1 ∣ N then f d1 else 0) * (if d2 ∣ N then f d2 else 0)
          = ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊,
            (if d2 ∣ N then f d2 else 0) * (if d1 ∣ N then f d1 else 0) :=
            Finset.sum_congr rfl (fun N _ => mul_comm _ _)
        _ ≤ f d2 * f d1 *
            (((Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N => d1 ∣ N)).card : ℝ) := hsw
        _ = f d1 * f d2 *
            (((Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N => d1 ∣ N)).card : ℝ) := by ring
        _ ≤ 2 * H * ((f d1 * (d1 : ℝ) ^ (-(1 / 2) : ℝ)) *
            (f d2 * (d2 : ℝ) ^ (-(1 / 2) : ℝ))) :=
            key d1 p1 q1 le_rfl (by exact_mod_cast h)
  calc ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊, (∑ d ∈ S, if d ∣ N then f d else 0) ^ 2
      = ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊, ∑ d1 ∈ S, ∑ d2 ∈ S,
          (if d1 ∣ N then f d1 else 0) * (if d2 ∣ N then f d2 else 0) := by
        apply Finset.sum_congr rfl
        intro N _
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ d1 ∈ S, ∑ d2 ∈ S, ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊,
          (if d1 ∣ N then f d1 else 0) * (if d2 ∣ N then f d2 else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d1 _
        rw [Finset.sum_comm]
    _ ≤ ∑ d1 ∈ S, ∑ d2 ∈ S, 2 * H * ((f d1 * (d1 : ℝ) ^ (-(1 / 2) : ℝ)) *
          (f d2 * (d2 : ℝ) ^ (-(1 / 2) : ℝ))) :=
        Finset.sum_le_sum (fun d1 h1 => Finset.sum_le_sum (fun d2 h2 => hpair d1 h1 d2 h2))
    _ = 2 * H * (∑ d ∈ S, f d * (d : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d1 _
        rw [Finset.mul_sum]

/-- P0069 page 8 display 2.9, the tail of the convergent series: over any finite set of
integers above `P` the sum of `d^{-5/4}` is at most `W P^{-1/8}`, with `W` the sum of
the series `Σ n^{-9/8}`. -/
theorem tail_sum_le512 :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ (S : Finset ℕ) (P : ℝ), 0 < P → (∀ d ∈ S, P < (d : ℝ)) →
      ∑ d ∈ S, (d : ℝ) ^ (-(5 / 4) : ℝ) ≤ W * P ^ (-(1 / 8) : ℝ) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(9 / 8) : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  refine ⟨∑' n : ℕ, (n : ℝ) ^ (-(9 / 8) : ℝ),
    tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _), ?_⟩
  intro S P hP hS
  calc ∑ d ∈ S, (d : ℝ) ^ (-(5 / 4) : ℝ)
      ≤ ∑ d ∈ S, (d : ℝ) ^ (-(9 / 8) : ℝ) * P ^ (-(1 / 8) : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd0 : (0 : ℝ) < d := hP.trans (hS d hd)
        have e : (d : ℝ) ^ (-(5 / 4) : ℝ) =
            (d : ℝ) ^ (-(9 / 8) : ℝ) * (d : ℝ) ^ (-(1 / 8) : ℝ) := by
          rw [← Real.rpow_add hd0]; norm_num
        rw [e]
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hd0.le _)
        exact (Real.rpow_le_rpow_iff_of_neg hd0 hP (by norm_num)).mpr (hS d hd).le
    _ = (∑ d ∈ S, (d : ℝ) ^ (-(9 / 8) : ℝ)) * P ^ (-(1 / 8) : ℝ) := by
        rw [Finset.sum_mul]
    _ ≤ (∑' n : ℕ, (n : ℝ) ^ (-(9 / 8) : ℝ)) * P ^ (-(1 / 8) : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hP.le _)
        exact hs.sum_le_tsum S (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- P0069 page 8 display 2.9, raw form: for every `0 < h ≤ 1` and every `A > 0`, with
`D₀ = 2A + 14`, for `D ≥ D₀` and `x` large,
`Σ_{N ∈ [x, x + x^h], N even} (Σ_{d | N, d > ℒ^{2D}} 1/φ(d))² ≤ C x^h ℒ^{-A-7}`.
The proof splits the divisors at `x^h`, see the file header. -/
theorem large_divisor_moment_raw512 (h : ℝ) (h0 : 0 < h) (h1 : h ≤ 1) :
    ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ∑ N ∈ (Finset.Icc ⌈x⌉₊ ⌊x + x ^ h⌋₊).filter (fun N => Even N),
        (∑ d ∈ N.divisors.filter (fun d : ℕ => Real.log x ^ (2 * D) < (d : ℝ)),
          1 / (Nat.totient d : ℝ)) ^ 2 ≤ C * x ^ h * Real.log x ^ (-A - 7) := by
  intro A hA
  obtain ⟨K, hK, hKb⟩ := one_div_totient_le512
  obtain ⟨K', hK', hK'b⟩ :=
    LeanLab.PerelliPintz1992.Section6.divisors_card_le_rpow (h / 8) (by positivity)
  obtain ⟨W, hW, hWb⟩ := tail_sum_le512
  refine ⟨2 * A + 14, fun D hD => ?_⟩
  have hlit := (isLittleO_log_rpow_rpow_atTop (A + 7)
    (show (0 : ℝ) < 5 * h / 4 by positivity)).bound (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hlit
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = 4 * (K * W) ^ 2 + 16 * (K * K') ^ 2 := ⟨_, rfl⟩
  refine ⟨max (max X0 (Real.exp 1)) C0, fun x hx => ?_⟩
  have hxX0 : X0 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxe : Real.exp 1 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hxe
  have hL0 : 0 < Real.log x := by linarith
  have hlog : Real.log x ^ (A + 7) ≤ x ^ (5 * h / 4) := by
    have hb := hX0 x hxX0
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at hb
    exact hb
  have hLA : Real.log x ^ (-A - 7) = (Real.log x ^ (A + 7))⁻¹ := by
    rw [← Real.rpow_neg hL0.le]; congr 1; ring
  have hLApos : 0 < Real.log x ^ (-A - 7) := Real.rpow_pos_of_pos hL0 _
  have hxpow : x ^ (-(5 * h / 4)) ≤ Real.log x ^ (-A - 7) := by
    rw [hLA, Real.rpow_neg hx0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hL0 _) hlog
  have hH1 : 1 ≤ x ^ h := Real.one_le_rpow hx1 h0.le
  have hHx : x ^ h ≤ x := by
    calc x ^ h ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 h1
      _ = x := Real.rpow_one x
  have hB : (x ^ (h / 8) * (x ^ h) ^ (-(3 / 4) : ℝ)) ^ 2 = x ^ (-(5 * h / 4)) := by
    rw [← Real.rpow_mul hx0.le, ← Real.rpow_add hx0, ← Real.rpow_natCast,
      ← Real.rpow_mul hx0.le]
    congr 1; push_cast; ring
  have e1 : ((Real.log x ^ (2 * D)) ^ (-(1 / 8) : ℝ)) ^ 2 ≤ Real.log x ^ (-A - 7) := by
    rw [← Real.rpow_mul hL0.le, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    push_cast; linarith
  have hP0 : 0 < Real.log x ^ (2 * D) := Real.rpow_pos_of_pos hL0 _
  have h2 : (2 : ℝ) ^ (h / 8) ≤ 2 := by
    calc (2 : ℝ) ^ (h / 8) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  -- from here on the three quantities are opaque
  generalize hLdef : Real.log x = L at *
  generalize hHdef : x ^ h = H at *
  generalize hPdef : L ^ (2 * D) = P at *
  have hH0 : 0 < H := by linarith
  have hf0 : ∀ d : ℕ, (0 : ℝ) ≤ 1 / (Nat.totient d : ℝ) := fun d => by positivity
  obtain ⟨S, hSdef⟩ : ∃ S : Finset ℕ,
      S = (Finset.Icc 1 ⌊H⌋₊).filter (fun d : ℕ => P < (d : ℝ)) := ⟨_, rfl⟩
  have hSmem : ∀ d : ℕ, d ∈ S ↔ (1 ≤ d ∧ (d : ℝ) ≤ H) ∧ P < (d : ℝ) := by
    intro d
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc, Nat.le_floor_iff hH0.le]
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ,
      B = 2 * K' * x ^ (h / 8) * (K * H ^ (-(3 / 4) : ℝ)) := ⟨_, rfl⟩
  have hxh8 : 0 < x ^ (h / 8) := Real.rpow_pos_of_pos hx0 _
  have hH34 : 0 < H ^ (-(3 / 4) : ℝ) := Real.rpow_pos_of_pos hH0 _
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have e2 : B ^ 2 ≤ 4 * (K * K') ^ 2 * L ^ (-A - 7) := by
    have e3 : B ^ 2 = 4 * (K * K') ^ 2 * (x ^ (h / 8) * H ^ (-(3 / 4) : ℝ)) ^ 2 := by
      rw [hBdef]; ring
    rw [e3, hB]
    exact mul_le_mul_of_nonneg_left hxpow (by positivity)
  -- pointwise split of the divisor sum at H
  have hpt : ∀ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊,
      (∑ d ∈ N.divisors.filter (fun d : ℕ => P < (d : ℝ)), 1 / (Nat.totient d : ℝ)) ^ 2 ≤
        2 * (∑ d ∈ S, if d ∣ N then 1 / (Nat.totient d : ℝ) else 0) ^ 2 + 2 * B ^ 2 := by
    intro N hN
    rw [Finset.mem_Icc] at hN
    have hxN : x ≤ (N : ℝ) := Nat.ceil_le.mp hN.1
    have hNR : (0 : ℝ) < (N : ℝ) := by linarith
    have hNpos : 0 < N := by exact_mod_cast hNR
    have hNle : (N : ℝ) ≤ 2 * x := by
      have hNH : (N : ℝ) ≤ x + H := (Nat.le_floor_iff (by linarith)).mp hN.2
      linarith
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (N.divisors.filter (fun d : ℕ => P < (d : ℝ))) (fun d : ℕ => (d : ℝ) ≤ H)
      (fun d => 1 / (Nat.totient d : ℝ))
    have hA1 : ∑ d ∈ (N.divisors.filter (fun d : ℕ => P < (d : ℝ))).filter
        (fun d : ℕ => (d : ℝ) ≤ H), 1 / (Nat.totient d : ℝ) ≤
        ∑ d ∈ S, if d ∣ N then 1 / (Nat.totient d : ℝ) else 0 := by
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        rw [Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors] at hd
        obtain ⟨⟨⟨hdN, _⟩, hPd⟩, hdH⟩ := hd
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdN hNpos
        rw [Finset.mem_filter, hSmem]
        exact ⟨⟨⟨hdpos, hdH⟩, hPd⟩, hdN⟩
      · intro d _ _; exact hf0 d
    have hA2 : ∑ d ∈ (N.divisors.filter (fun d : ℕ => P < (d : ℝ))).filter
        (fun d : ℕ => ¬ (d : ℝ) ≤ H), 1 / (Nat.totient d : ℝ) ≤ B := by
      calc ∑ d ∈ (N.divisors.filter (fun d : ℕ => P < (d : ℝ))).filter
            (fun d : ℕ => ¬ (d : ℝ) ≤ H), 1 / (Nat.totient d : ℝ)
          ≤ ∑ _d ∈ (N.divisors.filter (fun d : ℕ => P < (d : ℝ))).filter
            (fun d : ℕ => ¬ (d : ℝ) ≤ H), K * H ^ (-(3 / 4) : ℝ) := by
            apply Finset.sum_le_sum
            intro d hd
            rw [Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors, not_le] at hd
            obtain ⟨⟨⟨hdN, _⟩, _⟩, hdH⟩ := hd
            have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdN hNpos
            have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
            refine (hKb d hdpos).trans (mul_le_mul_of_nonneg_left ?_ hK.le)
            exact (Real.rpow_le_rpow_iff_of_neg hdR hH0 (by norm_num)).mpr hdH.le
        _ = (((N.divisors.filter (fun d : ℕ => P < (d : ℝ))).filter
            (fun d : ℕ => ¬ (d : ℝ) ≤ H)).card : ℝ) * (K * H ^ (-(3 / 4) : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * K' * x ^ (h / 8)) * (K * H ^ (-(3 / 4) : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            calc (((N.divisors.filter (fun d : ℕ => P < (d : ℝ))).filter
                  (fun d : ℕ => ¬ (d : ℝ) ≤ H)).card : ℝ)
                ≤ (N.divisors.card : ℝ) := by
                  exact_mod_cast Finset.card_le_card
                    ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
              _ ≤ K' * (N : ℝ) ^ (h / 8) := hK'b N hNpos.ne'
              _ ≤ K' * (2 * x) ^ (h / 8) :=
                  mul_le_mul_of_nonneg_left
                    (Real.rpow_le_rpow hNR.le hNle (by positivity)) hK'.le
              _ = K' * ((2 : ℝ) ^ (h / 8) * x ^ (h / 8)) := by
                  rw [Real.mul_rpow (by norm_num) hx0.le]
              _ ≤ K' * (2 * x ^ (h / 8)) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right h2 hxh8.le) hK'.le
              _ = 2 * K' * x ^ (h / 8) := by ring
        _ = B := by rw [hBdef]
    have hT0 : 0 ≤ ∑ d ∈ N.divisors.filter (fun d : ℕ => P < (d : ℝ)),
        1 / (Nat.totient d : ℝ) := Finset.sum_nonneg (fun d _ => hf0 d)
    have hle : ∑ d ∈ N.divisors.filter (fun d : ℕ => P < (d : ℝ)),
        1 / (Nat.totient d : ℝ) ≤
        (∑ d ∈ S, if d ∣ N then 1 / (Nat.totient d : ℝ) else 0) + B := by
      rw [← hsplit]; exact add_le_add hA1 hA2
    calc (∑ d ∈ N.divisors.filter (fun d : ℕ => P < (d : ℝ)),
          1 / (Nat.totient d : ℝ)) ^ 2
        ≤ ((∑ d ∈ S, if d ∣ N then 1 / (Nat.totient d : ℝ) else 0) + B) ^ 2 :=
          pow_le_pow_left₀ hT0 hle 2
      _ ≤ 2 * (∑ d ∈ S, if d ∣ N then 1 / (Nat.totient d : ℝ) else 0) ^ 2 + 2 * B ^ 2 := by
          nlinarith [sq_nonneg ((∑ d ∈ S, if d ∣ N then 1 / (Nat.totient d : ℝ) else 0) - B)]
  -- the divisors up to H
  have hsmall := small_part512 x H hx0.le hH1 S (fun d => 1 / (Nat.totient d : ℝ)) hf0
    (fun d hd => ⟨((hSmem d).mp hd).1.1, ((hSmem d).mp hd).1.2⟩)
  beta_reduce at hsmall
  have hSP : ∀ d ∈ S, P < (d : ℝ) := fun d hd => ((hSmem d).mp hd).2
  have hinner : ∑ d ∈ S, 1 / (Nat.totient d : ℝ) * (d : ℝ) ^ (-(1 / 2) : ℝ) ≤
      K * (W * P ^ (-(1 / 8) : ℝ)) := by
    calc ∑ d ∈ S, 1 / (Nat.totient d : ℝ) * (d : ℝ) ^ (-(1 / 2) : ℝ)
        ≤ ∑ d ∈ S, K * (d : ℝ) ^ (-(5 / 4) : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          have hdR : (0 : ℝ) < d := hP0.trans (hSP d hd)
          have hdpos : 0 < d := by exact_mod_cast hdR
          have e : (d : ℝ) ^ (-(5 / 4) : ℝ) =
              (d : ℝ) ^ (-(3 / 4) : ℝ) * (d : ℝ) ^ (-(1 / 2) : ℝ) := by
            rw [← Real.rpow_add hdR]; norm_num
          rw [e, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (hKb d hdpos) (Real.rpow_nonneg hdR.le _)
      _ = K * ∑ d ∈ S, (d : ℝ) ^ (-(5 / 4) : ℝ) := by rw [Finset.mul_sum]
      _ ≤ K * (W * P ^ (-(1 / 8) : ℝ)) :=
          mul_le_mul_of_nonneg_left (hWb S P hP0 hSP) hK.le
  have hcard : ((Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).card : ℝ) ≤ 2 * H := by
    have hc := card_Icc_le512 x (x + H) hx0.le (by linarith)
    linarith
  have hLm : 0 < L ^ (-A - 7) := hLApos
  have hmain : ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊,
      (∑ d ∈ N.divisors.filter (fun d : ℕ => P < (d : ℝ)), 1 / (Nat.totient d : ℝ)) ^ 2 ≤
        C0 * H * L ^ (-A - 7) := by
    calc ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊,
          (∑ d ∈ N.divisors.filter (fun d : ℕ => P < (d : ℝ)),
            1 / (Nat.totient d : ℝ)) ^ 2
        ≤ ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊,
          (2 * (∑ d ∈ S, if d ∣ N then 1 / (Nat.totient d : ℝ) else 0) ^ 2 + 2 * B ^ 2) :=
          Finset.sum_le_sum hpt
      _ = 2 * ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊,
            (∑ d ∈ S, if d ∣ N then 1 / (Nat.totient d : ℝ) else 0) ^ 2 +
          ((Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).card : ℝ) * (2 * B ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (2 * H * (K * (W * P ^ (-(1 / 8) : ℝ))) ^ 2) + (2 * H) * (2 * B ^ 2) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ (by norm_num)
            refine hsmall.trans ?_
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            exact pow_le_pow_left₀ (Finset.sum_nonneg (fun d _ =>
              mul_nonneg (hf0 d) (Real.rpow_nonneg (Nat.cast_nonneg d) _))) hinner 2
          · exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 4 * (K * W) ^ 2 * H * (P ^ (-(1 / 8) : ℝ)) ^ 2 + 4 * H * B ^ 2 := by ring
      _ ≤ 4 * (K * W) ^ 2 * H * L ^ (-A - 7) +
          4 * H * (4 * (K * K') ^ 2 * L ^ (-A - 7)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left e1 (by positivity)
          · exact mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = C0 * H * L ^ (-A - 7) := by rw [hC0]; ring
  calc ∑ N ∈ (Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N => Even N),
        (∑ d ∈ N.divisors.filter (fun d : ℕ => P < (d : ℝ)), 1 / (Nat.totient d : ℝ)) ^ 2
      ≤ ∑ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊,
        (∑ d ∈ N.divisors.filter (fun d : ℕ => P < (d : ℝ)), 1 / (Nat.totient d : ℝ)) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun N _ _ => sq_nonneg _)
    _ ≤ C0 * H * L ^ (-A - 7) := hmain
    _ ≤ max (max X0 (Real.exp 1)) C0 * H * L ^ (-A - 7) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hH0.le) hLm.le

end LeanLab.BHP1997.Route512
