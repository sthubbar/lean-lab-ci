/-
ROUTE BURST session 9, LZPowersOfTwo table step: Lemma 1 of P0079 for k = 1.
Paper: P0079 A. Languasco and A. Zaccagnini, "On a Diophantine problem with two primes and
s powers of two", arXiv 0811.3663v2, 2 Apr 2009, page 5, Lemma 1 and display (22).
Cited source: A. Khalfalah and J. Pintz, "On the representation of Goldbach numbers by a
bounded number of powers of two", Elementare und analytische Zahlentheorie, Schr. Wiss. Ges.
Goethe Univ. Frankfurt 20, Steiner 2006, pages 129 to 142, Theorem 2. No copy was reachable.
AI wrote this Lean code. Binary Goldbach is OPEN; this file says nothing about it.

`S(1, L) = ∑_{m ≠ 0} r_{1,1}(m) 𝔖(m)` is reduced here, by a finite and PROVED computation,
to the singular series along the numbers `2^d - 1`:
* `sprime_two_pow_mul_p3`: `𝔖'(2^a m) = 𝔖'(m)`, since `𝔖'` only sees odd primes.
* `natAbs_two_pow_sub_p3`: `|2^u - 2^v| = 2^v (2^{u-v} - 1)` for `v < u`.
* `S1_eq_p3`: `S(1, N) = 4 c0 ∑_{j < N} F(j)` with `F(j) = ∑_{1 ≤ d ≤ j} 𝔖'(2^d - 1)`;
  this is the evaluation `r_{1,1}(± 2^v (2^d - 1)) = N - d` written as a sum.
* `cesaro_p3`: if `F(j)/j → ν` then `∑_{j < N} F(j) / N² → ν/2`.
* `khalfalah_pintz_lemma1_p3`: the exact statement of `Burst8P2.khalfalah_pintz_lemma1_p2`,
  CONDITIONAL ON the one LEAF `kp_mean_leaf_p3`, the mean value of `𝔖'(2^d - 1)` with
  `A(1) = c0 ν - 1 < 0.2792521041`.
-/
import LeanLab.LZPowersOfTwo.Burst8Lemma4

open Real Finset Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo.Burst9Table

open LeanLab.LZPowersOfTwo LeanLab.LZPowersOfTwo.Burst8P2

/-- `F(j) = ∑_{1 ≤ d ≤ j} 𝔖'(2^d - 1)`, the partial sums of the singular series along the
differences `2^{u} - 2^{v}` with `u - v = d`, after removing the power of two. -/
def kpF (j : ℕ) : ℝ := ∑ d ∈ Icc 1 j, Sprime (2 ^ d - 1)

/-- P0079 page 5, definition (5): `𝔖'(n)` runs over odd primes only, so
`𝔖'(2^a m) = 𝔖'(m)` for `m ≠ 0`. PROVED. -/
theorem sprime_two_pow_mul_p3 (a m : ℕ) (hm : m ≠ 0) : Sprime (2 ^ a * m) = Sprime m := by
  unfold Sprime
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hdvd, _⟩, h2⟩
    refine ⟨⟨hp, ?_, hm⟩, h2⟩
    have hcop : Nat.Coprime p (2 ^ a) := by
      apply Nat.Coprime.pow_right
      exact (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
    exact hcop.dvd_of_dvd_mul_left hdvd
  · rintro ⟨⟨hp, hdvd, _⟩, h2⟩
    exact ⟨⟨hp, Dvd.dvd.mul_left hdvd _, by positivity⟩, h2⟩

/-- `|2^u - 2^v| = 2^v (2^{u-v} - 1)` for `v < u`. PROVED. -/
theorem natAbs_two_pow_sub_p3 (u v : ℕ) (h : v < u) :
    ((2 : ℤ) ^ u - 2 ^ v).natAbs = 2 ^ v * (2 ^ (u - v) - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, u = v + d := ⟨u - v, by omega⟩
  have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have e : ((2 : ℤ) ^ (v + d) - 2 ^ v) = ((2 ^ v * (2 ^ d - 1) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h1]
    ring
  rw [e, Int.natAbs_natCast, Nat.add_sub_cancel_left]

/-- The summand of `S(1, N)` at `v < u` is `2 c0 𝔖'(2^{u-v} - 1)`. PROVED. -/
theorem singS_pair_p3 (u v : ℕ) (h : v < u) :
    singS ((2 : ℤ) ^ u - 2 ^ v).natAbs = 2 * twinC0 * Sprime (2 ^ (u - v) - 1) := by
  rw [natAbs_two_pow_sub_p3 u v h]
  unfold singS
  rw [sprime_two_pow_mul_p3]
  have : 2 ≤ 2 ^ (u - v) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (u - v) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The summand is symmetric in `u` and `v`. -/
theorem singS_symm_p3 (u v : ℕ) :
    singS ((2 : ℤ) ^ u - 2 ^ v).natAbs = singS ((2 : ℤ) ^ v - 2 ^ u).natAbs := by
  rw [show ((2 : ℤ) ^ u - 2 ^ v) = -((2 : ℤ) ^ v - 2 ^ u) by ring, Int.natAbs_neg]

/-- The lower half: `∑_{1 ≤ v < u} 𝔖'(2^{u-v} - 1) = F(u - 1)`, by `d = u - v`. PROVED. -/
theorem lower_half_p3 (u : ℕ) :
    ∑ v ∈ Ico 1 u, Sprime (2 ^ (u - v) - 1) = kpF (u - 1) := by
  unfold kpF
  apply Finset.sum_nbij' (fun v => u - v) (fun d => u - d)
  · intro v hv; simp only [mem_Ico, mem_Icc, coe_Ico, coe_Icc, Set.mem_Ico, Set.mem_Icc] at hv ⊢
    omega
  · intro d hd; simp only [mem_Ico, mem_Icc, coe_Ico, coe_Icc, Set.mem_Ico, Set.mem_Icc] at hd ⊢
    omega
  · intro v hv; simp only [mem_Ico, coe_Ico, Set.mem_Ico] at hv; omega
  · intro d hd; simp only [mem_Icc, coe_Icc, Set.mem_Icc] at hd; omega
  · intro v _; rfl

/-- P0079 page 5, `S(1, L) = ∑_{m ≠ 0} r_{1,1}(m) 𝔖(m)` evaluated:
`S(1, N) = 4 c0 ∑_{j < N} F(j)`. Each `m = ± 2^v (2^d - 1)` with `1 ≤ d < N` has
`N - d` representations `2^u - 2^v` and `𝔖(m) = 2 c0 𝔖'(2^d - 1)`. PROVED. -/
theorem S1_eq_p3 (N : ℕ) : S1 N = 4 * twinC0 * ∑ j ∈ range N, kpF j := by
  set g : ℕ → ℕ → ℝ := fun u v => singS ((2 : ℤ) ^ u - 2 ^ v).natAbs with hg
  have split : ∀ u ∈ Icc 1 N, ∑ v ∈ (Icc 1 N).erase u, g u v =
      ∑ v ∈ Icc 1 N, ((if v < u then g u v else 0) + (if u < v then g u v else 0)) := by
    intro u hu
    rw [← Finset.sum_erase_add (Icc 1 N) _ hu]
    simp only [lt_irrefl, if_false, add_zero]
    apply sum_congr rfl
    intro v hv
    have hne : v ≠ u := Finset.ne_of_mem_erase hv
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h, not_lt.mpr h.le]
    · simp [h, not_lt.mpr h.le]
  have swap : ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, (if u < v then g u v else 0) =
      ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, (if v < u then g u v else 0) := by
    rw [Finset.sum_comm]
    apply sum_congr rfl; intro u _
    apply sum_congr rfl; intro v _
    by_cases h : v < u
    · simp [h, hg, singS_symm_p3]
    · simp [h]
  have lower : ∀ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, (if v < u then g u v else 0) =
      2 * twinC0 * kpF (u - 1) := by
    intro u hu
    simp only [mem_Icc] at hu
    rw [← Finset.sum_filter]
    have hf : (Icc 1 N).filter (fun v => v < u) = Ico 1 u := by
      ext v; simp only [mem_filter, mem_Icc, mem_Ico]; omega
    rw [hf, ← lower_half_p3, mul_sum]
    apply sum_congr rfl
    intro v hv
    simp only [mem_Ico] at hv
    exact singS_pair_p3 u v hv.2
  have shift : ∑ u ∈ Icc 1 N, kpF (u - 1) = ∑ j ∈ range N, kpF j := by
    apply Finset.sum_nbij' (fun u => u - 1) (fun j => j + 1)
    · intro u hu
      simp only [mem_Icc, mem_range, coe_Icc, coe_range, Set.mem_Icc, Set.mem_Iio] at hu ⊢
      omega
    · intro j hj
      simp only [mem_Icc, mem_range, coe_Icc, coe_range, Set.mem_Icc, Set.mem_Iio] at hj ⊢
      omega
    · intro u hu; simp only [mem_Icc, coe_Icc, Set.mem_Icc] at hu; omega
    · intro j _; simp
    · intro u _; rfl
  unfold S1
  rw [sum_congr rfl split]
  simp only [sum_add_distrib]
  rw [swap, sum_congr rfl lower, ← mul_sum, shift]
  ring

/-- The weighted Cesaro step: if `F(j)/j → ν` then `∑_{j < N} F(j) / N² → ν / 2`.
This turns the mean value of `𝔖'(2^d - 1)` into the limit of Lemma 1. PROVED. -/
theorem cesaro_p3 (F : ℕ → ℝ) (ν : ℝ)
    (h : Tendsto (fun n : ℕ => F n / n) atTop (nhds ν)) :
    Tendsto (fun N : ℕ => (∑ j ∈ range N, F j) / (N : ℝ) ^ 2) atTop (nhds (ν / 2)) := by
  -- write `F j = ν j + e j` with `e j / j → 0`
  set e : ℕ → ℝ := fun j => F j - ν * j with he
  have he0 : Tendsto (fun n : ℕ => e n / n) atTop (nhds 0) := by
    have h2 : Tendsto (fun n : ℕ => F n / n - ν) atTop (nhds 0) := by
      simpa using h.sub_const ν
    apply h2.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [he]; field_simp
  have hsplit : ∀ N : ℕ, 1 ≤ N → (∑ j ∈ range N, F j) / (N : ℝ) ^ 2 =
      ν * ((N : ℝ) - 1) / (2 * N) + (∑ j ∈ range N, e j) / (N : ℝ) ^ 2 := by
    intro N hN
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hg : (∑ j ∈ range N, (j : ℝ)) * 2 = N * ((N : ℝ) - 1) := by
      have := Finset.sum_range_id_mul_two N
      have hc : ((∑ j ∈ range N, j : ℕ) : ℝ) * 2 = ((N * (N - 1) : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast [Nat.cast_sub hN] at hc
      exact hc
    have hF : ∑ j ∈ range N, F j = ν * ∑ j ∈ range N, (j : ℝ) + ∑ j ∈ range N, e j := by
      rw [mul_sum, ← sum_add_distrib]; apply sum_congr rfl; intro j _; simp [he]
    rw [hF]
    field_simp
    linear_combination ν * hg
  -- the main part tends to `ν / 2`
  have hmain : Tendsto (fun N : ℕ => ν * ((N : ℝ) - 1) / (2 * N)) atTop (nhds (ν / 2)) := by
    have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h3 : Tendsto (fun N : ℕ => ν / 2 * (1 - 1 / (N : ℝ))) atTop (nhds (ν / 2 * (1 - 0))) :=
      (tendsto_const_nhds.sub h1).const_mul _
    rw [show ν / 2 * (1 - 0) = ν / 2 by ring] at h3
    apply h3.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : (N : ℝ) ≠ 0 := by positivity
    field_simp
  -- the error part tends to `0`
  have herr : Tendsto (fun N : ℕ => (∑ j ∈ range N, e j) / (N : ℝ) ^ 2) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨J0, hJ0⟩ := (Metric.tendsto_atTop.mp he0) (δ / 2) (by positivity)
    set J := max J0 1 with hJdef
    have hJ : ∀ n ≥ J, dist (e n / n) 0 < δ / 2 := fun n hn => hJ0 n (le_trans (le_max_left _ _) hn)
    set K : ℝ := ∑ j ∈ range J, |e j|
    obtain ⟨N0, hN0⟩ := exists_nat_gt (2 * K / δ)
    refine ⟨max (max N0 J) 1, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hNJ : J ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hNN0 : N0 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hbound : ∀ j, J ≤ j → |e j| ≤ δ / 2 * j := by
      intro j hj
      have hpos : 0 < j := lt_of_lt_of_le (by omega) (le_trans (le_max_right J0 1) hj)
      have hjpos : (0 : ℝ) < j := by exact_mod_cast hpos
      have := hJ j hj
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hjpos] at this
      have := (div_lt_iff₀ hjpos).mp this
      linarith
    have hsum : |∑ j ∈ range N, e j| ≤ K + δ / 2 * N ^ 2 := by
      rw [← Finset.sum_range_add_sum_Ico _ hNJ]
      refine (abs_add_le _ _).trans (add_le_add (abs_sum_le_sum_abs _ _) ?_)
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j ∈ Ico J N, |e j| ≤ ∑ j ∈ Ico J N, δ / 2 * (N : ℝ) := by
            apply sum_le_sum; intro j hj; simp only [mem_Ico] at hj
            refine (hbound j hj.1).trans ?_
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact_mod_cast hj.2.le
        _ ≤ ∑ j ∈ range N, δ / 2 * (N : ℝ) := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro j hj; simp only [mem_Ico] at hj; simp only [mem_range]; omega
            · intro _ _ _; positivity
        _ = δ / 2 * N ^ 2 := by simp; ring
    have hK : K < δ / 2 * N := by
      have h1 : 2 * K / δ < N := lt_of_lt_of_le hN0 (by exact_mod_cast hNN0)
      rw [div_lt_iff₀ hδ] at h1
      linarith
    have hKN : K ≤ δ / 2 * N ^ 2 - 0 := by
      have : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
        nlinarith
      nlinarith
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) ^ 2),
      div_lt_iff₀ (by positivity)]
    have hK0 : 0 ≤ K := sum_nonneg (fun _ _ => abs_nonneg _)
    have : (N : ℝ) < (N : ℝ) ^ 2 ∨ (N : ℝ) = 1 := by
      rcases eq_or_lt_of_le (show (1 : ℝ) ≤ N by exact_mod_cast hN1) with h | h
      · right; exact h.symm
      · left; nlinarith
    rcases this with h | h
    · nlinarith
    · rw [h] at hK hsum ⊢; nlinarith
  have := hmain.add herr
  rw [add_zero] at this
  apply this.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [hsplit N hN]

/-- LEAF, sorry. P0079 page 5, Lemma 1 for `k = 1` (Khalfalah and Pintz [10], Theorem 2)
with the numerical bound (22), in the form left after the PROVED evaluation `S1_eq_p3` of
`r_{1,1}`: the singular series `𝔖'(2^d - 1)` has a mean value `ν` over `1 ≤ d ≤ n`, and
`A(1) = c0 ν - 1 < 0.2792521041`. The existence of `ν` is the analytic content of [10],
Theorem 2, and the bound on `c0 ν` is the computation of [10] quoted in (22). -/
theorem kp_mean_leaf_p3 :
    ∃ ν : ℝ, Tendsto (fun n : ℕ => kpF n / n) atTop (nhds ν) ∧
      twinC0 * ν - 1 < 0.2792521041 := by
  sorry

/-- P0079 page 5, Lemma 1 for `k = 1` with (22): the exact statement of
`Burst8P2.khalfalah_pintz_lemma1_p2`. CONDITIONAL ON `kp_mean_leaf_p3`; the reduction is
PROVED by `S1_eq_p3` and `cesaro_p3`, with `A = c0 ν - 1`. -/
theorem khalfalah_pintz_lemma1_p3 :
    ∃ A : ℝ, Tendsto (fun N : ℕ => S1 N / (2 * (N : ℝ) ^ 2) - 1) atTop (nhds A) ∧
      A < 0.2792521041 := by
  obtain ⟨ν, hν, hb⟩ := kp_mean_leaf_p3
  refine ⟨twinC0 * ν - 1, ?_, hb⟩
  have hc := (cesaro_p3 kpF ν hν).const_mul (2 * twinC0)
  have hc' := hc.sub_const 1
  rw [show 2 * twinC0 * (ν / 2) - 1 = twinC0 * ν - 1 by ring] at hc'
  apply hc'.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have h1N : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have : (N : ℝ) ≠ 0 := by positivity
  rw [S1_eq_p3]
  field_simp
  ring

/-- The type agrees with the burst 8 leaf. -/
example : ∃ A : ℝ, Tendsto (fun N : ℕ => S1 N / (2 * (N : ℝ) ^ 2) - 1) atTop (nhds A) ∧
    A < 0.2792521041 := khalfalah_pintz_lemma1_p3

/-! ### Printed numerical constants of pages 3 and 6, PROVED -/

/-- P0079 page 6, proof of Lemma 4: `C = 2 B (1 + A(1))`; with the bound (22) and
`B = 3.9171` this is below the printed `C = 10.0219168340` of (4). PROVED. -/
theorem printed_C_check_p3 : 2 * 3.9171 * (1 + 0.2792521041 : ℝ) < 10.0219168340 := by
  norm_num

/-- P0079 pages 3 and 6: with `B = 1` in Lemma 3, `C = 2 (1 + 0.2792521041) = 2.5585042082`,
exactly as printed. PROVED. -/
theorem printed_C_twin_p3 : 2 * 1 * (1 + 0.2792521041 : ℝ) = 2.5585042082 := by
  norm_num

end LeanLab.LZPowersOfTwo.Burst9Table
