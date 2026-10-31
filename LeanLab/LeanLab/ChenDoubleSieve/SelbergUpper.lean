import LeanLab.ChenDoubleSieve.Statements
import LeanLab.SchnirelmannGoldbach.S1.Final
import LeanLab.ChenExplicit.TwinCNumeric

/-!
# `GoldbachUpper 1200`, unconditional, from the lab's Selberg sieve

Lab proof, unit U-5313, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics,
Brun 1920 and Selberg's sieve for the order of magnitude; P0036 Wu 2004 Theorem 1 gives `7.8209`
and Chen 1978 `7.8342`, both cited in Statements.lean.

* `D_eq_r`: Wu's `D(N) = #{p ≤ N : Ω(N - p) = 1}` is the lab's Goldbach count `r(N)`;
* `singProd_le_oddFactor`: `∏_{p ∣ N} (1 + 1/p) ≤ (3/2) ∏_{p ∣ N, p > 2} (p - 1)/(p - 2)` for even `N`;
* `goldbachUpper_77`: the same with `z = N^{99/100}`, U-5318;
* `goldbachUpper_1200`: `D(N) ≤ 1200 Θ(N)` for all large even `N`, from
  `SchnirelmannGoldbach.S1.r_le_of_even` at `z = N^{1/4}` and `twinC ≥ 0.65`.
Binary Goldbach is OPEN; this is an upper bound for the number of representations.
-/

open Finset Real Filter
open scoped ArithmeticFunction.Omega

noncomputable section
namespace LeanLab.ChenDoubleSieve

open LeanLab.ChenExplicit (twinC)

lemma D_eq_r (N : ℕ) : (D N : ℝ) = (SchnirelmannGoldbach.r N : ℝ) := by
  classical
  unfold D SchnirelmannGoldbach.r
  congr 1
  congr 1
  ext p
  simp only [mem_filter, mem_range, ArithmeticFunction.cardFactors_eq_one_iff_prime]
  constructor
  · rintro ⟨hp, hpr, hq⟩
    refine ⟨?_, hpr, hq⟩
    rcases Nat.lt_succ_iff.mp hp |>.lt_or_eq with h | h
    · exact h
    · subst h; simp at hq; exact absurd hq Nat.not_prime_zero
  · rintro ⟨hp, hpr, hq⟩; exact ⟨by omega, hpr, hq⟩

lemma oddFactor_ge_one (N : ℕ) : 1 ≤ oddFactor N := by
  unfold oddFactor
  calc (1 : ℝ) = ∏ p ∈ N.primeFactors.filter (2 < ·), (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
      intro p hp; simp only [mem_filter] at hp
      have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
      rw [le_div_iff₀ (by linarith)]; linarith

lemma singProd_le_oddFactor (N : ℕ) (hN : Even N) (hN0 : N ≠ 0) :
    SchnirelmannGoldbach.singProd N ≤ 3 / 2 * oddFactor N := by
  unfold SchnirelmannGoldbach.singProd oddFactor
  rw [← prod_filter_mul_prod_filter_not N.primeFactors (fun p => 2 < p)]
  have h2 : N.primeFactors.filter (fun p => ¬ 2 < p) = {2} := by
    ext p
    simp only [mem_filter, Nat.mem_primeFactors, mem_singleton, not_lt]
    constructor
    · rintro ⟨⟨hp, -, -⟩, hle⟩
      have := hp.two_le; omega
    · rintro rfl
      exact ⟨⟨Nat.prime_two, even_iff_two_dvd.mp hN, hN0⟩, le_rfl⟩
  rw [h2, prod_singleton]
  have hP : ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (1 + 1 / (p : ℝ)) ≤
      ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    apply Finset.prod_le_prod₀
    · intro p _; positivity
    · intro p hp
      simp only [mem_filter] at hp
      have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
      rw [show (1 : ℝ) + 1 / p = (p + 1) / p by field_simp]
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
  have h32 : (1 + 1 / ((2 : ℕ) : ℝ)) = 3 / 2 := by norm_num
  rw [h32]
  linarith

/-- `D(N) ≤ 1200 Θ(N)` for all large even `N`, unconditional. -/
theorem goldbachUpper_1200 : GoldbachUpper 1200 := by
  have hev : ∀ᶠ x in atTop, 4 * Real.log x ^ (8 : ℝ) ≤ x ^ ((3 : ℝ) / 4) := by
    have ho := (isLittleO_log_rpow_rpow_atTop (8 : ℝ) (show (0 : ℝ) < 3 / 4 by norm_num)).bound
      (show (0 : ℝ) < 1 / 4 by norm_num)
    filter_upwards [ho, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ x by linarith) ((3 : ℝ) / 4))] at hx
    have := le_abs_self (Real.log x ^ (8 : ℝ))
    linarith
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp
    (hev.and (Real.tendsto_log_atTop.eventually_ge_atTop 4))
  refine ⟨max ⌈X0⌉₊ 2, fun N hN hNX => ?_⟩
  have hN2 : 2 ≤ N := le_of_max_le_right hNX
  have hNX0 : X0 ≤ N := (Nat.le_ceil X0).trans (by exact_mod_cast le_of_max_le_left hNX)
  obtain ⟨hpow, hL4⟩ := hX0 N hNX0
  set L := Real.log N with hL
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 < L := by linarith
  set z : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4) with hz
  have hz1 : 1 < z := Real.one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
  have hz0 : 0 < z := by linarith
  have hlz : Real.log z = L / 4 := by rw [hz, Real.log_rpow hN0]; ring
  have hr := SchnirelmannGoldbach.S1.r_le_of_even hN (by omega) hz1
  rw [hlz] at hr
  have hsp := singProd_le_oddFactor N hN (by omega)
  have hodd := oddFactor_ge_one N
  have htw := LeanLab.ChenExplicit.twinC_ge_065
  -- main term
  have hmain : 32 * N * SchnirelmannGoldbach.singProd N / (L / 4) ^ 2 ≤
      768 * oddFactor N * N / L ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 32 * (N : ℝ) * SchnirelmannGoldbach.singProd N ≤ 32 * N * (3 / 2 * oddFactor N) :=
      mul_le_mul_of_nonneg_left hsp (by positivity)
    nlinarith [sq_nonneg L, mul_pos hN0 (sq_pos_of_pos hL0)]
  -- error term
  have herr : z * (1 + L / 4) ^ 6 + 2 * (z + 1) ≤ oddFactor N * N / L ^ 2 := by
    have h1 : (1 + L / 4) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
    have h8 : L ^ (8 : ℝ) = L ^ 6 * L ^ 2 := by
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hzN : z * (N : ℝ) ^ ((3 : ℝ) / 4) = N := by
      rw [hz, ← Real.rpow_add hN0]; norm_num
    have hL6 : 1 ≤ L ^ 6 := one_le_pow₀ (by linarith)
    have hL6' : 4 ≤ L ^ 6 := by
      calc (4 : ℝ) ≤ 4 ^ 6 := by norm_num
        _ ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL4 6
    have hz6 : z * (1 + L / 4) ^ 6 + 2 * (z + 1) ≤ 4 * z * L ^ 6 := by
      have a1 := mul_le_mul_of_nonneg_left h1 hz0.le
      have a2 : z * 4 ≤ z * L ^ 6 := mul_le_mul_of_nonneg_left hL6' hz0.le
      linarith
    have key : 4 * z * L ^ 6 * L ^ 2 ≤ N := by
      calc 4 * z * L ^ 6 * L ^ 2 = z * (4 * L ^ (8 : ℝ)) := by rw [h8]; ring
        _ ≤ z * (N : ℝ) ^ ((3 : ℝ) / 4) := mul_le_mul_of_nonneg_left hpow hz0.le
        _ = N := hzN
    rw [le_div_iff₀ (by positivity)]
    calc (z * (1 + L / 4) ^ 6 + 2 * (z + 1)) * L ^ 2 ≤ 4 * z * L ^ 6 * L ^ 2 :=
          mul_le_mul_of_nonneg_right hz6 (by positivity)
      _ ≤ N := key
      _ ≤ oddFactor N * N := by nlinarith
  rw [D_eq_r]
  unfold Θ CN
  calc (SchnirelmannGoldbach.r N : ℝ) ≤ _ := hr
    _ ≤ 768 * oddFactor N * N / L ^ 2 + oddFactor N * N / L ^ 2 := by linarith
    _ = 769 * oddFactor N * N / L ^ 2 := by ring
    _ ≤ 1200 * (oddFactor N * twinC * N / L ^ 2) := by
        rw [show 1200 * (oddFactor N * twinC * N / L ^ 2) = 1200 * twinC * (oddFactor N * N) / L ^ 2
          by ring, show 769 * oddFactor N * N / L ^ 2 = 769 * (oddFactor N * N) / L ^ 2 by ring]
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith

/-- `D(N) ≤ 77 Θ(N)` for all large even `N`, unconditional. -/
theorem goldbachUpper_77 : GoldbachUpper 77 := by
  have hev : ∀ᶠ x in atTop, 65 * Real.log x ^ (8 : ℝ) ≤ x ^ ((1 : ℝ) / 100) := by
    have ho := (isLittleO_log_rpow_rpow_atTop (8 : ℝ) (show (0 : ℝ) < 1 / 100 by norm_num)).bound
      (show (0 : ℝ) < 1 / 65 by norm_num)
    filter_upwards [ho, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ x by linarith) ((1 : ℝ) / 100))] at hx
    have := le_abs_self (Real.log x ^ (8 : ℝ))
    linarith
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp
    (hev.and (Real.tendsto_log_atTop.eventually_ge_atTop 4))
  refine ⟨max ⌈X0⌉₊ 2, fun N hN hNX => ?_⟩
  have hN2 : 2 ≤ N := le_of_max_le_right hNX
  have hNX0 : X0 ≤ N := (Nat.le_ceil X0).trans (by exact_mod_cast le_of_max_le_left hNX)
  obtain ⟨hpow, hL4⟩ := hX0 N hNX0
  set L := Real.log N with hL
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 < L := by linarith
  set z : ℝ := (N : ℝ) ^ ((99 : ℝ) / 100) with hz
  have hz1 : 1 < z := Real.one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
  have hz0 : 0 < z := by linarith
  have hlz : Real.log z = 99 / 100 * L := by rw [hz, Real.log_rpow hN0]
  have hr := SchnirelmannGoldbach.S1.r_le_of_even hN (by omega) hz1
  rw [hlz] at hr
  have hsp := singProd_le_oddFactor N hN (by omega)
  have hodd := oddFactor_ge_one N
  have htw := LeanLab.ChenExplicit.twinC_ge_065
  -- main term
  have hmain : 32 * N * SchnirelmannGoldbach.singProd N / (99 / 100 * L) ^ 2 ≤
      49 * oddFactor N * N / L ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 32 * (N : ℝ) * SchnirelmannGoldbach.singProd N ≤ 32 * N * (3 / 2 * oddFactor N) :=
      mul_le_mul_of_nonneg_left hsp (by positivity)
    nlinarith [sq_nonneg L, mul_pos hN0 (sq_pos_of_pos hL0)]
  -- error term
  have herr : z * (1 + 99 / 100 * L) ^ 6 + 2 * (z + 1) ≤ oddFactor N * N / L ^ 2 := by
    have h1 : (1 + 99 / 100 * L) ^ 6 ≤ (2 * L) ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
    have h8 : L ^ (8 : ℝ) = L ^ 6 * L ^ 2 := by
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hzN : z * (N : ℝ) ^ ((1 : ℝ) / 100) = N := by
      rw [hz, ← Real.rpow_add hN0]; norm_num
    have hL6 : 1 ≤ L ^ 6 := one_le_pow₀ (by linarith)
    have hL6' : 4 ≤ L ^ 6 := by
      calc (4 : ℝ) ≤ 4 ^ 6 := by norm_num
        _ ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL4 6
    have hz6 : z * (1 + 99 / 100 * L) ^ 6 + 2 * (z + 1) ≤ 65 * z * L ^ 6 := by
      have a1 := mul_le_mul_of_nonneg_left h1 hz0.le
      have e : (2 * L) ^ 6 = 64 * L ^ 6 := by ring
      rw [e] at a1
      have a2 : z * 4 ≤ z * L ^ 6 := mul_le_mul_of_nonneg_left hL6' hz0.le
      linarith
    have key : 65 * z * L ^ 6 * L ^ 2 ≤ N := by
      calc 65 * z * L ^ 6 * L ^ 2 = z * (65 * L ^ (8 : ℝ)) := by rw [h8]; ring
        _ ≤ z * (N : ℝ) ^ ((1 : ℝ) / 100) := mul_le_mul_of_nonneg_left hpow hz0.le
        _ = N := hzN
    rw [le_div_iff₀ (by positivity)]
    calc (z * (1 + 99 / 100 * L) ^ 6 + 2 * (z + 1)) * L ^ 2 ≤ 65 * z * L ^ 6 * L ^ 2 :=
          mul_le_mul_of_nonneg_right hz6 (by positivity)
      _ ≤ N := key
      _ ≤ oddFactor N * N := by nlinarith
  rw [D_eq_r]
  unfold Θ CN
  calc (SchnirelmannGoldbach.r N : ℝ) ≤ _ := hr
    _ ≤ 49 * oddFactor N * N / L ^ 2 + oddFactor N * N / L ^ 2 := by linarith
    _ = 50 * oddFactor N * N / L ^ 2 := by ring
    _ ≤ 77 * (oddFactor N * twinC * N / L ^ 2) := by
        rw [show 77 * (oddFactor N * twinC * N / L ^ 2) = 77 * twinC * (oddFactor N * N) / L ^ 2
          by ring, show 50 * oddFactor N * N / L ^ 2 = 50 * (oddFactor N * N) / L ^ 2 by ring]
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith

end LeanLab.ChenDoubleSieve
