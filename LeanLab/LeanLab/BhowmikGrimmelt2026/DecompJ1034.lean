import LeanLab.BhowmikGrimmelt2026.Statements
import LeanLab.BhowmikGrimmelt2026.DecompJ249
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue

namespace LeanLab.BhowmikGrimmelt2026

/-! ### Elementary properties of `ee` -/

private lemma ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  simp only [ee, ← Complex.exp_add]
  push_cast
  ring_nf

private lemma ee_nat_mul (t : ℝ) (a : ℕ) : ee ((a : ℝ) * t) = ee t ^ a := by
  induction a with
  | zero => simp [ee]
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, ee_add, ih, pow_succ]

private lemma ee_one : ee 1 = 1 := by
  refine Complex.exp_eq_one_iff.mpr ⟨1, ?_⟩
  push_cast
  ring

private lemma ee_natCast (n : ℕ) : ee (n : ℝ) = 1 := by
  have h : ee (n : ℝ) = ee 1 ^ n := by simpa using ee_nat_mul 1 n
  rw [h, ee_one, one_pow]

/-! ### The Ramanujan sum at a prime -/

private lemma ramanujan_prime_val {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (ramanujan p (N : ℤ)).re = if p ∣ N then (p : ℝ) - 1 else -1 := by
  have hp0 : 0 < p := hp.pos
  set t : ℝ := (N : ℝ) / (p : ℝ) with ht
  set ζ : ℂ := ee t with hζ
  -- the reduced residues below a prime are the nonzero ones
  have hfilter : (Finset.range p).filter (fun a => Nat.Coprime a p) =
      (Finset.range p).erase 0 := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1⟩
      rintro rfl
      rw [Nat.coprime_zero_left] at h2
      exact hp.ne_one h2
    · rintro ⟨h0, h1⟩
      exact ⟨h1, Nat.coprime_comm.mpr
        (hp.coprime_iff_not_dvd.mpr fun hd => h0 (Nat.eq_zero_of_dvd_of_lt hd h1))⟩
  have hterm : ∀ a : ℕ, ee ((a : ℝ) * ((N : ℤ) : ℝ) / (p : ℝ)) = ζ ^ a := by
    intro a
    rw [← ee_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have hζp : ζ ^ p = 1 := by
    rw [← ee_nat_mul]
    have hpt : (p : ℝ) * t = (N : ℝ) := by
      rw [ht]
      field_simp
    rw [hpt, ee_natCast]
  have hζ1 : ζ = 1 ↔ p ∣ N := by
    have hrec : ζ = Complex.exp (2 * ↑Real.pi * Complex.I * (N : ℂ) / (p : ℂ)) := by
      simp only [hζ, ee, ht]
      congr 1
      push_cast
      have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      field_simp
    rw [hrec, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hp.ne_zero]
  -- the full geometric sum
  have hgeom : ∑ a ∈ Finset.range p, ζ ^ a = if ζ = 1 then (p : ℂ) else 0 := by
    by_cases h1 : ζ = 1
    · rw [if_pos h1]
      simp [h1]
    · rw [if_neg h1]
      have h := geom_sum_mul ζ p
      rw [hζp, sub_self] at h
      exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr h1)
  have hsum : ∑ a ∈ (Finset.range p).filter (fun a => Nat.Coprime a p),
      ee ((a : ℝ) * ((N : ℤ) : ℝ) / (p : ℝ)) =
      (∑ a ∈ Finset.range p, ζ ^ a) - 1 := by
    rw [hfilter, Finset.sum_congr rfl (fun a _ => hterm a), eq_sub_iff_add_eq]
    simpa using Finset.sum_erase_add (Finset.range p) (fun a => ζ ^ a)
      (Finset.mem_range.mpr hp0)
  unfold ramanujan
  rw [hsum, hgeom]
  by_cases hd : p ∣ N
  · rw [if_pos (hζ1.mpr hd), if_pos hd]
    simp
  · rw [if_neg (fun h => hd (hζ1.mp h)), if_neg hd]
    simp

/-! ### The Euler factor at a prime -/

private lemma ee_zero : ee 0 = 1 := by
  simp [ee]

private lemma ramanujan_one (n : ℤ) : ramanujan 1 n = 1 := by
  simp [ramanujan, ee_zero]

private lemma eulerFactorSing_prime_val {p : ℕ} (hp : p.Prime) (N : ℕ) :
    eulerFactorSing N p = 1 + (ramanujan p (N : ℤ)).re / (Nat.totient p : ℝ) ^ 2 := by
  have hne : ∀ k : ℕ, p ^ k ≠ 0 := fun k => pow_ne_zero k hp.ne_zero
  unfold eulerFactorSing
  rw [tsum_eq_sum (s := {0, 1}) ?_, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  · simp only [pow_zero, pow_one, Nat.totient_one, ArithmeticFunction.moebius_apply_one,
      ArithmeticFunction.moebius_apply_prime hp]
    rw [ramanujan_one]
    simp only [Complex.one_re]
    ring
  · intro k hk
    have hk2 : 2 ≤ k := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      omega
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp

/-- The Euler factor at `2` is `2` at an even argument: `c₂(N) = 1` and `φ(2) = 1`. -/
private lemma eulerFactorSing_two {N : ℕ} (hN : Even N) : eulerFactorSing N 2 = 2 := by
  have hp : Nat.Prime 2 := Nat.prime_two
  rw [eulerFactorSing_prime_val hp N, ramanujan_prime_val hp N, Nat.totient_two]
  have h2 : (2 : ℕ) ∣ N := even_iff_two_dvd.mp hN
  rw [if_pos h2]
  norm_num

/-- Every odd prime factor of the Euler product is at least `1 - 1/(p-1)²`. -/
private lemma eulerFactorSing_odd_ge {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ eulerFactorSing N p := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    linarith
  have hφ : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  rw [eulerFactorSing_prime_val hp N, ramanujan_prime_val hp N, Nat.totient_prime hp, hφ]
  by_cases hd : p ∣ N
  · rw [if_pos hd]
    have h1 : ((p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 = 1 / ((p : ℝ) - 1) := by
      field_simp
    rw [h1]
    have h1' : 0 < 1 / ((p : ℝ) - 1) := by positivity
    have h2' : 0 < 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    nlinarith
  · rw [if_neg hd]
    have hgoal : (1 : ℝ) + (-1) / ((p : ℝ) - 1) ^ 2 = 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
      rw [neg_div]
      ring
    rw [hgoal]

/-! ### The Wallis-type product over the even integers -/

private lemma prod_step (x : ℝ) (hx : 0 ≤ x) :
    (x + 1 + 1) / (2 * (x + 1) + 1) ≤
      ((x + 1) / (2 * x + 1)) * (1 - 1 / (2 * (x + 1)) ^ 2) := by
  have h1 : (2 * x + 1) ≠ 0 := by positivity
  have h2 : (2 * (x + 1)) ≠ 0 := by positivity
  have key : ((x + 1) / (2 * x + 1)) * (1 - 1 / (2 * (x + 1)) ^ 2) =
      (2 * x + 3) / (4 * (x + 1)) := by
    field_simp
    ring
  rw [key, div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith

private lemma prod_even_ge_half (n : ℕ) :
    (1 : ℝ) / 2 ≤ ∏ k ∈ Finset.range (n + 1), (1 - 1 / (2 * (k : ℝ)) ^ 2) := by
  have key : ∀ m : ℕ, ((m : ℝ) + 1) / (2 * (m : ℝ) + 1) ≤
      ∏ k ∈ Finset.range (m + 1), (1 - 1 / (2 * (k : ℝ)) ^ 2) := by
    intro m
    induction m with
    | zero => simp
    | succ p ih =>
      rw [Finset.prod_range_succ]
      push_cast
      have hg0 : (0 : ℝ) ≤ 1 - 1 / (2 * ((p : ℝ) + 1)) ^ 2 := by
        have h1 : (1 : ℝ) ≤ 2 * ((p : ℝ) + 1) := by
          have : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
          linarith
        have h2 : (1 : ℝ) ≤ (2 * ((p : ℝ) + 1)) ^ 2 := by nlinarith
        rw [show (1 : ℝ) - 1 / (2 * ((p : ℝ) + 1)) ^ 2 =
          1 - 1 / (2 * ((p : ℝ) + 1)) ^ 2 from rfl]
        have h3 : 1 / (2 * ((p : ℝ) + 1)) ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact h2
        linarith
      have hstep := prod_step (p : ℝ) (Nat.cast_nonneg p)
      have h2 := mul_le_mul_of_nonneg_right ih hg0
      exact le_trans hstep h2
  have hle := key n
  have hhalf : (1 : ℝ) / 2 ≤ ((n : ℝ) + 1) / (2 * (n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  linarith

/-! ### The partial Euler products -/

private lemma prod_factor_nonneg {m : ℕ} (hm : ∃ k, m = 2 * k + 1) :
    (0 : ℝ) ≤ 1 - 1 / ((m : ℝ) - 1) ^ 2 := by
  obtain ⟨k, rfl⟩ := hm
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    norm_num
  · have h1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
      have : (1 : ℕ) ≤ 2 * k := by omega
      exact_mod_cast this
    have h2 : (1 : ℝ) ≤ (2 * (k : ℝ)) ^ 2 := by nlinarith
    have h3 : 1 / (2 * (k : ℝ)) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact h2
    have hcast : (((2 * k + 1 : ℕ) : ℝ) - 1) = 2 * (k : ℝ) := by push_cast; ring
    rw [hcast]
    linarith

private lemma partial_prod_ge_one {N : ℕ} (hN : Even N) (X : ℕ) :
    1 ≤ ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorSing N p := by
  classical
  set s := (Finset.range X).filter Nat.Prime with hs
  rcases Nat.lt_or_ge X 3 with hX | hX
  · have hse : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      simp only [hs, Finset.mem_filter, Finset.mem_range] at hp
      have := hp.2.two_le
      omega
    rw [hse]
    simp
  · have h2s : 2 ∈ s := by
      simp only [hs, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, Nat.prime_two⟩
    set t := (Finset.range X).image (fun k => 2 * k + 1) with ht
    have htmem : ∀ k, k ∈ Finset.range X ↔ 2 * k + 1 ∈ t := by
      intro k
      simp only [ht, Finset.mem_image, Finset.mem_range]
      constructor
      · intro hk
        exact ⟨k, hk, rfl⟩
      · rintro ⟨j, hj, hjk⟩
        have : j = k := by omega
        omega
    have hsub : s.erase 2 ⊆ t := by
      intro p hp
      simp only [Finset.mem_erase, hs, Finset.mem_filter, Finset.mem_range] at hp
      obtain ⟨hp2, hpx, hpp⟩ := hp
      have hodd : Odd p := by
        rcases hpp.eq_two_or_odd with h | h
        · exact absurd h hp2
        · exact Nat.odd_iff.mpr h
      obtain ⟨j, hj⟩ := hodd
      rw [ht, Finset.mem_image]
      exact ⟨j, by simp only [Finset.mem_range]; omega, by omega⟩
    have hf0 : ∀ m ∈ t, (0 : ℝ) ≤ 1 - 1 / ((m : ℝ) - 1) ^ 2 := by
      intro m hm
      rw [ht, Finset.mem_image] at hm
      obtain ⟨k, -, rfl⟩ := hm
      exact prod_factor_nonneg ⟨k, rfl⟩
    have hf1 : ∀ m ∈ t, (1 : ℝ) - 1 / ((m : ℝ) - 1) ^ 2 ≤ 1 := by
      intro m _
      have h : (0 : ℝ) ≤ 1 / ((m : ℝ) - 1) ^ 2 := by positivity
      linarith
    have hCA : ∏ m ∈ t, (1 - 1 / ((m : ℝ) - 1) ^ 2) ≤
        ∏ p ∈ s.erase 2, (1 - 1 / ((p : ℝ) - 1) ^ 2) :=
      Finset.prod_le_prod_of_subset_of_le_one₀ hsub hf0
        (fun m hm _ => hf1 m hm)
    have hAB : ∏ p ∈ s.erase 2, (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤
        ∏ p ∈ s.erase 2, eulerFactorSing N p := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact hf0 p (hsub hp)
      · intro p hp
        simp only [Finset.mem_erase, hs, Finset.mem_filter] at hp
        exact eulerFactorSing_odd_ge hp.2.2 hp.1 N
    have hCt : (1 : ℝ) / 2 ≤
        ∏ m ∈ Finset.image (fun k : ℕ => 2 * k + 1) (Finset.range X),
          (1 - 1 / ((m : ℝ) - 1) ^ 2) := by
      rw [Finset.prod_image (g := fun k : ℕ => 2 * k + 1)
        (f := fun m : ℕ => 1 - 1 / ((m : ℝ) - 1) ^ 2) (fun a _ b _ hab => by
          have h : 2 * a + 1 = 2 * b + 1 := hab
          omega)]
      have hprod : ∏ k ∈ Finset.range X, (1 - 1 / ((((2 * k + 1 : ℕ) : ℝ)) - 1) ^ 2) =
          ∏ k ∈ Finset.range X, (1 - 1 / (2 * (k : ℝ)) ^ 2) := by
        apply Finset.prod_congr rfl
        intro k _
        have hcast : (((2 * k + 1 : ℕ) : ℝ) - 1) = 2 * (k : ℝ) := by push_cast; ring
        rw [hcast]
      rw [hprod]
      have hX1 : X - 1 + 1 = X := by omega
      rw [← hX1]
      exact prod_even_ge_half (X - 1)
    have hB : (1 : ℝ) / 2 ≤ ∏ p ∈ s.erase 2, eulerFactorSing N p :=
      le_trans hCt (le_trans hCA hAB)
    rw [← Finset.insert_erase h2s,
      Finset.prod_insert (Finset.notMem_erase 2 s), eulerFactorSing_two hN]
    linarith


private lemma singular_ge_one {N : ℕ} (hN : Even N) (hNpos : 0 < N) :
    (1 : ℝ) ≤ singular N := by
  have hlim := euler_sing_eq N hNpos
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
    (fun X => partial_prod_ge_one hN X)

-- LEAF 1: Telescoping inequality
/-- LEAF. Page 6. The twin prime constant telescoping lower bound.
REPAIRED 20261106: `0 < N` added, because at `N = 0` the defining series is not summable and
Lean's totalized `tsum` gives `singular 0 = 0` (`ZeroEndpoint261.singular_zero261`). -/
theorem singular_series_lower_bound (N : ℕ) (hN : Even N) (hNpos : 0 < N) :
    (1 : ℝ) ≤ singular N :=
  singular_ge_one hN hNpos

-- LEAF 2: von Mangoldt factor upper bound for Goldbach exceptions
/-- LEAF. Page 13. Proper prime power sum bound. -/
theorem r2_prime_power_bound (N : ℕ) (hN : Even N) (h_not_G : ¬ IsGoldbachSum N) :
  r2 N ≤ 3/2 * (N : ℝ)^(1/2) * (Real.log (N : ℝ))^3 := by
  sorry

-- LEAF 3: Asymptotic inequality
/-- LEAF. Page 13. Size comparison for large N. -/
theorem r2_bound_le_half_N (N : ℕ) (hN : 2^30 ≤ N) :
  3/2 * (N : ℝ)^(1/2) * (Real.log (N : ℝ))^3 ≤ 1/2 * N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h0 : (0 : ℕ) < N := by
      have h1 : (0 : ℕ) < 2^30 := by norm_num
      omega
    exact_mod_cast h0
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h1 : (1 : ℕ) ≤ N := by
      have h2 : (1 : ℕ) ≤ 2^30 := by norm_num
      omega
    exact_mod_cast h1
  -- the exponent `1/2` in the statement is `ℕ`-division, so it is `0`
  have hexp : (N : ℝ) ^ ((1 : ℕ) / 2) = 1 := by norm_num
  rw [hexp, mul_one]
  -- `log N ≤ 6 N^(1/6)`
  have hlog : Real.log (N : ℝ) ≤ 6 * (N : ℝ) ^ ((1:ℝ)/6) := by
    have h := Real.log_le_rpow_div (le_of_lt hNpos) (by norm_num : (0:ℝ) < 1/6)
    calc Real.log (N : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/6) / (1/6) := h
      _ = 6 * (N : ℝ) ^ ((1:ℝ)/6) := by
            rw [div_eq_mul_inv, show ((1:ℝ)/6)⁻¹ = 6 by norm_num, mul_comm]
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  -- so `(log N)^3 ≤ 216 √N`
  have hcube : (Real.log (N : ℝ))^3 ≤ 216 * Real.sqrt (N : ℝ) := by
    have h1 : (Real.log (N : ℝ))^3 ≤ (6 * (N : ℝ) ^ ((1:ℝ)/6))^3 :=
      pow_le_pow_left₀ hlog0 hlog 3
    have h2 : (6 * (N : ℝ) ^ ((1:ℝ)/6))^3 = 216 * Real.sqrt (N : ℝ) := by
      rw [Real.sqrt_eq_rpow, mul_pow]
      norm_num
      rw [← Real.rpow_natCast ((N : ℝ) ^ ((1:ℝ)/6)) 3,
        ← Real.rpow_mul (le_of_lt hNpos)]
      norm_num
    linarith
  -- and `648 √N ≤ N`
  have hsqrt : (32768 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have h : Real.sqrt ((32768:ℝ)^2) ≤ Real.sqrt (N : ℝ) := by
      apply Real.sqrt_le_sqrt
      have : ((32768:ℝ)^2) = ((2:ℕ)^30 : ℝ) := by norm_num
      rw [this]
      exact_mod_cast hN
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 32768)] at h
  have hkey : 648 * Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hNpos)
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  nlinarith [Real.sqrt_nonneg (N : ℝ)]

theorem exceptional_gap150_j1034 : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → Even N → ¬ IsGoldbachSum N → c * N ≤ |E2 N| := by
  use 1 / 2
  refine ⟨by norm_num, 2^30, ?_⟩
  intro N hN hEven hNotG
  have h1 : 1 ≤ singular N := singular_series_lower_bound N hEven (by
    have h0 : (0:ℕ) < 2^30 := by norm_num
    omega)
  have h2 : r2 N ≤ 3/2 * (N : ℝ)^(1/2) * (Real.log (N : ℝ))^3 := r2_prime_power_bound N hEven hNotG
  have h3 : 3/2 * (N : ℝ)^(1/2) * (Real.log (N : ℝ))^3 ≤ 1/2 * N := r2_bound_le_half_N N hN
  have h4 : r2 N ≤ 1/2 * N := le_trans h2 h3
  unfold E2
  have h5 : (N : ℝ) * singular N ≥ N := by
    calc (N : ℝ) * singular N ≥ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
         _ = N := mul_one _
  have h6 : (N : ℝ) * singular N - r2 N ≥ 1/2 * N := by
    linarith
  rw [abs_sub_comm]
  exact le_trans h6 (le_abs_self _)

end LeanLab.BhowmikGrimmelt2026
