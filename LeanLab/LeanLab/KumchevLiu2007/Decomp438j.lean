/-
Numerical smooth tail supply for three-square truncation.
Source page 14 below display 50. The numerical leaf remains OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp438i
import LeanLab.PNTSieve.MertensUpper

namespace LeanLab.KumchevLiu2007.Task438j

open Real Complex Task129b Task129c Task292c Task438d
open scoped BigOperators

private theorem frac_local_bound (Q : ℝ) (hQ : 0 < Q) (p : ℕ)
    (hp : p.Prime) (hpQ : (p : ℝ) ≤ Q) :
    0 < (p : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q))) - 1 ∧
      64 / ((p : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q))) - 1) ≤ 768 / (p : ℝ) := by
  let V := max 1 (Real.log Q)
  let δ := 1 / (2 * V)
  let s := 1 - δ
  have hV1 : 1 ≤ V := le_max_left _ _
  have hVpos : 0 < V := by linarith
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hδ : δ ≤ (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by dsimp [V] at *; linarith)
  have hs : (1 / 2 : ℝ) ≤ s := by dsimp [s]; linarith
  have hlog : Real.log (p : ℝ) ≤ V :=
    (Real.log_le_log hp0 hpQ).trans (le_max_right _ _)
  have hδlog : Real.log (p : ℝ) * δ ≤ 1 := by
    dsimp [δ]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * V)).mpr
    linarith
  have hexp : Real.exp (Real.log (p : ℝ) * δ) ≤ 3 := by
    exact (Real.exp_le_exp.mpr hδlog).trans (by linarith [Real.exp_one_lt_d9])
  have hprod : (p : ℝ) ^ s * Real.exp (Real.log (p : ℝ) * δ) = (p : ℝ) := by
    rw [Real.rpow_def_of_pos hp0, ← Real.exp_add]
    have he : Real.log (p : ℝ) * s + Real.log (p : ℝ) * δ = Real.log (p : ℝ) := by
      dsimp [s]
      ring
    rw [he, Real.exp_log hp0]
  have hp3 : (p : ℝ) / 3 ≤ (p : ℝ) ^ s := by
    have hh := mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hp0.le s)
    rw [hprod] at hh
    linarith
  have hsqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hp43 : (4 / 3 : ℝ) ≤ (p : ℝ) ^ s := by
    calc
      _ ≤ Real.sqrt 2 := hsqrt
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 2
      _ ≤ (p : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hp2 (by norm_num)
      _ ≤ (p : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by linarith) hs
  have hden : (p : ℝ) / 12 ≤ (p : ℝ) ^ s - 1 := by linarith
  have hdenpos : 0 < (p : ℝ) ^ s - 1 := lt_of_lt_of_le (by positivity) hden
  change 0 < (p : ℝ) ^ s - 1 ∧ 64 / ((p : ℝ) ^ s - 1) ≤ 768 / (p : ℝ)
  refine ⟨hdenpos, ?_⟩
  apply (div_le_div_iff₀ hdenpos hp0).mpr
  nlinarith

/-! ### Uniform numerical Euler product bound (port of EulerProduct447) -/

private theorem frac_euler_product_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ Q : ℝ, 0 < Q →
      (∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime,
        (1 + 64 / ((p : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q))) - 1))) ≤
        C * (max 1 (Real.log Q)) ^ D := by
  classical
  refine ⟨Real.exp 9216, 768, Real.exp_pos _, by norm_num, ?_⟩
  intro Q hQ
  let S := (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime
  let s := 1 - 1 / (2 * max 1 (Real.log Q))
  by_cases hQ2 : 2 ≤ Q
  · let N := ⌊Q⌋₊
    have hN2 : 2 ≤ N := Nat.le_floor hQ2
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hNQ : (N : ℝ) ≤ Q := Nat.floor_le hQ.le
    have hlocal (p : ℕ) (hp : p ∈ S) :
        0 < 1 + 64 / ((p : ℝ) ^ s - 1) ∧
          Real.log (1 + 64 / ((p : ℝ) ^ s - 1)) ≤ 768 * (1 / (p : ℝ)) := by
      have hprime := (Finset.mem_filter.mp hp).2
      have hpN : p ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
      have hpQ : (p : ℝ) ≤ Q := (Nat.cast_le.mpr hpN).trans hNQ
      obtain ⟨hd, hb⟩ := frac_local_bound Q hQ p hprime hpQ
      change 0 < (p : ℝ) ^ s - 1 at hd
      change 64 / ((p : ℝ) ^ s - 1) ≤ 768 / (p : ℝ) at hb
      have hpos : 0 < 1 + 64 / ((p : ℝ) ^ s - 1) := by positivity
      refine ⟨hpos, ?_⟩
      have hh := Real.log_le_sub_one_of_pos hpos
      have hh' : Real.log (1 + 64 / ((p : ℝ) ^ s - 1)) ≤ 64 / ((p : ℝ) ^ s - 1) := by
        linarith
      convert hh'.trans hb using 1 <;> ring
    have hsum : (∑ p ∈ S, 1 / (p : ℝ)) ≤ Real.log (Real.log (N : ℝ)) + 12 := by
      have hsub : S ⊆ (Finset.Icc 1 N).filter Nat.Prime := by
        intro p hp
        obtain ⟨hpr, hprime⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨hprime.one_le, Nat.lt_succ_iff.mp (Finset.mem_range.mp hpr)⟩, hprime⟩
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp hn => by positivity)).trans
        (LeanLab.PNTSieve.Mertens.sum_inv_primes_le N hN2)
    have hprodpos : 0 < ∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1)) :=
      Finset.prod_pos (fun p hp => (hlocal p hp).1)
    have hlogprod : Real.log (∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1))) ≤
        768 * (Real.log (Real.log (N : ℝ)) + 12) := by
      rw [Real.log_prod (fun p hp => (hlocal p hp).1.ne')]
      calc
        _ ≤ ∑ p ∈ S, 768 * (1 / (p : ℝ)) := Finset.sum_le_sum (fun p hp => (hlocal p hp).2)
        _ = 768 * ∑ p ∈ S, 1 / (p : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)
    have hprod : (∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1))) ≤
        Real.exp 9216 * (Real.log (N : ℝ)) ^ (768 : ℕ) := by
      have hh := (Real.log_le_iff_le_exp hprodpos).mp hlogprod
      have he : Real.exp (768 * (Real.log (Real.log (N : ℝ)) + 12)) =
          Real.exp 9216 * (Real.log (N : ℝ)) ^ (768 : ℕ) := by
        rw [mul_add, Real.exp_add, show (768 : ℝ) = ((768 : ℕ) : ℝ) by norm_num,
          Real.exp_nat_mul, Real.exp_log hlogN]
        norm_num
        ring
      exact hh.trans_eq he
    calc
      _ ≤ Real.exp 9216 * (Real.log (N : ℝ)) ^ (768 : ℕ) := hprod
      _ ≤ Real.exp 9216 * (max 1 (Real.log Q)) ^ (768 : ℕ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply pow_le_pow_left₀ hlogN.le
        exact (Real.log_le_log hNpos hNQ).trans (le_max_right _ _)
      _ = _ := by norm_num
  · have hS : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hprime := (Finset.mem_filter.mp hp).2
      have hpN : p ≤ ⌊Q⌋₊ :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
      have hpQ : (p : ℝ) ≤ Q := (Nat.cast_le.mpr hpN).trans (Nat.floor_le hQ.le)
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      linarith
    change (∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1))) ≤ _
    rw [hS, Finset.prod_empty]
    have hC : 1 ≤ Real.exp 9216 := Real.one_le_exp (by norm_num)
    have hV : 1 ≤ (max 1 (Real.log Q)) ^ (768 : ℝ) :=
      Real.one_le_rpow (le_max_left _ _) (by norm_num)
    nlinarith

/-! ### Finite Euler comparison (port of SmoothEuler447, no new definitions) -/

private theorem wr_nonneg (s : ℝ) (q : ℕ) : 0 ≤ coefficientMajorant q / (q : ℝ) ^ s := by
  unfold coefficientMajorant
  positivity

private theorem wr_one (s : ℝ) : coefficientMajorant 1 / ((1 : ℕ) : ℝ) ^ s = 1 := by
  simp [coefficientMajorant]

private theorem wr_mul (s : ℝ) (hs : 0 < s) (a b : ℕ) (hab : a.Coprime b) :
    coefficientMajorant (a * b) / ((a * b : ℕ) : ℝ) ^ s =
      (coefficientMajorant a / (a : ℝ) ^ s) * (coefficientMajorant b / (b : ℝ) ^ s) := by
  by_cases ha : a = 0
  · subst a
    simp [Real.zero_rpow hs.ne']
  by_cases hb : b = 0
  · subst b
    simp [Real.zero_rpow hs.ne']
  have hM : coefficientMajorant (a * b) = coefficientMajorant a * coefficientMajorant b := by
    simp only [coefficientMajorant, Nat.primeFactors_mul ha hb,
      Finset.prod_union hab.disjoint_primeFactors]
  simp only [hM, Nat.cast_mul, Real.mul_rpow (by positivity : (0 : ℝ) ≤ a)
    (by positivity : (0 : ℝ) ≤ b)]
  ring

private theorem wr_prime_power_hasSum (p : ℕ) (hp : p.Prime) (s : ℝ) (hs : 0 < s) :
    HasSum (fun k : ℕ => coefficientMajorant (p ^ k) / ((p ^ k : ℕ) : ℝ) ^ s)
      (1 + 64 / ((p : ℝ) ^ s - 1)) := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hps : 1 < (p : ℝ) ^ s := Real.one_lt_rpow (by exact_mod_cast hp.one_lt) hs
  let r := ((p : ℝ) ^ s)⁻¹
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ hps
  have hterm (k : ℕ) : coefficientMajorant (p ^ k) / ((p ^ k : ℕ) : ℝ) ^ s =
      64 * r ^ k - (if k = 0 then 63 else 0) := by
    by_cases hk : k = 0
    · subst k
      norm_num [coefficientMajorant]
    · have hpow : (((p ^ k : ℕ) : ℝ)) ^ s = ((p : ℝ) ^ s) ^ k := by
        rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
          mul_comm (k : ℝ) s, Real.rpow_mul hp0.le, Real.rpow_natCast]
      simp only [coefficientMajorant, Nat.primeFactors_prime_pow hk hp,
        Finset.prod_singleton, hpow, hk, ite_false, sub_zero]
      dsimp [r]
      rw [inv_pow, div_eq_mul_inv]
  have hh := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (64 : ℝ)).sub
    (hasSum_ite_eq (0 : ℕ) (63 : ℝ))
  have he : 64 * (1 - r)⁻¹ - 63 = 1 + 64 / ((p : ℝ) ^ s - 1) := by
    dsimp [r]
    have hpos : 0 < (p : ℝ) ^ s := by positivity
    field_simp [ne_of_gt hpos, ne_of_gt (sub_pos.mpr hps)]
    <;> ring
  rw [he] at hh
  simpa only [← hterm] using hh

private theorem smooth_moment_euler_bound (Q : ℝ) (M : ℕ) (hQ : 0 < Q) (s : ℝ) (hs : 0 < s) :
    (∑ q ∈ Finset.Icc 1 M,
      smoothWeight q Q * coefficientMajorant q / (q : ℝ) ^ s) ≤
      ∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime,
        (1 + 64 / ((p : ℝ) ^ s - 1)) := by
  classical
  let S := (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime
  have hsum (p : ℕ) (hp : p.Prime) :
      Summable (fun k : ℕ => ‖coefficientMajorant (p ^ k) / ((p ^ k : ℕ) : ℝ) ^ s‖) := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (wr_nonneg s _)]
    exact (wr_prime_power_hasSum p hp s hs).summable
  have H := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun q : ℕ => coefficientMajorant q / (q : ℝ) ^ s)
    (wr_one s) (fun {a b} hab => wr_mul s hs a b hab) (fun {p} hp => hsum p hp) S).2
  have hfilter : S.filter Nat.Prime = S := by
    exact Finset.filter_eq_self.mpr (fun p hp => (Finset.mem_filter.mp hp).2)
  rw [hfilter] at H
  have hprod : (∏ p ∈ S, ∑' k : ℕ, coefficientMajorant (p ^ k) / ((p ^ k : ℕ) : ℝ) ^ s) =
      ∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1)) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact (wr_prime_power_hasSum p (Finset.mem_filter.mp hp).2 s hs).tsum_eq
  rw [hprod] at H
  let T := (Finset.Icc 1 M).filter (fun q => ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q)
  have hT (q : ℕ) (hq : q ∈ T) : q ∈ Nat.factoredNumbers S := by
    apply Nat.mem_factoredNumbers'.mpr
    intro p hp hpq
    have hpQ := (Finset.mem_filter.mp hq).2 p hp hpq
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.lt_succ_iff.mpr (Nat.le_floor hpQ)), hp⟩
  have he : (∑ q ∈ Finset.Icc 1 M,
      smoothWeight q Q * coefficientMajorant q / (q : ℝ) ^ s) =
      ∑ q ∈ T, coefficientMajorant q / (q : ℝ) ^ s := by
    simp only [smoothWeight, ite_mul, one_mul, zero_mul, ite_div, zero_div]
    rw [← Finset.sum_filter]
  rw [he]
  change (∑ q ∈ T, coefficientMajorant q / (q : ℝ) ^ s) ≤
    ∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1))
  rw [← Finset.sum_subtype_of_mem (fun q => coefficientMajorant q / (q : ℝ) ^ s) hT]
  exact (Summable.sum_le_tsum (T.subtype (fun q => q ∈ Nat.factoredNumbers S))
    (fun q hq => wr_nonneg s q) H.summable).trans_eq H.tsum_eq

/-! ### Fractional smooth moment (port of Decomp447c) -/

private theorem smooth_fractional_moment :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ (Q : ℝ) (M : ℕ), 0 < Q →
      (∑ q ∈ Finset.Icc 1 M,
        smoothWeight q Q * coefficientMajorant q /
          (q : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q)))) ≤
        C * (max 1 (Real.log Q)) ^ D := by
  obtain ⟨C, D, hC, hD, hb⟩ := frac_euler_product_bound
  refine ⟨C, D, hC, hD, ?_⟩
  intro Q M hQ
  have hV : (1 : ℝ) ≤ max 1 (Real.log Q) := le_max_left _ _
  have hs : 0 < 1 - 1 / (2 * max 1 (Real.log Q)) := by
    have hh : 1 / (2 * max 1 (Real.log Q)) ≤ (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  exact (smooth_moment_euler_bound Q M hQ _ hs).trans (hb Q hQ)

/-! ### Finite Rankin inequality (port of Decomp447b) -/

private theorem weighted_rankin_tail (w : ℕ → ℝ) (hw : ∀ q, 0 ≤ w q)
    (T δ : ℝ) (hT : 0 < T) (hδ : 0 ≤ δ) (M : ℕ) :
    (∑ q ∈ Finset.Ioc ⌊T⌋₊ M, w q / (q : ℝ)) ≤
      (∑ q ∈ Finset.Icc 1 M, w q / (q : ℝ) ^ (1 - δ)) / T ^ δ := by
  have hpow : 0 < T ^ δ := Real.rpow_pos_of_pos hT δ
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊T⌋₊ M, (w q / (q : ℝ) ^ (1 - δ)) / T ^ δ := by
      apply Finset.sum_le_sum
      intro q hq
      have hqT : T < (q : ℝ) := (Nat.floor_lt hT.le).mp (Finset.mem_Ioc.mp hq).1
      have hq0 : (0 : ℝ) < q := hT.trans hqT
      have hp : T ^ δ ≤ (q : ℝ) ^ δ := Real.rpow_le_rpow hT.le hqT.le hδ
      have he : (q : ℝ) ^ (1 - δ) * (q : ℝ) ^ δ = q := by
        rw [← Real.rpow_add hq0]
        simp
      calc
        _ = (w q / (q : ℝ) ^ (1 - δ)) / (q : ℝ) ^ δ := by
          rw [div_div, he]
        _ ≤ _ :=
          div_le_div_of_nonneg_left (div_nonneg (hw q) (Real.rpow_nonneg hq0.le _)) hpow hp
    _ = (∑ q ∈ Finset.Ioc ⌊T⌋₊ M, w q / (q : ℝ) ^ (1 - δ)) / T ^ δ := by
      rw [Finset.sum_div]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hpow.le
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Ioc.mp hq).1; omega,
          (Finset.mem_Ioc.mp hq).2⟩
      · intro q hq hn
        exact div_nonneg (hw q) (Real.rpow_nonneg (by positivity) _)

/-! ### Real parameter absorption (port of Rankin447) -/

private theorem rankin_parameter_absorption (D B ε : ℝ) (hD : 0 ≤ D)
    (hB : 0 < B) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (max 1 (Real.log Q)) ^ D /
        (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * max 1 (Real.log Q))) ≤
          C / Real.log x ^ B := by
  let η := min ε (1 / 2 : ℝ)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hηε : η ≤ ε := min_le_left _ _
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hDB : 0 < D + B := by linarith
  have hc : 0 < η / (6 * (D + B)) := by positivity
  obtain ⟨L0, hb⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_atTop hη).bound hc)
  refine ⟨1, max 2 (Real.exp (max L0 2)), by norm_num, le_max_left _ _, ?_⟩
  intro x y Q hx hy _hyx hQpos hQ
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hxpos : 0 < x := by linarith
  let L := Real.log x
  have hL : max L0 2 ≤ L := by
    apply (Real.le_log_iff_exp_le hxpos).mpr
    exact (le_max_right _ _).trans hx
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hlog : Real.log L ≤ η / (6 * (D + B)) * L ^ η := by
    have hh := hb L ((le_max_left _ _).trans hL)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL1),
      abs_of_pos (Real.rpow_pos_of_pos hLpos _)] using hh
  have hlogs : (D + B) * Real.log L ≤ η / 6 * L ^ η := by
    have hh := mul_le_mul_of_nonneg_left hlog hDB.le
    have he : (D + B) * (η / (6 * (D + B))) = η / 6 := by field_simp
    calc
      _ ≤ (D + B) * (η / (6 * (D + B)) * L ^ η) := hh
      _ = _ := by rw [← mul_assoc, he]
  let V := max 1 (Real.log Q)
  have hV1 : 1 ≤ V := le_max_left _ _
  have hVpos : 0 < V := by linarith
  have hV : V ≤ L ^ (1 - η) := by
    apply max_le
    · exact Real.one_le_rpow hL1 (by linarith)
    · have hlogQ : Real.log Q ≤ L ^ (1 - ε) :=
        (Real.log_le_iff_le_exp hQpos).mpr hQ
      exact hlogQ.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have hVL : V ≤ L := by
    calc
      _ ≤ L ^ (1 - η) := hV
      _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = L := Real.rpow_one L
  have hscale : V * L ^ η ≤ L := by
    calc
      _ ≤ L ^ (1 - η) * L ^ η :=
        mul_le_mul_of_nonneg_right hV (Real.rpow_nonneg hLpos.le _)
      _ = L := by rw [← Real.rpow_add hLpos]; simp
  have hypos : 0 < y := (Real.rpow_pos_of_pos hxpos ε).trans_le hy
  have hlogy : η * L ≤ Real.log y := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hxpos ε) hy
    rw [Real.log_rpow hxpos] at hh
    exact (mul_le_mul_of_nonneg_right hηε hLpos.le).trans hh
  have harg0 : η / 6 * L ^ η ≤ Real.log y / (6 * V) := by
    apply (le_div_iff₀ (by positivity : 0 < 6 * V)).mpr
    have hh := mul_le_mul_of_nonneg_left hscale hη.le
    nlinarith
  have hT : 0 < y ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hypos _
  have harg : Real.exp (η / 6 * L ^ η) ≤
      (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * V)) := by
    rw [Real.rpow_def_of_pos hT]
    apply Real.exp_le_exp.mpr
    rw [Real.log_rpow hypos]
    convert harg0 using 1 <;> ring
  have hnum : V ^ D * L ^ B ≤ Real.exp (η / 6 * L ^ η) := by
    calc
      _ ≤ L ^ D * L ^ B :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hVpos.le hVL hD)
          (Real.rpow_nonneg hLpos.le _)
      _ = L ^ (D + B) := (Real.rpow_add hLpos _ _).symm
      _ = Real.exp ((D + B) * Real.log L) := by
        rw [Real.rpow_def_of_pos hLpos]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hlogs
  change V ^ D / (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * V)) ≤ 1 / L ^ B
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hT _) (Real.rpow_pos_of_pos hLpos B)).mpr
  simpa only [one_mul] using hnum.trans harg

/-! ### The leaf -/

private theorem smooth_reciprocal_tail_proved (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (4 * smoothModulus Q),
        smoothWeight q Q * (coefficientMajorant q / (q : ℝ))) ≤
          C / Real.log x ^ (A / 2) := by
  obtain ⟨C, D, hC, hD, hm⟩ := smooth_fractional_moment
  obtain ⟨K, x0, hK, hx0, hk⟩ :=
    rankin_parameter_absorption D (A / 2) ε hD (by linarith) hε
  refine ⟨C * K, x0, mul_pos hC hK, hx0, ?_⟩
  intro x y Q hx hy hyx hQpos hQ
  have hxpos : (0 : ℝ) < x := by linarith
  have hT : 0 < y ^ (1 / 3 : ℝ) := by
    have hypos : 0 < y := (Real.rpow_pos_of_pos hxpos ε).trans_le hy
    exact Real.rpow_pos_of_pos hypos _
  have hδ : 0 ≤ 1 / (2 * max 1 (Real.log Q)) := by positivity
  have hw (q : ℕ) : 0 ≤ smoothWeight q Q * coefficientMajorant q := by
    have hsw : 0 ≤ smoothWeight q Q := by unfold smoothWeight; split <;> norm_num
    exact mul_nonneg hsw (by unfold coefficientMajorant; positivity)
  calc
    _ = ∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (4 * smoothModulus Q),
        (smoothWeight q Q * coefficientMajorant q) / (q : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ (∑ q ∈ Finset.Icc 1 (4 * smoothModulus Q),
        smoothWeight q Q * coefficientMajorant q /
          (q : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q)))) /
        (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * max 1 (Real.log Q))) :=
      weighted_rankin_tail _ hw _ _ hT hδ _
    _ ≤ (C * (max 1 (Real.log Q)) ^ D) /
        (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * max 1 (Real.log Q))) :=
      div_le_div_of_nonneg_right (hm Q _ hQpos) (by positivity)
    _ = C * ((max 1 (Real.log Q)) ^ D /
        (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * max 1 (Real.log Q)))) := by ring
    _ ≤ C * (K / Real.log x ^ (A / 2)) :=
      mul_le_mul_of_nonneg_left (hk x y Q hx hy hyx hQpos hQ) hC.le
    _ = _ := by ring

/-- LEAF. Page 14 below display 50, using Lemma 3.5 on page 12.
This is only a numerical weighted smooth reciprocal tail. There is no A3,
n, Euler product, series error or interval average. The proved conservative
majorant has one factor 64 per distinct prime divisor. -/
theorem smooth_reciprocal_tail (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (4 * smoothModulus Q),
        smoothWeight q Q * (coefficientMajorant q / (q : ℝ))) ≤
          C / Real.log x ^ (A / 2) := by
  exact smooth_reciprocal_tail_proved A ε hA hε

/-- Page 14 below display 50. The proved composite estimate bounds the
norm of the smooth coefficient tail by its numerical majorant. -/
theorem smooth_tail_norm (n : ℕ) (T Q : ℝ) :
    ‖∑ q ∈ Finset.Ioc ⌊T⌋₊ (4 * smoothModulus Q),
      (smoothWeight q Q : ℂ) * A3 n q‖ ≤
    ∑ q ∈ Finset.Ioc ⌊T⌋₊ (4 * smoothModulus Q),
      smoothWeight q Q * (coefficientMajorant q / (q : ℝ)) := by
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊T⌋₊ (4 * smoothModulus Q),
        ‖(smoothWeight q Q : ℂ) * A3 n q‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
      have hw : 0 ≤ smoothWeight q Q := by unfold smoothWeight; split <;> norm_num
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (coefficient_product_bound n q hqn) hw

/-- Page 14 below display 50. Exact Task438a pointwise tail statement.
CONDITIONAL only on the numerical smooth_reciprocal_tail leaf. -/
theorem smooth_tail_pointwise (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) → ∀ n : ℕ,
      ‖∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (4 * smoothModulus Q),
        (smoothWeight q Q : ℂ) * A3 n q‖ ^ 2 ≤
          C / Real.log x ^ A := by
  obtain ⟨C, x0, hC, hx0, hb⟩ := smooth_reciprocal_tail A ε hA hε
  refine ⟨C ^ 2, x0, by positivity, hx0, ?_⟩
  intro x y Q hx hy hyx hQpos hQ n
  have hx2 : 2 ≤ x := hx0.trans hx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  calc
    _ ≤ (C / Real.log x ^ (A / 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        ((smooth_tail_norm n _ Q).trans (hb x y Q hx hy hyx hQpos hQ)) 2
    _ = C ^ 2 / Real.log x ^ A := by
      have hp : (Real.log x ^ (A / 2)) ^ (2 : ℕ) = Real.log x ^ A := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]
        congr 1
        push_cast
        ring
      rw [div_pow, hp]

#print axioms smooth_reciprocal_tail
#print axioms smooth_tail_norm
#print axioms smooth_tail_pointwise

end LeanLab.KumchevLiu2007.Task438j
