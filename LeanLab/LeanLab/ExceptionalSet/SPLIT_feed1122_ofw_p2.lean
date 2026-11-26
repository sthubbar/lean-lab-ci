import LeanLab.ExceptionalSet.SPLIT_leaf_arc_energy

/-!
Split, burst-20261122 p2 by CLOUD S149, of the leaf `leaf_ofw_short` of
`SPLIT_feed1122_leaf_arc_energy_offwindow.lean`, the odd frequencies `0 ≤ n ≤ X`, P0029
Bhowmik and Grimmelt 2026 with the arc model of P0083 Pintz 2026.  The same branch already splits
`leaf_ofw_high_tail` the same way in `SPLIT_feed1122_leaf_ofw_high_tail.lean`, CLOUD S132.

It is split by `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²` into the energy of the prime side alone and the energy of
the arc model alone.  The split is faithful: at odd `n` the paper bounds the two sides
separately, there is no main term cancellation between `R_Λ(n) e^{-n/X}` and `v_X(n)` there.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.BG2026.Decomp522a

open Finset Real MeasureTheory AddCircle
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.BG2026.Supply385

noncomputable section

/-- Pointwise `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²`, summed over an index set. -/
theorem p2_tsum_ind_norm_sub_sq_le (P : ℤ → Prop) [DecidablePred P] (a b : ℤ → ℂ)
    (ha : Summable (fun n => if P n then ‖a n‖ ^ 2 else 0))
    (hb : Summable (fun n => if P n then ‖b n‖ ^ 2 else 0)) :
    (∑' n, if P n then ‖a n - b n‖ ^ 2 else 0) ≤
      2 * (∑' n, if P n then ‖a n‖ ^ 2 else 0) + 2 * (∑' n, if P n then ‖b n‖ ^ 2 else 0) := by
  have hpt : ∀ n, (if P n then ‖a n - b n‖ ^ 2 else 0) ≤
      2 * (if P n then ‖a n‖ ^ 2 else 0) + 2 * (if P n then ‖b n‖ ^ 2 else 0) := by
    intro n
    split_ifs
    · have h1 := norm_sub_le (a n) (b n)
      have h2 : 0 ≤ ‖a n - b n‖ := norm_nonneg _
      have h3 : 0 ≤ ‖a n‖ := norm_nonneg _
      have h4 : 0 ≤ ‖b n‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖a n‖ - ‖b n‖)]
    · simp
  have hs : Summable (fun n => 2 * (if P n then ‖a n‖ ^ 2 else 0) +
      2 * (if P n then ‖b n‖ ^ 2 else 0)) := (ha.mul_left 2).add (hb.mul_left 2)
  have hl : Summable (fun n => if P n then ‖a n - b n‖ ^ 2 else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hpt hs
  calc (∑' n, if P n then ‖a n - b n‖ ^ 2 else 0)
      ≤ ∑' n, (2 * (if P n then ‖a n‖ ^ 2 else 0) + 2 * (if P n then ‖b n‖ ^ 2 else 0)) :=
        hl.tsum_le_tsum hpt hs
    _ = _ := by rw [(ha.mul_left 2).tsum_add (hb.mul_left 2), tsum_mul_left, tsum_mul_left]

/-- Parseval summability of the squared coefficients of an `L²` function on the circle. -/
theorem p2_summable_coeff_sq {f : AddCircle (1 : ℝ) → ℂ} (hf : MemLp f 2 haarAddCircle) :
    Summable (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) := by
  have hh := hasSum_sq_fourierCoeff (hf.toLp f)
  have hcoef : fourierCoeff ((hf.toLp f : Lp ℂ 2 haarAddCircle) : AddCircle (1 : ℝ) → ℂ) =
      fourierCoeff f := fourierCoeff_congr_ae (MemLp.coeFn_toLp hf)
  rw [hcoef] at hh
  exact hh.summable

theorem p2_summable_ind {P : ℤ → Prop} [DecidablePred P] {c : ℤ → ℝ} (hc : Summable c)
    (h0 : ∀ n, 0 ≤ c n) : Summable (fun n => if P n then c n else 0) :=
  Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp [h0])
    (fun n => by split_ifs <;> simp [h0]) hc

/-- The coefficient of the difference is the difference of the coefficients. -/
theorem p2_coeff_diff (X : ℕ) (hX : 0 < X) (n : ℤ) :
    fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n =
      fourierCoeff (fun t => FX X (X ^ 2) t ^ 2) n -
        fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  set W : AddCircle (1 : ℝ) → ℂ := Vfun X (Nat.sqrt X) (Nat.sqrt X) with hWdef
  have hW : MemLp W 2 haarAddCircle := memLp_Vfun hX0 _ _
  have hFX : MemLp (fun t => FX (X : ℝ) (X ^ 2) t ^ 2) 2 haarAddCircle :=
    memLp_FX_sq (X : ℝ) (X ^ 2)
  have hneg : fourierCoeff (-W) = -fourierCoeff W := by
    ext m
    have h := fourierCoeff.const_smul (T := (1 : ℝ)) W (-1) m
    simpa [neg_smul, one_smul] using h
  have hadd := fourierCoeff.add (T := (1 : ℝ))
    (f := fun t => FX X (X ^ 2) t ^ 2) (g := -W)
    (hFX.integrable one_le_two) (hW.integrable one_le_two).neg
  have heq : (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) =
      (fun t => FX X (X ^ 2) t ^ 2) + (-W) := by
    ext t
    simp [hWdef, sub_eq_add_neg]
  rw [heq, hadd, hneg, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]

section OcntCount
open ArithmeticFunction LeanLab.ExceptionalSet.PintzAlthofer2026

/-- An even prime power is a power of `2`. -/
theorem ocnt_eq_two_pow_of_even {u : ℕ} (hu : Λ u ≠ 0) (he : 2 ∣ u) : ∃ k, 2 ^ k = u := by
  rw [vonMangoldt_ne_zero_iff] at hu
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff u).mp hu
  have h2p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow he
  have : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm
  exact ⟨k, by rw [this]⟩

/-- At odd `m` a nonzero term of `R_Λ(m)` has a power of `2`, so `R_Λ(m) ≤ 2 (log₂ m + 1) (log m)²`. -/
theorem ocnt_RΛ_odd_le {m : ℕ} (hm : ¬ 2 ∣ m) :
    RΛ m ≤ 2 * ((Nat.log 2 m + 1 : ℕ) : ℝ) * Real.log m ^ 2 := by
  classical
  have hL : ∀ a ≤ m, Λ a ≤ Real.log m := by
    intro a ha
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0; simp; exact Real.log_natCast_nonneg m
    · exact vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast ha))
  have hlog0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  set A := (range (m + 1)).filter (fun u => ∃ k, 2 ^ k = u) with hA
  set B := (range (m + 1)).filter (fun u => ∃ k, 2 ^ k = m - u) with hB
  have hterm : ∀ u ∈ range (m + 1), Λ u * Λ (m - u) ≤
      (if u ∈ A then Real.log m ^ 2 else 0) + (if u ∈ B then Real.log m ^ 2 else 0) := by
    intro u hu
    have hum : u ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hu)
    by_cases h : Λ u * Λ (m - u) = 0
    · rw [h]; positivity
    · have hb : Λ u * Λ (m - u) ≤ Real.log m ^ 2 := by
        rw [sq]
        exact mul_le_mul (hL u hum) (hL (m - u) (Nat.sub_le m u)) vonMangoldt_nonneg hlog0
      have hu0 : Λ u ≠ 0 := left_ne_zero_of_mul h
      have hv0 : Λ (m - u) ≠ 0 := right_ne_zero_of_mul h
      rcases Nat.even_or_odd u with he | ho
      · have hA' : u ∈ A := by
          rw [hA, mem_filter]; exact ⟨hu, ocnt_eq_two_pow_of_even hu0 (even_iff_two_dvd.mp he)⟩
        rw [if_pos hA']; split_ifs <;> linarith [sq_nonneg (Real.log m)]
      · have hev : 2 ∣ m - u := by
          rcases ho with ⟨j, hj⟩
          omega
        have hB' : u ∈ B := by
          rw [hB, mem_filter]; exact ⟨hu, ocnt_eq_two_pow_of_even hv0 hev⟩
        rw [if_pos hB']; split_ifs <;> linarith [sq_nonneg (Real.log m)]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hAc : A.card ≤ Nat.log 2 m + 1 := by
    calc A.card ≤ ((range (Nat.log 2 m + 1)).image (fun k => 2 ^ k)).card := by
          apply card_le_card
          intro u hu
          rw [hA, mem_filter, mem_range] at hu
          obtain ⟨hum, k, rfl⟩ := hu
          rw [mem_image]
          refine ⟨k, ?_, rfl⟩
          rw [mem_range, Nat.lt_succ_iff]
          exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by omega)
      _ ≤ (range (Nat.log 2 m + 1)).card := card_image_le
      _ = _ := card_range _
  have hBc : B.card ≤ Nat.log 2 m + 1 := by
    calc B.card ≤ ((range (Nat.log 2 m + 1)).image (fun k => m - 2 ^ k)).card := by
          apply card_le_card
          intro u hu
          rw [hB, mem_filter, mem_range] at hu
          obtain ⟨hum, k, hk⟩ := hu
          rw [mem_image]
          refine ⟨k, ?_, by omega⟩
          rw [mem_range, Nat.lt_succ_iff]
          have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 2)
          exact (Nat.le_log_iff_pow_le (by norm_num) hm0).mpr (by omega)
      _ ≤ (range (Nat.log 2 m + 1)).card := card_image_le
      _ = _ := card_range _
  have hAi : (range (m + 1) ∩ A) = A := by
    rw [hA]; exact inter_eq_right.mpr (filter_subset _ _)
  have hBi : (range (m + 1) ∩ B) = B := by
    rw [hB]; exact inter_eq_right.mpr (filter_subset _ _)
  rw [hAi, hBi] at hsum
  have hAr : (A.card : ℝ) ≤ ((Nat.log 2 m + 1 : ℕ) : ℝ) := by exact_mod_cast hAc
  have hBr : (B.card : ℝ) ≤ ((Nat.log 2 m + 1 : ℕ) : ℝ) := by exact_mod_cast hBc
  unfold RΛ
  nlinarith [sq_nonneg (Real.log m)]


/-- At odd `m ≤ X`, `R_Λ(m)² ≤ 82944 (X^{1/4})⁶`. -/
theorem ocnt_RΛ_odd_sq_le {X m : ℕ} (hm : ¬ 2 ∣ m) (hmX : m ≤ X) :
    RΛ m ^ 2 ≤ 82944 * ((X : ℝ) ^ ((1 : ℝ) / 4)) ^ 6 := by
  have hm1 : 1 ≤ m := by rcases Nat.eq_zero_or_pos m with h | h
                         · subst h; exact absurd (dvd_zero 2) hm
                         · exact h
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_trans hm1 hmX
  set s := (X : ℝ) ^ ((1 : ℝ) / 4) with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow hX1 (by norm_num)
  have hlogX : Real.log X ≤ 4 * s := by
    have := Real.log_le_rpow_div (x := (X : ℝ)) (by linarith) (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [← hs] at this; linarith
  have hlm0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hlm : Real.log m ≤ 4 * s :=
    (Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmX)).trans hlogX
  have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hnl : ((Nat.log 2 m : ℕ) : ℝ) ≤ 2 * Real.log m := by
    have h2 : (2 : ℝ) ^ (Nat.log 2 m) ≤ m := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have := Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at this
    nlinarith
  have h := ocnt_RΛ_odd_le hm
  push_cast at h
  have h0 : 0 ≤ RΛ m := Finset.sum_nonneg fun _ _ =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
  have hb : RΛ m ≤ 288 * s ^ 3 := by
    have e1 : ((Nat.log 2 m : ℕ) : ℝ) + 1 ≤ 9 * s := by linarith
    have e2 : Real.log m ^ 2 ≤ 16 * s ^ 2 := by nlinarith
    have e3 : 0 ≤ ((Nat.log 2 m : ℕ) : ℝ) + 1 := by positivity
    calc RΛ m ≤ 2 * (((Nat.log 2 m : ℕ) : ℝ) + 1) * Real.log m ^ 2 := h
      _ ≤ 2 * (9 * s) * (16 * s ^ 2) := by gcongr
      _ = 288 * s ^ 3 := by ring
  calc RΛ m ^ 2 ≤ (288 * s ^ 3) ^ 2 := pow_le_pow_left₀ h0 hb 2
    _ = 82944 * s ^ 6 := by ring


end OcntCount

/-- LEAF: P0029, the prime side at odd frequencies `0 ≤ n ≤ X`.  An odd `n` is a sum of two prime
powers only with a power of `2`, so `R_Λ(n) ≪ log³ n` and the energy of `R_Λ(n) e^{-n/X}` over
odd `n ≤ X` is `O(X log⁶ X)`.  EASY: a divisibility count, no zero free input. -/
theorem leaf_ofw_short_count (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
          n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
        ‖((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
            Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ)‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  refine ⟨2 * 82944, by norm_num, 1, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  set s := (X : ℝ) ^ ((1 : ℝ) / 4) with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow hX1 (by norm_num)
  have hs4 : s ^ 4 = (X : ℝ) := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  set F : ℤ → ℝ := fun n => if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
          n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
        ‖((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
            Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ)‖ ^ 2
        else 0 with hF
  have hzero : ∀ n ∉ Finset.Icc (0 : ℤ) X, F n = 0 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    simp only [hF]
    rw [if_neg]; tauto
  have hpt : ∀ n ∈ Finset.Icc (0 : ℤ) X, F n ≤ 82944 * s ^ 6 := by
    intro n _
    simp only [hF]
    split_ifs with hc
    · obtain ⟨h0, hnX, hne⟩ := hc
      have hmX : n.toNat ≤ X := by omega
      have hodd : ¬ 2 ∣ n.toNat := by
        intro h2
        apply hne
        rw [mem_image]
        refine ⟨n.toNat, ?_, by omega⟩
        rw [mem_filter, mem_range]
        exact ⟨by omega, even_iff_two_dvd.mpr h2⟩
      have hb := ocnt_RΛ_odd_sq_le hodd hmX
      rw [← hs] at hb
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
      have he0 : 0 ≤ Real.exp (-(n.toNat : ℝ) / X) := (Real.exp_pos _).le
      have he1 : Real.exp (-(n.toNat : ℝ) / X) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact div_nonpos_of_nonpos_of_nonneg (by simp) (by positivity)
      have he2 : Real.exp (-(n.toNat : ℝ) / X) ^ 2 ≤ 1 := pow_le_one₀ he0 he1
      have hr0 : 0 ≤ LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat ^ 2 := sq_nonneg _
      nlinarith
    · positivity
  rw [tsum_eq_sum (s := Finset.Icc (0 : ℤ) X) hzero]
  have hsum := Finset.sum_le_card_nsmul _ _ _ hpt
  rw [Int.card_Icc, nsmul_eq_mul] at hsum
  have hcard : (((X : ℤ) + 1 - 0).toNat : ℝ) = (X : ℝ) + 1 := by
    rw [sub_zero, show ((X : ℤ) + 1) = ((X + 1 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
    push_cast; ring
  rw [hcard] at hsum
  have h10 : s ^ 10 = (X : ℝ) ^ ((5 : ℝ) / 2) := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hpow : (X : ℝ) ^ ((5 : ℝ) / 2) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hs6 : 0 ≤ s ^ 6 := by positivity
  calc ∑ n ∈ Finset.Icc (0 : ℤ) X, F n ≤ ((X : ℝ) + 1) * (82944 * s ^ 6) := hsum
    _ ≤ (2 * s ^ 4) * (82944 * s ^ 6) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity); rw [hs4]; linarith
    _ = 2 * 82944 * s ^ 10 := by ring
    _ ≤ 2 * 82944 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by rw [h10]; linarith


/-- LEAF: P0083 Pintz 2026 (4.14), the arc model at odd frequencies `0 ≤ n ≤ X`.  At odd `n` the
terms `q` and `2q`, `q` odd, cancel in the truncated singular series since `c_{2q}(n) = -c_q(n)`
and `φ(2q) = φ(q)`; only odd `q` with `Q/2 < q ≤ Q`, `Q = √X`, survive, giving `|v_X(n)| ≪ X^{1/2+ε}`
up to the arc truncation error, and energy `O(X^{2+2ε})` over odd `n ≤ X`.  MEDIUM: Ramanujan sum
bookkeeping in `fourierCoeff_Vfun` plus a bound on the cut arc integrals, no zero free input. -/
theorem leaf_ofw_short_model (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
          n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
        ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- Reduction of `leaf_ofw_short` to `leaf_ofw_short_count` and `leaf_ofw_short_model`. -/
theorem leaf_ofw_short_of_leaves (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
          n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
        ‖((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
            Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ) -
          fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  obtain ⟨C1, hC1, X1, h1⟩ := leaf_ofw_short_count Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C2, hC2, X2, h2⟩ := leaf_ofw_short_model Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨2 * C1 + 2 * C2, by positivity, X1 + X2 + 1, ?_⟩
  intro X hX
  have hXpos : 0 < X := by omega
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hXpos
  set P : ℤ → Prop := fun n => 0 ≤ n ∧ n ≤ (X : ℤ) ∧
    n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) with hP
  have hA : Summable (fun n : ℤ => if P n then
      ‖((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
          Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ)‖ ^ 2 else 0) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (0 : ℤ) X)
    intro n hn
    have : ¬ P n := by
      rintro ⟨h0, hle, _⟩
      exact hn (Finset.mem_Icc.mpr ⟨h0, hle⟩)
    simp [this]
  have hB := p2_summable_ind (P := P)
    (p2_summable_coeff_sq (memLp_Vfun hX0 (Nat.sqrt X : ℝ) (Nat.sqrt X)))
    (fun n => by positivity)
  have hle := p2_tsum_ind_norm_sub_sq_le P _ _ hA hB
  have e1 := h1 X (by omega)
  have e2 := h2 X (by omega)
  have hp : 0 ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by positivity
  nlinarith

end

end LeanLab.ExceptionalSet.BG2026.Decomp522a
