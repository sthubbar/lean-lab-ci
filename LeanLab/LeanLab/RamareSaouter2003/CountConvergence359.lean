import LeanLab.RamareSaouter2003.Decomp359a
import LeanLab.RamareSaouter2003.Decomp359c
import LeanLab.RamareSaouter2003.Decomp290a

/-!
P0099 p. 14, Lemma 2, and p. 20, display 15.
The existing finite Lemma 2 bounds give convergence directly from Lemma 1.
Every result here is CONDITIONAL ON the explicit actual-count hypothesis.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.CountConvergence359
open Real Smooth L3Zeta L3Zeros Decomp290c

/-- P0099 p. 14, Lemma 2. CONDITIONAL ON the actual two-sided Lemma 1.
Mathlib turns the existing uniform nonnegative finite sum bounds into summability. -/
theorem reciprocal_tail_summable_of_count (hN : L1Zeta.Lemma1N) (m : ℕ) (hm : 1 ≤ m) :
    Summable (fun i : ZI => if (1000 : ℝ) < |gZ i| then
      1 / |gZ i| ^ (m + 1) else 0) := by
  apply summable_of_sum_le (c := L2 m 1000 / (1000 : ℝ) ^ m)
  · intro i
    change 0 ≤ if (1000 : ℝ) < |gZ i| then 1 / |gZ i| ^ (m + 1) else 0
    split_ifs <;> positivity
  · intro s
    simpa only [Finset.sum_filter] using
      lemma2_upper (L1Zeta.lemma1Count_zeta hN) hm (by norm_num : (1000 : ℝ) ≤ 1000) s

/-- P0099 pp. 14 and 20, Lemma 2 and display 15.
CONDITIONAL ON the actual Lemma 1. The critical strip bounds the numerator. -/
theorem weighted_tail_summable_of_count (hN : L1Zeta.Lemma1N) (m : ℕ) (X T : ℝ)
    (hm : 1 ≤ m) (hX : 1 ≤ X) (hT : 1000 ≤ T) :
    Summable (fun i : ZI => if T < |gZ i| then X ^ bZ i / |gZ i| ^ (m + 1) else 0) := by
  have ht := reciprocal_tail_summable_of_count hN m hm
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (ht.mul_left X)
  · change 0 ≤ if T < |gZ i| then X ^ bZ i / |gZ i| ^ (m + 1) else 0
    split_ifs <;> positivity
  · change (if T < |gZ i| then X ^ bZ i / |gZ i| ^ (m + 1) else 0) ≤
      X * (if (1000 : ℝ) < |gZ i| then 1 / |gZ i| ^ (m + 1) else 0)
    by_cases hi : T < |gZ i|
    · have h1000 : (1000 : ℝ) < |gZ i| := lt_of_le_of_lt hT hi
      simp only [if_pos hi, if_pos h1000]
      have hx : X ^ bZ i ≤ X := by
        calc _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (bZ_mem i).2
             _ = X := Real.rpow_one X
      convert div_le_div_of_nonneg_right hx (by positivity : 0 ≤ |gZ i| ^ (m + 1)) using 1 <;> ring
    · simp only [if_neg hi]
      split_ifs <;> positivity

/-- P0099 pp. 19 and 20, summability of the actual smoothed zero terms.
CONDITIONAL ON the actual Lemma 1. The near support and majorant are proved. -/
theorem zeroTerm_summable_of_count (hN : L1Zeta.Lemma1N) (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001) :
    Summable (zeroTerm m X u) := by
  classical
  obtain ⟨C, _, hC⟩ := Decomp359c.far_norm_majorant m X u hm hX hu hmu
  have ht := (reciprocal_tail_summable_of_count hN m (by omega)).mul_left C
  have hf : Summable (fun i : ZI => if (1000 : ℝ) < |gZ i| then zeroTerm m X u i else 0) :=
    Summable.of_norm_bounded ht hC
  have hn : Summable (fun i : ZI => if |gZ i| ≤ (1000 : ℝ) then zeroTerm m X u i else 0) :=
    summable_of_hasFiniteSupport (Decomp359a.near_support_finite m X u)
  convert hn.add hf using 1
  funext i
  by_cases hi : |gZ i| ≤ (1000 : ℝ)
  · simp [hi, not_lt.mpr hi]
  · simp [hi, lt_of_not_ge hi]

/-- P0099 p. 20, displays 14 and 15. Exactly the original far_sum_le target.
CONDITIONAL only on its explicit actual-count premise. No cited sorry is used. -/
theorem far_sum_le (hN : L1Zeta.Lemma1N) (m : ℕ) (X u T : ℝ)
    (hm : 2 ≤ m) (hX : 10 ^ 12 ≤ X) (hu : 0 < u)
    (hmu : (m : ℝ) * u ≤ 0.0001) (hT : 1000 ≤ T) :
    farSum m X u T ≤ (Real.exp u + 1) * (1 + m * u) ^ (m + 1) * muStar m *
      (∫ t in (0 : ℝ)..1, fm m t) / (m * u) ^ m * ZsF gZ bZ m T X := by
  let K := (Real.exp u + 1) * (1 + m * u) ^ (m + 1) * muStar m *
    (∫ t in (0 : ℝ)..1, fm m t) / (m * u) ^ m
  let W : ZI → ℝ := fun i => if T < |gZ i| then X ^ bZ i / |gZ i| ^ (m + 1) else 0
  let R : ZI → ℝ := fun i => if T < |gZ i| then (zeroTerm m X u i).re else 0
  have hW : Summable W := weighted_tail_summable_of_count hN m X T (by omega) (by linarith) hT
  have hδ : 0 < (m : ℝ) * u := by
    have : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    positivity
  have hbound (i : ZI) : ‖R i‖ ≤ K * W i := by
    by_cases hi : T < |gZ i|
    · have hγ : ((i.1 : ℂ)).im ≠ 0 := by
        change gZ i ≠ 0
        intro hh
        simp [hh] at hi
        linarith
      have hb := Decomp1531a.far_zero_term_le (bZ_mem i).1 (bZ_mem i).2 hγ hu.le hδ
        (by linarith : 0 < X) m
      change ‖if T < |gZ i| then (zeroTerm m X u i).re else 0‖ ≤
        K * (if T < |gZ i| then X ^ bZ i / |gZ i| ^ (m + 1) else 0)
      rw [if_pos hi, if_pos hi, Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm (zeroTerm m X u i)).trans hb
    · simp [R, W, hi]
  have hR : Summable R := Summable.of_norm_bounded (hW.mul_left K) hbound
  have hle : (∑' i, R i) ≤ ∑' i, K * W i :=
    hR.tsum_le_tsum (fun i => (le_abs_self (R i)).trans (by simpa [Real.norm_eq_abs] using hbound i))
      (hW.mul_left K)
  simpa only [R, W, K, farSum, ZsF, tsum_mul_left] using hle

/-- P0099 p. 14, the positive half of Lemma 2 at m = 1 and T = 1000.
CONDITIONAL ON the actual Lemma 1. Reflect a finite positive set and apply
the existing two-sided finite bound to the disjoint union. -/
theorem positive_square_partial_bound_of_count (hN : L1Zeta.Lemma1N) (s : Finset ZI) :
    (∑ i ∈ s, if (1000 : ℝ) < gZ i then 1 / (gZ i) ^ 2 else 0) ≤
      L2 1 1000 / (2 * 1000) := by
  classical
  let p := s.filter (fun i => (1000 : ℝ) < gZ i)
  let q := p.image σZ
  have hp (i : ZI) (hi : i ∈ p) : (1000 : ℝ) < gZ i := (Finset.mem_filter.mp hi).2
  have hq (i : ZI) (hi : i ∈ q) : gZ i < -1000 := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [L1Zeta.gZ_σ_neg]
    linarith [hp j hj]
  have hd : Disjoint p q := Finset.disjoint_left.mpr (by
    intro i hi hj
    linarith [hp i hi, hq i hj])
  have hall : (p ∪ q).filter (fun i => (1000 : ℝ) < |gZ i|) = p ∪ q := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (hp i hi).trans_le (le_abs_self _)
    · have hn := hq i hi
      rw [abs_of_neg (by linarith : gZ i < 0)]
      linarith
  have hb := lemma2_upper (L1Zeta.lemma1Count_zeta hN) (m := 1) (by norm_num)
    (T := 1000) (by norm_num) (p ∪ q)
  rw [hall, Finset.sum_union hd] at hb
  have hsp : (∑ i ∈ p, 1 / |gZ i| ^ (1 + 1)) = ∑ i ∈ p, 1 / (gZ i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_of_pos (by linarith [hp i hi] : 0 < gZ i)]
  have hsq : (∑ i ∈ q, 1 / |gZ i| ^ (1 + 1)) = ∑ i ∈ p, 1 / (gZ i) ^ 2 := by
    dsimp [q]
    rw [Finset.sum_image (fun _ _ _ _ hh => σZ_injective hh)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [gZ_σ, abs_of_pos (by linarith [hp i hi] : 0 < gZ i)]
  rw [hsp, hsq, pow_one] at hb
  have hsum : (∑ i ∈ s, if (1000 : ℝ) < gZ i then 1 / (gZ i) ^ 2 else 0) =
      ∑ i ∈ p, 1 / (gZ i) ^ 2 := by
    symm
    exact Finset.sum_filter _ _
  rw [hsum]
  linarith

end LeanLab.RamareSaouter2003.CountConvergence359

#print axioms LeanLab.RamareSaouter2003.CountConvergence359.reciprocal_tail_summable_of_count

#print axioms LeanLab.RamareSaouter2003.CountConvergence359.weighted_tail_summable_of_count

#print axioms LeanLab.RamareSaouter2003.CountConvergence359.zeroTerm_summable_of_count

#print axioms LeanLab.RamareSaouter2003.CountConvergence359.far_sum_le

#print axioms LeanLab.RamareSaouter2003.CountConvergence359.positive_square_partial_bound_of_count
