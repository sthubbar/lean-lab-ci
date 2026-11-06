import LeanLab.GoldbachAverage.Kernel402

/-!
BHMS, arXiv 1704.06103v2 page 6 Lemma 3 and page 19 high zero estimate.
The ported norm tail count is converted to an ordinate tail with threshold at least one.
Compact low zeros cover thresholds below six.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.TailCount402
open Finset
open LeanLab.PNTPort.Selberg LeanLab.PNTPort.ExplicitPsi1

/-- The norm to ordinate comparison used in the BHMS page 6 reciprocal square tail. -/
theorem reciprocal_square_comparison (ρ : ℂ) (hρ : NZ ρ) (hi : 1 ≤ |ρ.im|) :
    mz ρ / |ρ.im| ^ 2 ≤ 4 * (mz ρ / ‖ρ‖ ^ 2) := by
  have him : 0 < |ρ.im| := by linarith
  have hn0 : 0 < ‖ρ‖ := lt_of_lt_of_le him (Complex.abs_im_le_norm ρ)
  have hn := norm_le_of_NZ hρ
  have hnorm : ‖ρ‖ ≤ 2 * |ρ.im| := by linarith
  have hs := pow_le_pow_left₀ (norm_nonneg ρ) hnorm 2
  apply (div_le_iff₀ (by positivity : 0 < |ρ.im| ^ 2)).mpr
  have hm := mul_le_mul_of_nonneg_left hs (mz_nonneg ρ)
  have he : (4 * (mz ρ / ‖ρ‖ ^ 2) * |ρ.im| ^ 2) * ‖ρ‖ ^ 2 =
      4 * mz ρ * |ρ.im| ^ 2 := by field_simp
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < ‖ρ‖ ^ 2)).mp
  rw [he]
  nlinarith only [hm]

/-- The genuine zero ordinate reciprocal square tail in BHMS page 6 Lemma 3.
The threshold starts at one, as required in its page 19 application. -/
theorem reciprocal_ordinate_tail : ∃ D : ℝ, 0 ≤ D ∧
    ∀ T : ℝ, 1 ≤ T → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, NZ ρ ∧ T < |ρ.im|) →
      (∑ ρ ∈ S, mz ρ / |ρ.im| ^ 2) ≤ D * (Real.log T + 2) / T := by
  classical
  obtain ⟨C, hC, htail⟩ := tail_count
  obtain ⟨B, hB, hlow⟩ := sum_mz_low
  refine ⟨168 * B + 16 * C, by positivity, ?_⟩
  intro T hT S hS
  have hT0 : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlarge (R : ℝ) (hR : 6 ≤ R) (U : Finset ℂ)
      (hU : ∀ ρ ∈ U, NZ ρ ∧ R < |ρ.im|) :
      (∑ ρ ∈ U, mz ρ / |ρ.im| ^ 2) ≤ 4 * C * (Real.log R + 1) / R := by
    have ht := htail R hR U (by
      intro ρ hρ
      obtain ⟨hz, hi⟩ := hU ρ hρ
      exact ⟨hz.1, hz.2.1, hz.2.2, hi.trans_le (Complex.abs_im_le_norm ρ)⟩)
    have hs : (∑ ρ ∈ U, mz ρ / |ρ.im| ^ 2) ≤
        4 * ∑ ρ ∈ U, mz ρ / ‖ρ‖ ^ 2 := by
      rw [mul_sum]
      exact sum_le_sum (fun ρ hρ => reciprocal_square_comparison ρ (hU ρ hρ).1
        (by linarith [(hU ρ hρ).2]))
    have ht' : (∑ ρ ∈ U, mz ρ / ‖ρ‖ ^ 2) ≤ C * (Real.log R + 1) / R := ht
    calc _ ≤ 4 * ∑ ρ ∈ U, mz ρ / ‖ρ‖ ^ 2 := hs
      _ ≤ 4 * (C * (Real.log R + 1) / R) := by gcongr
      _ = _ := by ring
  by_cases h6 : 6 ≤ T
  · have ht := hlarge T h6 S hS
    have hc : 4 * C ≤ 168 * B + 16 * C := by linarith
    calc _ ≤ 4 * C * (Real.log T + 1) / T := ht
      _ ≤ (168 * B + 16 * C) * (Real.log T + 2) / T := by gcongr <;> linarith
  · let L := S.filter (fun ρ => |ρ.im| ≤ 6)
    let H := S.filter (fun ρ => ¬ |ρ.im| ≤ 6)
    have hl : (∑ ρ ∈ L, mz ρ / |ρ.im| ^ 2) ≤ 56 * B := by
      have hb := hlow 6 (by norm_num) L (by
        intro ρ hρ
        exact ⟨(hS ρ (mem_filter.mp hρ).1).1, (mem_filter.mp hρ).2⟩)
      have hs : (∑ ρ ∈ L, mz ρ / |ρ.im| ^ 2) ≤ ∑ ρ ∈ L, mz ρ := by
        apply sum_le_sum
        intro ρ hρ
        have hi : 1 ≤ |ρ.im| := le_trans hT (hS ρ (mem_filter.mp hρ).1).2.le
        apply div_le_self (mz_nonneg ρ)
        nlinarith
      norm_num at hb
      exact hs.trans hb
    have hh : (∑ ρ ∈ H, mz ρ / |ρ.im| ^ 2) ≤ 4 * C := by
      have ht := hlarge 6 (by norm_num) H (by
        intro ρ hρ
        exact ⟨(hS ρ (mem_filter.mp hρ).1).1, lt_of_not_ge (mem_filter.mp hρ).2⟩)
      have hlog6 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
      have hc := mul_le_mul_of_nonneg_left hlog6 hC
      nlinarith only [ht, hc]
    have hsplit := sum_filter_add_sum_filter_not S (fun ρ => |ρ.im| ≤ 6)
      (f := fun ρ => mz ρ / |ρ.im| ^ 2)
    have hmass : (∑ ρ ∈ S, mz ρ / |ρ.im| ^ 2) ≤ 56 * B + 4 * C := by
      change (∑ ρ ∈ L, mz ρ / |ρ.im| ^ 2) + (∑ ρ ∈ H, mz ρ / |ρ.im| ^ 2) = _ at hsplit
      linarith
    apply hmass.trans
    apply (le_div_iff₀ hT0).mpr
    have hmul := mul_le_mul_of_nonneg_left (show T ≤ 6 by linarith) (show 0 ≤ 56 * B + 4 * C by positivity)
    nlinarith [mul_nonneg hB hlog, mul_nonneg hC hlog]

/-- The asymmetric high zero pair bound in BHMS page 19 after the symmetry step.
The second zero range is enlarged to all ordinates of absolute value at most x. -/
theorem finite_high_pair_count : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x → ∀ U V : Finset ℂ,
      (∀ ρ ∈ U, NZ ρ ∧ x / h < |ρ.im|) →
      (∀ σ ∈ V, NZ σ ∧ |σ.im| ≤ x) →
      (∑ ρ ∈ U, (mz ρ / |ρ.im| ^ 2) *
        (∑ σ ∈ V, mz σ / (1 + |ρ.im - σ.im|))) ≤
        C * (h / x) * Real.log x ^ 4 := by
  obtain ⟨K, hK, hk⟩ := Kernel402.reciprocal_ordinate_sum
  obtain ⟨D, hD, hd⟩ := reciprocal_ordinate_tail
  refine ⟨10 * K * D, by positivity, ?_⟩
  intro x h hx hh hhx U V hU hV
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < h := by linarith
  have hT : 1 ≤ x / h := (le_div_iff₀ hh0).mpr (by simpa using hhx)
  have hlog : (1 : ℝ) / 2 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith
  have hlogT : Real.log (x / h) + 2 ≤ 5 * Real.log x := by
    have hTx : x / h ≤ x := div_le_self hx0.le (by linarith)
    have := Real.log_le_log (show 0 < x / h by positivity) hTx
    linarith
  have ht := hd (x / h) hT U hU
  have htail : (∑ ρ ∈ U, mz ρ / |ρ.im| ^ 2) ≤ 5 * D * (h / x) * Real.log x := by
    calc _ ≤ D * (Real.log (x / h) + 2) / (x / h) := ht
      _ ≤ D * (5 * Real.log x) / (x / h) := by gcongr
      _ = _ := by field_simp
  have hi (ρ : ℂ) : (∑ σ ∈ V, mz σ / (1 + |ρ.im - σ.im|)) ≤ K * Real.log x ^ 2 := by
    simpa only [abs_sub_comm] using hk x hx ρ.im V hV
  calc _ ≤ ∑ ρ ∈ U, (mz ρ / |ρ.im| ^ 2) * (K * Real.log x ^ 2) :=
      sum_le_sum (fun ρ _ => mul_le_mul_of_nonneg_left (hi ρ) (div_nonneg (mz_nonneg ρ) (sq_nonneg _)))
    _ = (∑ ρ ∈ U, mz ρ / |ρ.im| ^ 2) * (K * Real.log x ^ 2) := by rw [sum_mul]
    _ ≤ (5 * D * (h / x) * Real.log x) * (K * Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_right htail (by positivity)
    _ ≤ (10 * K * D) * (h / x) * Real.log x ^ 4 := by
      have hp : Real.log x ^ 3 ≤ 2 * Real.log x ^ 4 := by
        have hm := mul_le_mul_of_nonneg_right hlog (show 0 ≤ Real.log x ^ 3 by positivity)
        nlinarith only [hm]
      have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 5 * K * D * (h / x) by positivity)
      nlinarith only [hm]

end LeanLab.GoldbachAverage.TailCount402
