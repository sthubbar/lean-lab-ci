import LeanLab.GoldbachAverage.TruncatedRanges444
import LeanLab.GoldbachAverage.EndpointBounds239
import LeanLab.DERZ1997.Decomp1529b2

/-!
BHMS, https://arxiv.org/abs/1704.06103v2 page 7 Lemma 4 and page 17 difference step.
A uniform single endpoint formula leaves only the classical unsmoothed explicit formula open.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp444e
open MeasureTheory Complex
open Decomp287d TruncatedRanges444

open LeanLab.DERZ1997.Decomp1529a (zetaZeros zetaMult zetaZeros_finite one_le_zetaMult)

/-- The zero sets are monotone in the height. -/
private lemma zetaZeros_mono {T T' : ℝ} (h : T ≤ T') : zetaZeros T ⊆ zetaZeros T' :=
  fun _ hρ => ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans h⟩

private lemma zetaZeros_toFinset_mono {T T' : ℝ} (h : T ≤ T') :
    (zetaZeros_finite T).toFinset ⊆ (zetaZeros_finite T').toFinset :=
  Set.Finite.toFinset_subset_toFinset.mpr (zetaZeros_mono h)

/-- The single-endpoint truncated zero sum is a finite sum over the zeros with `|Im ρ| ≤ T`. -/
private lemma cutoffPrimitive_eq_finset {T u : ℝ} (hT : 0 ≤ T) :
    cutoffPrimitive T u =
      ∑ ρ ∈ (zetaZeros_finite T).toFinset, (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ := by
  classical
  obtain ⟨S, hS, hsum⟩ := cutoff_sum_finite T hT
  have h1 : cutoffPrimitive T u =
      ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * (u : ℂ) ^ ρ.1 / ρ.1 := by
    simpa only [cutoffPrimitive, mul_div_assoc] using hsum (fun ρ => (u : ℂ) ^ ρ / ρ)
  rw [h1]
  apply Finset.sum_bij (i := fun (ρ : NontrivialZero) (_ : ρ ∈ S) => ρ.1)
    (t := (zetaZeros_finite T).toFinset)
    (g := fun ρ => (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ)
  · intro a ha
    have h := (hS a).mp ha
    rw [Set.Finite.mem_toFinset]
    exact ⟨a.2.1, a.2.2.1, a.2.2.2, h⟩
  · intro a1 _ a2 _ he
    exact Subtype.ext he
  · intro b hb
    rw [Set.Finite.mem_toFinset] at hb
    exact ⟨⟨b, hb.1, hb.2.1, hb.2.2.1⟩, (hS _).mpr hb.2.2.2, rfl⟩
  · intro a ha
    have h := (hS a).mp ha
    show (analyticOrderNatAt riemannZeta a.1 : ℂ) * (u : ℂ) ^ a.1 / a.1
        = (zetaMult a.1 : ℂ) * (u : ℂ) ^ a.1 / a.1
    rw [zetaMult]

/-! ### Counting zeros in a window -/

open LeanLab.PNTPort.ZetaZeros in
private lemma zw_finite {t : ℝ} (ht : 3 ≤ |t|) : (ZW t).Finite := by
  apply (zetaZeros_finite (|t| + 1)).subset
  intro ρ hρ
  obtain ⟨hz, hre, him⟩ := hρ
  refine ⟨hz, by linarith, ?_, ?_⟩
  · exact lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hz)
  · calc |ρ.im| = |ρ.im - t + t| := by rw [sub_add_cancel]
      _ ≤ |ρ.im - t| + |t| := abs_add_le (ρ.im - t) t
      _ ≤ 2 / 5 + |t| := by linarith
      _ ≤ |t| + 1 := by linarith

open LeanLab.PNTPort.ZetaZeros in
private lemma zw_count_add :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 3 ≤ |t| → ∀ hfin : (ZW t).Finite,
      (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        (1 / Real.log (29 / 22)) * Real.log |t| + B := by
  classical
  refine ⟨|Real.log (41 / m0)| / Real.log (29 / 22), by positivity, fun t ht hfin => ?_⟩
  have hl22 : 0 < Real.log (29 / 22) := Real.log_pos (by norm_num)
  have hfinZ := finiteSetOfZeros_mono (by norm_num : (11 / 15 : ℝ) < 1) (fz_finite_zeros ht)
  have hinj : Set.InjOn (affInv t) (hfin.toFinset : Set ℂ) := by
    intro a _ b _ hab
    have h := congr_arg (aff t) hab
    rwa [aff_affInv, aff_affInv] at h
  have hsub : hfin.toFinset.image (affInv t) ⊆ hfinZ.toFinset := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨ρ, hρ, rfl⟩ := hz
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    exact affInv_mem ht hρ
  have hsum : (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) =
      ∑ z ∈ hfin.toFinset.image (affInv t), (analyticOrderNatAt (fz t) z : ℝ) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    have hm := (affInv_mem ht hρ).1
    rw [ord_fz ht (by linarith), aff_affInv]
  rw [hsum]
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)).trans ?_
  refine (fz_count ht).trans ?_
  have ht0 : 0 < |t| := by linarith
  have hm0 := m0_pos
  have hB : Real.log (Bz t) ≤ Real.log |t| + |Real.log (41 / m0)| := by
    have h1 : Bz t ≤ |t| * (41 / m0) := by
      unfold Bz
      rw [div_le_iff₀ hm0]
      field_simp
      linarith
    have hBpos : 0 < Bz t := by unfold Bz; exact div_pos (by positivity) hm0
    calc Real.log (Bz t) ≤ Real.log (|t| * (41 / m0)) := Real.log_le_log hBpos h1
      _ = Real.log |t| + Real.log (41 / m0) := Real.log_mul ht0.ne' (by positivity)
      _ ≤ Real.log |t| + |Real.log (41 / m0)| := by
          gcongr
          exact le_abs_self _
  rw [div_le_iff₀ hl22]
  have he : (1 / Real.log (29 / 22) * Real.log |t| + |Real.log (41 / m0)| / Real.log (29 / 22))
      * Real.log (29 / 22) = Real.log |t| + |Real.log (41 / m0)| := by
    field_simp
  rw [he]
  exact hB

open LeanLab.PNTPort.ZetaZeros in
private lemma za_count_add :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 3 ≤ |t| → ∃ hfin : (ZA t).Finite,
      (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        (2 / Real.log (29 / 22)) * Real.log |t| + B := by
  classical
  obtain ⟨B, hB, hW⟩ := zw_count_add
  refine ⟨2 * B, by positivity, fun t ht => ?_⟩
  have ht' : 3 ≤ |-t| := by rwa [abs_neg]
  have hfW : (ZW t).Finite := zw_finite ht
  have hfW' : (ZW (-t)).Finite := zw_finite ht'
  have hWa := hW t ht hfW
  have hWb := hW (-t) ht' hfW'
  rw [abs_neg] at hWb
  have hfL : (ZL t).Finite := by
    apply (hfW'.image (fun z => 1 - z)).subset
    intro ρ hρ
    exact ⟨1 - ρ, ZL_map ht hρ, by ring⟩
  have hfA : (ZA t).Finite := by rw [ZA_eq]; exact hfW.union hfL
  refine ⟨hfA, ?_⟩
  have hsplit : hfA.toFinset ⊆ hfW.toFinset ∪ hfL.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset, ZA_eq, Set.mem_union] at hρ
    rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact hρ
  have hL : (∑ ρ ∈ hfL.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
      (1 / Real.log (29 / 22)) * Real.log |t| + B := by
    have hinj : Set.InjOn (fun z : ℂ => 1 - z) (hfL.toFinset : Set ℂ) := by
      intro a _ b _ hab
      simpa using hab
    have hsubB : hfL.toFinset.image (fun z : ℂ => 1 - z) ⊆ hfW'.toFinset := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨ρ, hρ, rfl⟩ := hz
      rw [Set.Finite.mem_toFinset] at hρ ⊢
      exact ZL_map ht hρ
    have heq : (∑ ρ ∈ hfL.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) =
        ∑ z ∈ hfL.toFinset.image (fun z : ℂ => 1 - z),
          (analyticOrderNatAt riemannZeta z : ℝ) := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [Set.Finite.mem_toFinset] at hρ
      have h0 := ZL_re_pos ht hρ
      rw [ord_one_sub h0 (by linarith [hρ.2.1])]
    rw [heq]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsubB (fun _ _ _ => Nat.cast_nonneg _)).trans hWb
  calc (∑ ρ ∈ hfA.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ))
      ≤ ∑ ρ ∈ hfW.toFinset ∪ hfL.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsplit (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ (∑ ρ ∈ hfW.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) +
        ∑ ρ ∈ hfL.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
        have hu := Finset.sum_union_inter (s₁ := hfW.toFinset) (s₂ := hfL.toFinset)
          (f := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ))
        have hi : 0 ≤ ∑ ρ ∈ hfW.toFinset ∩ hfL.toFinset,
            (analyticOrderNatAt riemannZeta ρ : ℝ) :=
          Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
        linarith
    _ ≤ ((1 / Real.log (29 / 22)) * Real.log |t| + B) +
        ((1 / Real.log (29 / 22)) * Real.log |t| + B) := add_le_add hWa hL
    _ = (2 / Real.log (29 / 22)) * Real.log |t| + 2 * B := by
        field_simp
        ring

/-! ### A height separated from all zero ordinates -/

open LeanLab.PNTPort.ZetaZeros in
/-- For large `x` there is `H ∈ [x - 1/2, x]` whose distance to every zero ordinate below
`H + 1` is at least `1/(100 log H)`. -/
private lemma exists_good_height {A B : ℝ} (hA : 0 < A) (hA10 : A ≤ 10) (hB : 0 ≤ B)
    (hcnt : ∀ t : ℝ, 3 ≤ |t| → ∃ hfin : (ZA t).Finite,
      (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ A * Real.log |t| + B)
    {x : ℝ} (hx : Real.exp (2 * B + 16) ≤ x) :
    ∃ H ∈ Set.Icc (x - 1 / 2) x,
      ∀ ρ ∈ zetaZeros (H + 1), 1 / (100 * Real.log H) ≤ |ρ.im - H| := by
  classical
  have hexp2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hxlog : 2 * B + 16 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos (2 * B + 16)) hx
    rwa [Real.log_exp] at h
  have hx4 : 4 ≤ x := by
    have h1 : Real.exp 3 ≤ Real.exp (2 * B + 16) :=
      Real.exp_le_exp.mpr (show (3 : ℝ) ≤ 2 * B + 16 by linarith)
    have h2 : (4 : ℝ) ≤ Real.exp 3 := by
      have h3 := Real.add_one_le_exp (3 : ℝ)
      linarith
    linarith
  set r : ℝ := 1 / (100 * Real.log (x - 1 / 2)) with hr
  have hhalf3 : 3 ≤ x - 1 / 2 := by linarith
  have hloghalf : Real.log (x - 1 / 2) ≥ Real.log x - 1 := by
    have h1 : Real.log (x / 2) ≤ Real.log (x - 1 / 2) := by
      apply Real.log_le_log (by linarith)
      linarith
    rw [Real.log_div hxpos.ne' (by norm_num)] at h1
    linarith [Real.log_two_lt_d9]
  have hloghalfpos : 0 < Real.log (x - 1 / 2) := by linarith
  have h100 : 0 < 100 * Real.log (x - 1 / 2) := by linarith
  have hr0 : 0 < r := by rw [hr]; exact div_pos one_pos h100
  have hr1 : r ≤ 1 / 10 := by
    rw [hr, div_le_iff₀ (by positivity)]
    nlinarith
  set Zf : Finset ℂ := (zetaZeros_finite (x + 1)).toFinset.filter
    (fun ρ => x - 3 / 5 ≤ ρ.im ∧ ρ.im ≤ x + 1 / 10) with hZf
  have hZcount : (∑ ρ ∈ Zf, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
      2 * (A * Real.log (x + 1) + B) := by
    obtain ⟨hf1, hb1⟩ := hcnt (x - 1 / 4) (by
      rw [abs_of_pos (by linarith)]; linarith)
    have hsub1 : Zf ⊆ hf1.toFinset := by
      intro ρ hρ
      rw [hZf, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
      obtain ⟨hρz, h1, h2⟩ := hρ
      rw [Set.Finite.mem_toFinset]
      refine ⟨hρz.1, ?_⟩
      rw [abs_le]
      constructor <;> linarith
    have h1' : (∑ ρ ∈ Zf, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        A * Real.log |x - 1 / 4| + B :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub1
        (fun _ _ _ => Nat.cast_nonneg _)).trans hb1
    have h2' : A * Real.log |x - 1 / 4| + B ≤ A * Real.log (x + 1) + B := by
      rw [abs_of_pos (by linarith : (0:ℝ) < x - 1 / 4)]
      have hle : Real.log (x - 1 / 4) ≤ Real.log (x + 1) :=
        Real.log_le_log (by linarith) (by linarith)
      nlinarith
    have hnn : 0 ≤ A * Real.log (x + 1) + B := by
      have h1 : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
      nlinarith
    linarith
  have hcard : (Zf.card : ℝ) ≤ 2 * (A * Real.log (x + 1) + B) := by
    refine le_trans ?_ hZcount
    calc (Zf.card : ℝ) = ∑ ρ ∈ Zf, (1 : ℝ) := by simp
      _ ≤ ∑ ρ ∈ Zf, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          rw [hZf, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
          exact_mod_cast one_le_zetaMult hρ.1
  by_contra hcon
  push_neg at hcon
  have hcov : Set.Icc (x - 1 / 2) x ⊆
      ⋃ i : ↥Zf, Set.Ioo ((i : ℂ).im - r) ((i : ℂ).im + r) := by
    intro H hHI
    have hH1 : x - 1 / 2 ≤ H := hHI.1
    have hH2 : H ≤ x := hHI.2
    obtain ⟨ρ, hρz, hρd⟩ := hcon H hHI
    have hlogH : Real.log (x - 1 / 2) ≤ Real.log H :=
      Real.log_le_log (by linarith) hH1
    have hrH : 1 / (100 * Real.log H) ≤ r := by
      rw [hr, div_le_div_iff₀ (by linarith) h100]
      nlinarith
    have hd : |ρ.im - H| < r := lt_of_lt_of_le hρd hrH
    have hd' := abs_lt.mp hd
    have him1 : x - 3 / 5 ≤ ρ.im := by linarith
    have him2 : ρ.im ≤ x + 1 / 10 := by linarith
    have him0 : ρ.im ≠ 0 := by linarith
    obtain ⟨hzlo, hzhi⟩ := abs_le.mp hρz.2.2.2
    have hmem : ρ ∈ Zf := by
      rw [hZf, Finset.mem_filter, Set.Finite.mem_toFinset]
      refine ⟨⟨hρz.1, ?_, ?_, ?_⟩, him1, him2⟩
      · by_contra hneg
        exact zeta_ne_zero_of_re_nonpos (le_of_not_gt hneg) him0 hρz.1
      · exact lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hρz.1)
      · rw [abs_le]
        constructor <;> linarith
    refine Set.mem_iUnion.mpr ⟨⟨ρ, hmem⟩, ?_⟩
    rw [Set.mem_Ioo]
    constructor <;> linarith
  have hvol : ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal ((Zf.card : ℝ) * (2 * r)) := by
    have h1 : volume (Set.Icc (x - 1 / 2) x) ≤
        volume (⋃ i : ↥Zf, Set.Ioo ((i : ℂ).im - r) ((i : ℂ).im + r)) :=
      measure_mono hcov
    have h2 : volume (⋃ i : ↥Zf, Set.Ioo ((i : ℂ).im - r) ((i : ℂ).im + r)) ≤
        ∑' i : ↥Zf, volume (Set.Ioo ((i : ℂ).im - r) ((i : ℂ).im + r)) :=
      measure_iUnion_le _
    have h3 : (∑' i : ↥Zf, volume (Set.Ioo ((i : ℂ).im - r) ((i : ℂ).im + r)))
        = ENNReal.ofReal ((Zf.card : ℝ) * (2 * r)) := by
      rw [tsum_fintype]
      have hvi : ∀ i : ↥Zf, volume (Set.Ioo ((i : ℂ).im - r) ((i : ℂ).im + r))
          = ENNReal.ofReal (2 * r) := by
        intro i
        rw [Real.volume_Ioo]
        congr 1
        ring
      simp only [hvi, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast]
      rw [← ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal (1 / 2) = volume (Set.Icc (x - 1 / 2) x) := by
          rw [Real.volume_Icc]
          congr 1
          ring
      _ ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := h3
  have hkey : (1 / 2 : ℝ) ≤ (Zf.card : ℝ) * (2 * r) := by
    rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hvol
  have hbound : (Zf.card : ℝ) * (2 * r) ≤ (2 * (A * Real.log (x + 1) + B)) * (2 * r) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  have hlt : (2 * (A * Real.log (x + 1) + B)) * (2 * r) < 1 / 2 := by
    rw [hr]
    have he : (2 * (A * Real.log (x + 1) + B)) * (2 * (1 / (100 * Real.log (x - 1 / 2))))
        = 4 * (A * Real.log (x + 1) + B) / (100 * Real.log (x - 1 / 2)) := by
      field_simp
      ring
    rw [he, div_lt_iff₀ (by positivity)]
    have hlogx1 : Real.log (x + 1) ≤ Real.log x + 1 := by
      have h1 : Real.log (x + 1) ≤ Real.log (2 * x) :=
        Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) hxpos.ne'] at h1
      linarith [Real.log_two_lt_d9]
    have hAL : A * Real.log (x + 1) ≤ 10 * (Real.log x + 1) := by
      have h1 : A * Real.log (x + 1) ≤ A * (Real.log x + 1) :=
        mul_le_mul_of_nonneg_left hlogx1 (le_of_lt hA)
      have h2 : A * (Real.log x + 1) ≤ 10 * (Real.log x + 1) :=
        mul_le_mul_of_nonneg_right hA10 (by linarith)
      linarith
    have h4B : 4 * B ≤ 2 * Real.log x - 32 := by linarith
    nlinarith [hAL, h4B, hB, hxlog]
  linarith

/-! ### The endpoint bound -/

set_option maxHeartbeats 2000000 in
open LeanLab.PNTPort.ZetaZeros in
private theorem endpoint_main : ∃ A : ℂ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x u : ℝ,
    2 ≤ x → u ∈ Set.Icc x (3 * x) →
      ‖((Chebyshev.psi u - u : ℝ) : ℂ) + cutoffPrimitive x u - A‖ ≤ C * Real.log x ^ 2 := by
  classical
  obtain ⟨C1, hC1⟩ := LeanLab.DERZ1997.Decomp1529b2.explicit_formula_good266
  obtain ⟨B2, hB2, hcnt⟩ := za_count_add
  set A2 : ℝ := 2 / Real.log (29 / 22) with hA2def
  have hlog22 : 0 < Real.log (29 / 22) := Real.log_pos (by norm_num)
  have hA2 : 0 < A2 := by rw [hA2def]; positivity
  have hA2le : A2 ≤ 10 := by
    have hl : (1 : ℝ) / 5 ≤ Real.log (29 / 22) := by
      have h1 : 1 - (29 / 22)⁻¹ ≤ Real.log (29 / 22) :=
        Real.one_sub_inv_le_log_of_pos (by norm_num)
      have h2 : (1 : ℝ) - (29 / 22)⁻¹ = 7 / 29 := by norm_num
      rw [h2] at h1
      linarith
    rw [hA2def, div_le_iff₀ hlog22]
    linarith
  set T0 : ℝ := Real.exp (2 * B2 + 16) with hT0
  have hT0pos : 0 < T0 := Real.exp_pos _
  have hT0ge4 : 4 ≤ T0 := by
    have h1 : Real.exp 3 ≤ Real.exp (2 * B2 + 16) :=
      Real.exp_le_exp.mpr (show (3 : ℝ) ≤ 2 * B2 + 16 by linarith)
    have h2 : (4 : ℝ) ≤ Real.exp 3 := by
      have h3 := Real.add_one_le_exp (3 : ℝ)
      linarith
    rw [hT0]
    linarith
  set M : ℝ := (Real.log 4 + 5) * (3 * T0) + 3 * T0 * (∑ ρ ∈ (zetaZeros_finite T0).toFinset,
      (zetaMult ρ : ℝ) / ‖ρ‖) with hM
  have hMnn : 0 ≤ M := by
    rw [hM]
    have h1 : 0 ≤ ∑ ρ ∈ (zetaZeros_finite T0).toFinset, (zetaMult ρ : ℝ) / ‖ρ‖ :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have h2 : 0 ≤ 3 * T0 := by positivity
    have h3 : 0 ≤ 3 * T0 * (∑ ρ ∈ (zetaZeros_finite T0).toFinset, (zetaMult ρ : ℝ) / ‖ρ‖) :=
      mul_nonneg h2 h1
    have h4 : 0 ≤ (Real.log 4 + 5) * (3 * T0) := by positivity
    linarith
  set Cbig : ℝ := 1000 * (A2 + B2 + |C1| + 1) with hCbig
  have hCbignn : 0 ≤ Cbig := by rw [hCbig]; positivity
  refine ⟨0, max (M / (Real.log 2) ^ 2 + 1) Cbig, ?_, ?_⟩
  · have h1 : 0 ≤ M / (Real.log 2) ^ 2 := by positivity
    have : (0:ℝ) ≤ M / (Real.log 2) ^ 2 + 1 := by linarith
    exact le_trans this (le_max_left _ _)
  intro x u hx hu
  have hx0 : 0 < x := by linarith
  have hu2 : 2 ≤ u := le_trans hx hu.1
  have hu0 : 0 < u := by linarith
  have hlogx2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogxpos : 0 < Real.log x := by linarith
  have hcp : cutoffPrimitive x u =
      ∑ ρ ∈ (zetaZeros_finite x).toFinset, (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ :=
    cutoffPrimitive_eq_finset hx0.le
  by_cases hsmall : x ≤ T0
  · -- the crude range
    have hu3 : u ≤ 3 * T0 := by linarith [hu.2]
    have hpsi_nn : 0 ≤ Chebyshev.psi u := by
      unfold Chebyshev.psi
      exact Finset.sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)
    have hpsi_le : Chebyshev.psi u ≤ (Real.log 4 + 4) * u :=
      Chebyshev.psi_le_const_mul_self hu0.le
    have hpsi : |Chebyshev.psi u - u| ≤ (Real.log 4 + 5) * (3 * T0) := by
      have h1 : Chebyshev.psi u - u ≤ (Real.log 4 + 5) * u := by
        nlinarith
      have h2 : u - Chebyshev.psi u ≤ (Real.log 4 + 5) * u := by
        have h3 : 0 ≤ (Real.log 4 + 4) * u := by positivity
        nlinarith
      rw [abs_le]
      constructor <;> nlinarith
    have hterm_le : ∀ ρ ∈ (zetaZeros_finite x).toFinset,
        ‖(zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ‖ ≤ u * ((zetaMult ρ : ℝ) / ‖ρ‖) := by
      intro ρ hρ
      rw [Set.Finite.mem_toFinset] at hρ
      have hnorm : ‖(u : ℂ) ^ ρ‖ = u ^ ρ.re := Complex.norm_cpow_eq_rpow_re_of_pos hu0 ρ
      have hrpow : u ^ ρ.re ≤ u := by
        have h1 : u ^ ρ.re ≤ u ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ u) hρ.2.2.1.le
        simpa using h1
      have hmul : ‖(zetaMult ρ : ℂ)‖ = (zetaMult ρ : ℝ) := by
        first
        | rw [Complex.norm_natCast]
        | rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Nat.cast_nonneg _)]
      have hm0 : (0 : ℝ) ≤ (zetaMult ρ : ℝ) := Nat.cast_nonneg _
      calc ‖(zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ‖
          = ‖(zetaMult ρ : ℂ)‖ * ‖(u : ℂ) ^ ρ‖ / ‖ρ‖ := by rw [norm_div, norm_mul]
        _ = (zetaMult ρ : ℝ) * u ^ ρ.re / ‖ρ‖ := by rw [hnorm, hmul]
        _ ≤ (zetaMult ρ : ℝ) * u / ‖ρ‖ := by
            have h0 : (0 : ℝ) < ‖ρ‖ := by
              have h1 := Complex.abs_re_le_norm ρ
              rw [abs_of_pos hρ.2.1] at h1
              have hre : (0 : ℝ) < ρ.re := hρ.2.1
              linarith
            gcongr
        _ = u * ((zetaMult ρ : ℝ) / ‖ρ‖) := by ring
    have hS : ‖cutoffPrimitive x u‖ ≤
        3 * T0 * (∑ ρ ∈ (zetaZeros_finite T0).toFinset, (zetaMult ρ : ℝ) / ‖ρ‖) := by
      rw [hcp]
      have hsum1 : (∑ ρ ∈ (zetaZeros_finite x).toFinset,
            (zetaMult ρ : ℝ) / ‖ρ‖) ≤
          ∑ ρ ∈ (zetaZeros_finite T0).toFinset, (zetaMult ρ : ℝ) / ‖ρ‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (zetaZeros_toFinset_mono hsmall)
        intro _ _ _
        positivity
      calc ‖∑ ρ ∈ (zetaZeros_finite x).toFinset, (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ‖
          ≤ ∑ ρ ∈ (zetaZeros_finite x).toFinset,
              ‖(zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ‖ := norm_sum_le _ _
        _ ≤ ∑ ρ ∈ (zetaZeros_finite x).toFinset, u * ((zetaMult ρ : ℝ) / ‖ρ‖) :=
            Finset.sum_le_sum hterm_le
        _ = u * ∑ ρ ∈ (zetaZeros_finite x).toFinset, (zetaMult ρ : ℝ) / ‖ρ‖ := by
            rw [Finset.mul_sum]
        _ ≤ 3 * T0 * ∑ ρ ∈ (zetaZeros_finite x).toFinset, (zetaMult ρ : ℝ) / ‖ρ‖ := by
            have h0 : 0 ≤ ∑ ρ ∈ (zetaZeros_finite x).toFinset, (zetaMult ρ : ℝ) / ‖ρ‖ :=
              Finset.sum_nonneg (fun _ _ => by positivity)
            nlinarith
        _ ≤ 3 * T0 * ∑ ρ ∈ (zetaZeros_finite T0).toFinset, (zetaMult ρ : ℝ) / ‖ρ‖ := by
            have h0 : 0 ≤ 3 * T0 := by positivity
            exact mul_le_mul_of_nonneg_left hsum1 h0
    have hE : ‖((Chebyshev.psi u - u : ℝ) : ℂ) + cutoffPrimitive x u‖ ≤ M := by
      calc ‖((Chebyshev.psi u - u : ℝ) : ℂ) + cutoffPrimitive x u‖
          ≤ ‖((Chebyshev.psi u - u : ℝ) : ℂ)‖ + ‖cutoffPrimitive x u‖ := norm_add_le _ _
        _ = |Chebyshev.psi u - u| + ‖cutoffPrimitive x u‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (Real.log 4 + 5) * (3 * T0) +
              3 * T0 * (∑ ρ ∈ (zetaZeros_finite T0).toFinset, (zetaMult ρ : ℝ) / ‖ρ‖) :=
            add_le_add hpsi hS
        _ = M := by rw [hM]
    rw [sub_zero]
    refine le_trans hE ?_
    have hstep : M ≤ (M / (Real.log 2) ^ 2 + 1) * (Real.log x) ^ 2 := by
      have h1 : M = (M / (Real.log 2) ^ 2) * (Real.log 2) ^ 2 := by
        field_simp
      have h2 : (Real.log 2) ^ 2 ≤ (Real.log x) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt hlog2pos) hlogx2 2
      have h3 : 0 ≤ M / (Real.log 2) ^ 2 := by positivity
      calc M = (M / (Real.log 2) ^ 2) * (Real.log 2) ^ 2 := h1
        _ ≤ (M / (Real.log 2) ^ 2) * (Real.log x) ^ 2 := by gcongr
        _ ≤ (M / (Real.log 2) ^ 2 + 1) * (Real.log x) ^ 2 := by
            apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    exact le_trans hstep (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · -- the main range
    push_neg at hsmall
    obtain ⟨H, hHI, hHgood⟩ := exists_good_height hA2 hA2le hB2 hcnt (le_of_lt hsmall)
    have hHlo : x - 1 / 2 ≤ H := hHI.1
    have hHhi : H ≤ x := hHI.2
    have hHge2 : 2 ≤ H := by linarith
    have hHpos : 0 < H := by linarith
    have hHhalf : x / 2 ≤ H := by linarith
    have hHle : H ≤ u := le_trans hHhi hu.1
    have hx3' : (3 : ℝ) ≤ x := by linarith
    have hxlog16 : 16 ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos (2 * B2 + 16)) (le_of_lt hsmall)
      rw [Real.log_exp] at h
      linarith
    have hlogx1 : 1 ≤ Real.log x := by linarith
    have hexp := hC1 u H hu2 hHge2 hHle hHgood (zetaZeros_finite H)
    have hcast : ((Chebyshev.psi u - u : ℝ) : ℂ) = (Chebyshev.psi u : ℂ) - (u : ℂ) := by
      push_cast
      ring
    have hdiff : cutoffPrimitive x u -
        (∑ ρ ∈ (zetaZeros_finite H).toFinset, (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ) =
        ∑ ρ ∈ (zetaZeros_finite x).toFinset,
          (if ρ ∈ (zetaZeros_finite H).toFinset then 0 else (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ) := by
      rw [hcp]
      have hsub : (zetaZeros_finite H).toFinset ⊆ (zetaZeros_finite x).toFinset :=
        zetaZeros_toFinset_mono hHhi
      have h2 : (∑ ρ ∈ (zetaZeros_finite H).toFinset, (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ) =
          ∑ ρ ∈ (zetaZeros_finite x).toFinset,
            (if ρ ∈ (zetaZeros_finite H).toFinset then (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ else 0) := by
        rw [← Finset.sum_subset hsub
          (f := fun ρ => if ρ ∈ (zetaZeros_finite H).toFinset then
            (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ else 0)
          (fun x' _ hx'not => by rw [if_neg hx'not])]
        apply Finset.sum_congr rfl
        intro ρ hρ
        rw [if_pos hρ]
      rw [h2, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro ρ hρ
      by_cases h : ρ ∈ (zetaZeros_finite H).toFinset <;> simp [h]
    have hterm2 : ∀ ρ ∈ (zetaZeros_finite x).toFinset,
        ‖(if ρ ∈ (zetaZeros_finite H).toFinset then 0 else (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ)‖ ≤
          6 * (if ρ ∈ (zetaZeros_finite H).toFinset then 0 else (zetaMult ρ : ℝ)) := by
      intro ρ hρ
      by_cases hH : ρ ∈ (zetaZeros_finite H).toFinset
      · simp [hH]
      · rw [Set.Finite.mem_toFinset] at hρ
        rw [if_neg hH, if_neg hH]
        have himH : H < |ρ.im| := by
          by_contra hle
          exact hH (by
            rw [Set.Finite.mem_toFinset]
            exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, le_of_not_gt hle⟩)
        have hρnorm : H ≤ ‖ρ‖ := le_trans (le_of_lt himH) (Complex.abs_im_le_norm ρ)
        have hnorm : ‖(u : ℂ) ^ ρ‖ = u ^ ρ.re := Complex.norm_cpow_eq_rpow_re_of_pos hu0 ρ
        have hrpow : u ^ ρ.re ≤ u := by
          have h1 : u ^ ρ.re ≤ u ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ u) hρ.2.2.1.le
          simpa using h1
        have hmul : ‖(zetaMult ρ : ℂ)‖ = (zetaMult ρ : ℝ) := by
          first
          | rw [Complex.norm_natCast]
          | rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Nat.cast_nonneg _)]
        have hm0 : (0 : ℝ) ≤ (zetaMult ρ : ℝ) := Nat.cast_nonneg _
        have huH : u / H ≤ 6 := by
          rw [div_le_iff₀ hHpos]
          nlinarith [hHhalf, hu.2, hu.1, hHpos]
        calc ‖(zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ‖
            = ‖(zetaMult ρ : ℂ)‖ * ‖(u : ℂ) ^ ρ‖ / ‖ρ‖ := by rw [norm_div, norm_mul]
          _ = (zetaMult ρ : ℝ) * u ^ ρ.re / ‖ρ‖ := by rw [hnorm, hmul]
          _ ≤ (zetaMult ρ : ℝ) * u / H := by
              have h1 : (0 : ℝ) < ‖ρ‖ := lt_of_lt_of_le hHpos hρnorm
              rw [div_le_div_iff₀ h1 hHpos]
              have hstep : u ^ ρ.re * H ≤ u * ‖ρ‖ := by
                have hA : u ^ ρ.re * H ≤ u * H := by
                  have h2 : (0 : ℝ) ≤ H := le_of_lt hHpos
                  exact mul_le_mul_of_nonneg_right hrpow h2
                have hB : u * H ≤ u * ‖ρ‖ := by
                  have h2 : (0 : ℝ) ≤ u := le_of_lt hu0
                  exact mul_le_mul_of_nonneg_left hρnorm h2
                linarith
              calc (zetaMult ρ : ℝ) * u ^ ρ.re * H
                  = (zetaMult ρ : ℝ) * (u ^ ρ.re * H) := by ring
                _ ≤ (zetaMult ρ : ℝ) * (u * ‖ρ‖) := by
                    exact mul_le_mul_of_nonneg_left hstep hm0
                _ = (zetaMult ρ : ℝ) * u * ‖ρ‖ := by ring
          _ = (zetaMult ρ : ℝ) * (u / H) := by ring
          _ ≤ (zetaMult ρ : ℝ) * 6 := by
              apply mul_le_mul_of_nonneg_left huH hm0
          _ = 6 * (zetaMult ρ : ℝ) := by ring
    have hcount : (∑ ρ ∈ (zetaZeros_finite x).toFinset,
        (if ρ ∈ (zetaZeros_finite H).toFinset then 0 else (zetaMult ρ : ℝ))) ≤
        2 * (A2 * Real.log (x + 1) + B2) := by
      obtain ⟨hf1, hb1⟩ := hcnt (x - 1 / 4) (by
        rw [abs_of_pos (by linarith)]; linarith)
      obtain ⟨hf2, hb2⟩ := hcnt (-(x - 1 / 4)) (by
        rw [abs_neg, abs_of_pos (by linarith)]; linarith)
      have hb1' : (∑ ρ ∈ hf1.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
          A2 * Real.log (x + 1) + B2 := by
        refine hb1.trans ?_
        rw [abs_of_pos (by linarith : (0:ℝ) < x - 1 / 4)]
        have hle : Real.log (x - 1 / 4) ≤ Real.log (x + 1) :=
          Real.log_le_log (by linarith) (by linarith)
        nlinarith
      have hb2' : (∑ ρ ∈ hf2.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
          A2 * Real.log (x + 1) + B2 := by
        refine hb2.trans ?_
        rw [abs_neg, abs_of_pos (by linarith : (0:ℝ) < x - 1 / 4)]
        have hle : Real.log (x - 1 / 4) ≤ Real.log (x + 1) :=
          Real.log_le_log (by linarith) (by linarith)
        nlinarith
      have hsupp : ∀ ρ ∈ (zetaZeros_finite x).toFinset, ρ ∉ (zetaZeros_finite H).toFinset →
          ρ ∈ hf1.toFinset ∪ hf2.toFinset := by
        intro ρ hρ hnot
        rw [Set.Finite.mem_toFinset] at hρ hnot
        have himH : H < |ρ.im| := by
          by_contra hle
          exact hnot ⟨hρ.1, hρ.2.1, hρ.2.2.1, le_of_not_gt hle⟩
        obtain ⟨hzlo, hzhi⟩ := abs_le.mp hρ.2.2.2
        rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
        rcases lt_trichotomy ρ.im 0 with hneg | hzero | hpos
        · right
          refine ⟨hρ.1, ?_⟩
          rw [abs_le]
          rw [abs_of_neg hneg] at himH
          constructor <;> linarith
        · rw [hzero] at himH
          simp at himH
          linarith
        · left
          refine ⟨hρ.1, ?_⟩
          rw [abs_le]
          rw [abs_of_pos hpos] at himH
          constructor <;> linarith
      calc (∑ ρ ∈ (zetaZeros_finite x).toFinset,
            (if ρ ∈ (zetaZeros_finite H).toFinset then 0 else (zetaMult ρ : ℝ)))
          = ∑ ρ ∈ (zetaZeros_finite x).toFinset.filter
              (fun ρ => ρ ∉ (zetaZeros_finite H).toFinset), (zetaMult ρ : ℝ) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro ρ _
            by_cases h : ρ ∈ (zetaZeros_finite H).toFinset <;> simp [h]
        _ ≤ ∑ ρ ∈ hf1.toFinset ∪ hf2.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro ρ hρ
              rw [Finset.mem_filter] at hρ
              exact hsupp ρ hρ.1 hρ.2
            · intro _ _ _
              exact Nat.cast_nonneg _
        _ ≤ (∑ ρ ∈ hf1.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ)) +
              ∑ ρ ∈ hf2.toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
            have hu := Finset.sum_union_inter (s₁ := hf1.toFinset) (s₂ := hf2.toFinset)
              (f := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ))
            have hi : 0 ≤ ∑ ρ ∈ hf1.toFinset ∩ hf2.toFinset,
                (analyticOrderNatAt riemannZeta ρ : ℝ) :=
              Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
            linarith
        _ ≤ (A2 * Real.log (x + 1) + B2) + (A2 * Real.log (x + 1) + B2) :=
            add_le_add hb1' hb2'
        _ = 2 * (A2 * Real.log (x + 1) + B2) := by ring
    have htransfer : ‖∑ ρ ∈ (zetaZeros_finite x).toFinset,
        (if ρ ∈ (zetaZeros_finite H).toFinset then 0 else (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ)‖ ≤
        12 * (A2 * Real.log (x + 1) + B2) := by
      calc ‖∑ ρ ∈ (zetaZeros_finite x).toFinset,
            (if ρ ∈ (zetaZeros_finite H).toFinset then 0 else (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ)‖
          ≤ ∑ ρ ∈ (zetaZeros_finite x).toFinset,
              ‖if ρ ∈ (zetaZeros_finite H).toFinset then 0 else (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ‖ :=
            norm_sum_le _ _
        _ ≤ ∑ ρ ∈ (zetaZeros_finite x).toFinset,
              6 * (if ρ ∈ (zetaZeros_finite H).toFinset then 0 else (zetaMult ρ : ℝ)) :=
            Finset.sum_le_sum hterm2
        _ = 6 * ∑ ρ ∈ (zetaZeros_finite x).toFinset,
              (if ρ ∈ (zetaZeros_finite H).toFinset then 0 else (zetaMult ρ : ℝ)) := by
            rw [Finset.mul_sum]
        _ ≤ 6 * (2 * (A2 * Real.log (x + 1) + B2)) := by
            apply mul_le_mul_of_nonneg_left hcount (by norm_num)
        _ = 12 * (A2 * Real.log (x + 1) + B2) := by ring
    have hexp' : ‖((Chebyshev.psi u - u : ℝ) : ℂ) +
        ∑ ρ ∈ (zetaZeros_finite H).toFinset, (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ‖ ≤
        |C1| * (u * Real.log u ^ 2 / H + Real.log u) := by
      rw [hcast]
      refine hexp.trans ?_
      have h0 : 0 ≤ u * Real.log u ^ 2 / H + Real.log u := by
        have h1 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
        have h2 : 0 ≤ u * Real.log u ^ 2 / H := by positivity
        linarith
      exact mul_le_mul_of_nonneg_right (le_abs_self C1) h0
    have hEq : ((Chebyshev.psi u - u : ℝ) : ℂ) + cutoffPrimitive x u =
        (((Chebyshev.psi u - u : ℝ) : ℂ) +
          ∑ ρ ∈ (zetaZeros_finite H).toFinset, (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ) +
        ∑ ρ ∈ (zetaZeros_finite x).toFinset,
          (if ρ ∈ (zetaZeros_finite H).toFinset then 0 else (zetaMult ρ : ℂ) * (u : ℂ) ^ ρ / ρ) := by
      linear_combination hdiff
    have hupper : ‖((Chebyshev.psi u - u : ℝ) : ℂ) + cutoffPrimitive x u‖ ≤
        |C1| * (u * Real.log u ^ 2 / H + Real.log u) +
          12 * (A2 * Real.log (x + 1) + B2) := by
      rw [hEq]
      exact le_trans (norm_add_le _ _) (add_le_add hexp' htransfer)
    rw [sub_zero]
    refine le_trans hupper ?_
    have hlogu : Real.log u ≤ 2 * Real.log x := by
      have h1 : Real.log u ≤ Real.log (3 * x) := Real.log_le_log hu0 (by linarith [hu.2])
      rw [Real.log_mul (by norm_num) hx0.ne'] at h1
      have hlog3 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3'
      linarith
    have hratio : u * Real.log u ^ 2 / H ≤ 24 * Real.log x ^ 2 := by
      have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
      have hlogxnn : 0 ≤ Real.log x := le_of_lt hlogxpos
      have hsqu : Real.log u ^ 2 ≤ (2 * Real.log x) ^ 2 :=
        pow_le_pow_left₀ hlogu0 hlogu 2
      have h1 : u / H ≤ 6 := by
        rw [div_le_iff₀ hHpos]
        nlinarith [hHhalf, hu.2, hu.1, hHpos]
      have h2 : u * Real.log u ^ 2 / H = (u / H) * Real.log u ^ 2 := by ring
      rw [h2]
      have h3 : (u / H) * Real.log u ^ 2 ≤ 6 * (2 * Real.log x) ^ 2 :=
        mul_le_mul h1 hsqu (by positivity) (by norm_num)
      nlinarith
    have hlog3x : Real.log (x + 1) ≤ Real.log x + 1 := by
      have h1 : Real.log (x + 1) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) hx0.ne'] at h1
      linarith [Real.log_two_lt_d9]
    have hb1 : |C1| * (u * Real.log u ^ 2 / H + Real.log u) ≤
        26 * |C1| * Real.log x ^ 2 := by
      have h1 : u * Real.log u ^ 2 / H + Real.log u ≤ 26 * Real.log x ^ 2 := by
        have h2 : 2 * Real.log x ≤ 2 * Real.log x ^ 2 := by nlinarith
        linarith
      have h3 : 0 ≤ |C1| := abs_nonneg _
      nlinarith [h1]
    have hA2x : A2 * Real.log (x + 1) ≤ 10 * (Real.log x + 1) := by
      have h1 : A2 * Real.log (x + 1) ≤ A2 * (Real.log x + 1) :=
        mul_le_mul_of_nonneg_left hlog3x (le_of_lt hA2)
      have h2 : A2 * (Real.log x + 1) ≤ 10 * (Real.log x + 1) :=
        mul_le_mul_of_nonneg_right hA2le (by linarith)
      linarith
    have hb2 : 12 * (A2 * Real.log (x + 1) + B2) ≤
        200 * (A2 + B2 + 1) * Real.log x ^ 2 := by
      have hsq1 : (1 : ℝ) ≤ Real.log x ^ 2 := by nlinarith
      have hB2sq : B2 ≤ B2 * Real.log x ^ 2 := by nlinarith
      have hkey : A2 * Real.log (x + 1) + B2 ≤ 16 * (A2 + B2 + 1) * Real.log x ^ 2 := by
        have h4 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
        nlinarith
      nlinarith
    have hfin : |C1| * (u * Real.log u ^ 2 / H + Real.log u) +
        12 * (A2 * Real.log (x + 1) + B2) ≤ Cbig * Real.log x ^ 2 := by
      have hl2 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
      rw [hCbig]
      nlinarith [hb1, hb2, hl2, abs_nonneg C1, hA2, hB2]
    exact le_trans hfin (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))


/-- LEAF. BHMS page 7 Lemma 4 at q one, with cutoff T equal to x and x at most u at most three x.
The source constant is retained and the uniform error is at most C log squared x.
This leaf concerns one endpoint and contains no increment subtraction or variance estimate. -/
theorem truncated_endpoint : ∃ A : ℂ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x u : ℝ,
    2 ≤ x → u ∈ Set.Icc x (3 * x) →
      ‖((Chebyshev.psi u - u : ℝ) : ℂ) + cutoffPrimitive x u - A‖ ≤ C * Real.log x ^ 2 :=
  endpoint_main

/-- BHMS page 17, subtract the two endpoint formulas and cancel their common constant.
CONDITIONAL ON truncated_endpoint. -/
theorem truncated_increment_assembled : ∃ C : ℝ, 0 ≤ C ∧ ∀ x h t : ℝ,
    2 ≤ x → 2 ≤ h → h ≤ x → t ∈ Set.Icc x (2 * x) →
      ‖((Chebyshev.psi (t + h) - Chebyshev.psi t - h : ℝ) : ℂ) +
        lowZeros x h t + highZeros x h t‖ ≤ C * Real.log x ^ 2 := by
  obtain ⟨A, C, hC, hE⟩ := truncated_endpoint
  refine ⟨2 * C, by positivity, ?_⟩
  intro x h t hx hh hhx ht
  have h1 := hE x (t + h) hx ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h2 := hE x t hx ⟨ht.1, by linarith [ht.2]⟩
  have hid : ((Chebyshev.psi (t + h) - Chebyshev.psi t - h : ℝ) : ℂ) +
        lowZeros x h t + highZeros x h t =
      (((Chebyshev.psi (t + h) - (t + h) : ℝ) : ℂ) + cutoffPrimitive x (t + h) - A) -
        (((Chebyshev.psi t - t : ℝ) : ℂ) + cutoffPrimitive x t - A) := by
    have hs := cutoff_difference x h t (by linarith) (by linarith)
    push_cast at *
    linear_combination -hs
  rw [hid]
  have hn := norm_sub_le
    (((Chebyshev.psi (t + h) - (t + h) : ℝ) : ℂ) + cutoffPrimitive x (t + h) - A)
    (((Chebyshev.psi t - t : ℝ) : ℂ) + cutoffPrimitive x t - A)
  nlinarith

end LeanLab.GoldbachAverage.Decomp444e
