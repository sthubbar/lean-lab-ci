import LeanLab.HeathBrownPuchta.Assembly
import LeanLab.HeathBrownPuchta.Decomp1530b
import LeanLab.HeathBrownPuchta.Decomp130C0
import LeanLab.HeathBrownPuchta.Decomp130C2

/-!
P0012, structural estimates supporting Decomp130.
The canonical definitions below are copied verbatim from Decomp130.
The numerical moment certificate is used by the final exceptional exponent proof.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.HeathBrownPuchta.Decomp130
open Real Filter MeasureTheory LeanLab.Linnik
open LeanLab.HeathBrownPuchta.Decomp1530a
open LeanLab.HeathBrownPuchta.Decomp1530b
open LeanLab.HeathBrownPuchta.Assembly

/-- Paper page 14, display 23, the twin prime product. -/
noncomputable def C0 : ℝ :=
  ∏' p : ℕ, if p.Prime ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

/-- Paper page 27, the chosen major arc parameter. -/
noncomputable def P (N : ℕ) (w : ℝ) : ℝ := (N : ℝ) ^ (45 / 154 - 4 * w)

/-- Paper page 3, the major arcs in the unit interval. -/
def majorArcs (N : ℕ) (w : ℝ) : Set ℝ :=
  {α ∈ Set.Icc (0 : ℝ) 1 | ∃ (a : ℤ) (q : ℕ), 0 < q ∧ (q : ℝ) ≤ P N w ∧
    |α - (a : ℝ) / q| ≤ P N w / (q * N)}

/-- Paper page 2, the exceptional set at the unconditional lambda. -/
def exceptional (N : ℕ) : Set ℝ :=
  {α ∈ Set.Icc (0 : ℝ) 1 | (863665 / 1000000 : ℝ) * Lpar N 13 ≤ ‖Tp (Lpar N 13) α‖}

/-- Paper page 27, the integrand at K equal to 13. -/
noncomputable def integrand (N : ℕ) (w α : ℝ) : ℂ :=
  Sp N w α ^ 2 * Tp (Lpar N 13) α ^ 13 * ee (-(α * N))

/-- Paper pages 20 and 28, the major arc contribution. -/
noncomputable def maj (N : ℕ) (w : ℝ) : ℝ :=
  ∫ α in majorArcs N w, (integrand N w α).re

/-- Paper page 28, the minor arcs outside the exceptional set. -/
noncomputable def mout (N : ℕ) (w : ℝ) : ℝ :=
  ∫ α in (Set.Icc (0 : ℝ) 1 \ majorArcs N w) \ exceptional N, (integrand N w α).re

/-- Paper page 28, the minor arcs inside the exceptional set. -/
noncomputable def minr (N : ℕ) (w : ℝ) : ℝ :=
  ∫ α in (Set.Icc (0 : ℝ) 1 \ majorArcs N w) ∩ exceptional N, (integrand N w α).re

/-- Paper pages 20 and 28, the common scale of the three estimates. -/
noncomputable def X (N : ℕ) : ℝ :=
  C0 * N * (Lpar N 13 : ℝ) ^ (13 - 2) / Real.log 2 ^ 2


/-- P0012 page 2 and page 19. The floor in L changes the logarithmic
length by a bounded amount, so L divided by log N tends to 1 over log 2. -/
theorem length_ratio215 : Tendsto (fun N : ℕ => (Lpar N 13 : ℝ) / Real.log N)
    atTop (nhds (1 / Real.log 2)) := by
  let A : ℝ := 1 + Real.log (2 * (13 : ℝ)) / Real.log 2
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hi : Tendsto (fun N : ℕ => (Real.log (N : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlo : Tendsto (fun N : ℕ => 1 / Real.log 2 - A * (Real.log (N : ℝ))⁻¹)
      atTop (nhds (1 / Real.log 2)) := by
    simpa using tendsto_const_nhds.sub (hi.const_mul A)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : 1 ≤ N := by omega
    have hn : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hb := div_le_div_of_nonneg_right (Lpar_ge_log hN1 (by norm_num : 1 ≤ 13)) hn.le
    convert hb using 1
    dsimp [A]
    field_simp [h2.ne', hn.ne']
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : 1 ≤ N := by omega
    have hn : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hb := div_le_div_of_nonneg_right (Lpar_le_log hN1 (by norm_num : 1 ≤ 13)) hn.le
    convert hb using 1
    field_simp [h2.ne', hn.ne']

/-- P0012 page 19, conversion to the scale used by Lemma 7.
The ratio of the two displayed main term scales tends to 1. -/
theorem major_scale_ratio215 :
    Tendsto (fun N : ℕ => (Lpar N 13 : ℝ) ^ 2 * Real.log 2 ^ 2 / Real.log N ^ 2)
      atTop (nhds 1) := by
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h := (length_ratio215.mul_const (Real.log 2)).pow 2
  have he : ((1 / Real.log 2) * Real.log 2) ^ 2 = (1 : ℝ) := by field_simp
  rw [he] at h
  convert h using 1
  funext N
  ring

/-- P0012 page 19, before Lemma 7. Convert the paper main term scale
and its vanishing remainder to the scale X. CONDITIONAL ON the major arc input. -/
theorem major_from_remainder215 {w : ℝ} (hw : 0 ≤ w) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (nhds 0))
    (hmain : ∀ᶠ N : ℕ in atTop, Even N →
      (27895 / 10000 * (1 - 2 * w) + r N) *
        (C0 * N * (Lpar N 13 : ℝ) ^ 13 / Real.log N ^ 2) ≤ maj N w) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, Even N →
      (27895 / 10000 * (1 - 3 * w) - ε) * X N ≤ maj N w := by
  intro ε hε
  let a : ℝ := 27895 / 10000 * (1 - 2 * w)
  let Q : ℕ → ℝ := fun N => (Lpar N 13 : ℝ) ^ 2 * Real.log 2 ^ 2 / Real.log N ^ 2
  have ht : Tendsto (fun N => (a + r N) * Q N) atTop (nhds a) := by
    have h := ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => a) atTop (nhds a)).add hr).mul major_scale_ratio215
    simpa only [add_zero, mul_one] using h
  have hc : 0 ≤ C0 := by linarith [show (66 / 100 : ℝ) ≤ C0 from c0_bound215]
  have hgap : 27895 / 10000 * (1 - 3 * w) - ε < a := by dsimp [a]; nlinarith
  filter_upwards [hmain, ht.eventually (lt_mem_nhds hgap), eventually_ge_atTop 2]
    with N hN hrN hN2
  intro he
  have hX : 0 ≤ X N := by unfold X; positivity
  have hlog : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hN2))
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  apply le_trans (mul_le_mul_of_nonneg_right hrN.le hX)
  convert hN he using 1
  dsimp [a, Q, X]
  field_simp [hlog, h2]
  <;> ring

/-- LEAF. P0012 page 19, the estimate preceding Lemma 7.
The character expansion and density estimates in Sections 3 and 4
supply the paper main term and a vanishing relative error.
Source https://arxiv.org/abs/math/0201299 . -/
theorem major_remainder215 : ∃ w0 > (0 : ℝ), ∀ w : ℝ, 0 < w → w ≤ w0 →
    ∃ r : ℕ → ℝ, Tendsto r atTop (nhds 0) ∧
      ∀ᶠ N : ℕ in atTop, Even N →
        (27895 / 10000 * (1 - 2 * w) + r N) *
          (C0 * N * (Lpar N 13 : ℝ) ^ 13 / Real.log N ^ 2) ≤ maj N w := by
  sorry

/-- P0012 page 28. The power sum has norm at most its length. -/
theorem Tp_norm_le215 (L : ℕ) (α : ℝ) : ‖Tp L α‖ ≤ L := by
  unfold Tp
  calc
    _ ≤ ∑ ν ∈ Finset.Icc 1 L, ‖ee (α * 2 ^ ν)‖ := norm_sum_le _ _
    _ = L := by simp [ee, Complex.norm_exp, -Complex.ofReal_pow]

/-- P0012 page 28. A bound on S bounds the representation integrand. -/
theorem integrand_bound215 {N : ℕ} {w α B : ℝ} (hB : ‖Sp N w α‖ ≤ B) :
    |(integrand N w α).re| ≤ B ^ 2 * (Lpar N 13 : ℝ) ^ 13 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  apply (Complex.abs_re_le_norm _).trans
  simp only [integrand, norm_mul, norm_pow]
  have he : ‖ee (-(α * N))‖ = 1 := by simp [ee, Complex.norm_exp]
  rw [he, mul_one]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hB 2)
    (pow_le_pow_left₀ (norm_nonneg _) (Tp_norm_le215 _ _) 13)
    (pow_nonneg (norm_nonneg _) 13) (sq_nonneg _)

/-- P0012 page 28. Integrate a uniform bound over the exceptional part. -/
theorem minor_in_of_measure215 {N : ℕ} {w B : ℝ}
    (hS : ∀ α ∈ Set.Icc (0 : ℝ) 1 \ majorArcs N w, ‖Sp N w α‖ ≤ B) :
    |minr N w| ≤ B ^ 2 * (Lpar N 13 : ℝ) ^ 13 * (volume (exceptional N)).toReal := by
  let s := (Set.Icc (0 : ℝ) 1 \ majorArcs N w) ∩ exceptional N
  have he : volume (exceptional N) < ⊤ :=
    lt_of_le_of_lt (measure_mono (fun _ h => h.1)) (by simp)
  have hs : volume s < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_right) he
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (f := fun α => (integrand N w α).re) hs
    (fun α hα => by simpa only [Real.norm_eq_abs] using integrand_bound215 (hS α hα.1))
  change |∫ α in s, (integrand N w α).re| ≤ _
  rw [Real.norm_eq_abs] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (measureReal_mono Set.inter_subset_right he.ne) (by positivity))

/-- P0012 page 28. Move between the two indexing conventions for T. -/
theorem Tp_TL_difference215 (L : ℕ) (α : ℝ) :
    Tp L α - TL L α = ee (α * 2 ^ L) - ee α := by
  induction L with
  | zero => simp [Tp, TL]
  | succ L ih =>
    have hp : Tp (L + 1) α = Tp L α + ee (α * 2 ^ (L + 1)) := by
      unfold Tp
      exact Finset.sum_Icc_succ_top (by omega) _
    have ht : TL (L + 1) α = TL L α + ee (α * 2 ^ L) := by
      unfold TL
      exact Finset.sum_range_succ _ _
    rw [hp, ht]
    linear_combination ih

/-- P0012 Section 7 display 42 and page 28. Rotate the large power sum
and apply the exponential moment estimate to each scalar projection. -/
theorem large_Tp_measure215 {η ξ lam : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hξ : 0 ≤ ξ) (hlam : 0 ≤ lam) {h : ℕ} (hh : 0 < h) (L : ℕ) :
    (volume {α ∈ Set.Icc (0 : ℝ) 1 | lam * L ≤ ‖Tp L α‖}).toReal ≤
      ((1 + ⌊2 * π / η⌋₊ : ℕ) : ℝ) * Real.exp (2 * ξ) * Real.exp (ξ * h) *
        (Real.exp (-(ξ * (1 - η) * lam * L)) * F ξ h ^ (L / h)) := by
  classical
  let M : ℕ := 1 + ⌊2 * π / η⌋₊
  let A (m : ℕ) := {α ∈ Set.Icc (0 : ℝ) 1 |
    (1 - η) * (lam * L) - 2 ≤ (ee (-((m : ℝ) / M)) * TL L α).re}
  have hee (x : ℝ) : ‖ee x‖ = 1 := by simp [ee, Complex.norm_exp]
  have hsub : {α ∈ Set.Icc (0 : ℝ) 1 | lam * L ≤ ‖Tp L α‖} ⊆
      ⋃ m ∈ Finset.range M, A m := by
    intro α hα
    obtain ⟨m, hm, hr⟩ := rotation hη hη1 (by positivity : 0 ≤ lam * (L : ℝ)) hα.2
    have hd : ‖Tp L α - TL L α‖ ≤ 2 := by
      rw [Tp_TL_difference215]
      exact (norm_sub_le _ _).trans (by rw [hee, hee]; norm_num)
    have hρ : ‖ee (-((m : ℝ) / (M : ℝ)))‖ = 1 := hee _
    have hproj := Complex.re_le_norm (ee (-((m : ℝ) / (M : ℝ))) * (Tp L α - TL L α))
    have hnorm : ‖ee (-((m : ℝ) / (M : ℝ))) * (Tp L α - TL L α)‖ ≤ 2 := by
      rw [norm_mul, hρ, one_mul]
      exact hd
    rw [mul_sub, Complex.sub_re] at hproj
    rw [mul_sub] at hnorm
    refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hm, ?_⟩⟩
    refine ⟨hα.1, ?_⟩
    dsimp [M] at hproj hnorm ⊢
    linarith
  have hfin : volume (⋃ m ∈ Finset.range M, A m) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_mono ?_) (show volume (Set.Icc (0 : ℝ) 1) < ⊤ by simp)
    intro α hα
    simp only [Set.mem_iUnion] at hα
    obtain ⟨m, _, hm⟩ := hα
    exact hm.1
  have hm := measureReal_mono (μ := volume) hsub hfin
  have hu := measureReal_biUnion_finset_le (μ := volume) (Finset.range M) A
  have hb (m : ℕ) : volume.real (A m) ≤
      Real.exp (2 * ξ) * Real.exp (ξ * h) *
        (Real.exp (-(ξ * (1 - η) * lam * L)) * F ξ h ^ (L / h)) := by
    have hx := exceptional_bound hξ (hee (-((m : ℝ) / (M : ℝ)))) hh L
      ((1 - η) * (lam * L) - 2)
    change volume.real (A m) ≤ _ at hx
    have he : -(ξ * ((1 - η) * (lam * (L : ℝ)) - 2)) =
        2 * ξ + -(ξ * (1 - η) * lam * L) := by ring
    rw [he, Real.exp_add] at hx
    convert hx using 1 <;> ring
  have hs := Finset.sum_le_sum (fun m (_ : m ∈ Finset.range M) => hb m)
  have hall := hm.trans (hu.trans hs)
  simpa only [M, Measure.real, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc] using hall

/-- P0012 page 28. Logarithmic powers are absorbed by every positive power of N. -/
theorem length_subpower215 {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, (Lpar N 13 : ℝ) ^ 13 ≤ (N : ℝ) ^ δ := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := (isLittleO_log_rpow_atTop (by positivity : 0 < δ / 13)).bound hl
  have hbn : ∀ᶠ N : ℕ in atTop,
      ‖Real.log (N : ℝ)‖ ≤ Real.log 2 * ‖(N : ℝ) ^ (δ / 13)‖ :=
    tendsto_natCast_atTop_atTop.eventually hb
  filter_upwards [hbn, eventually_ge_atTop 1] with N hN hN1
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hn.le _)] at hN
  have hL : (Lpar N 13 : ℝ) ≤ (N : ℝ) ^ (δ / 13) := by
    apply (Lpar_le_log hN1 (by norm_num : 1 ≤ 13)).trans
    rw [div_le_iff₀ hl]
    nlinarith
  calc
    _ ≤ ((N : ℝ) ^ (δ / 13)) ^ 13 := pow_le_pow_left₀ (Nat.cast_nonneg _) hL 13
    _ = (N : ℝ) ^ δ := by
      rw [← Real.rpow_mul_natCast hn.le]
      congr 1
      norm_num

/-- LEAF. P0012 page 27, the first unweighted minor arc bound
following Vaughan Theorem 3.1. The constant can depend on w.
Source https://arxiv.org/abs/math/0201299 page 27 reference 17. -/
theorem vaughan_minor_raw215 : ∃ w0 > (0 : ℝ), ∀ w : ℝ, 0 < w → w ≤ w0 →
    ∃ B ≥ (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ α ∈ Set.Icc (0 : ℝ) 1 \ majorArcs N w,
        ‖Sp N w α‖ ≤ B * Real.log N ^ 3 *
          ((N : ℝ) ^ (4 / 5 : ℝ) + (N : ℝ) * (P N w) ^ (-(1 / 2 : ℝ))) := by
  sorry

/-- P0012 page 27. Substitute the chosen P, compare the two powers,
and absorb the cubic logarithm. CONDITIONAL ON vaughan_minor_raw215. -/
theorem vaughan_minor_sup215 : ∃ w0 > (0 : ℝ), ∀ w : ℝ, 0 < w → w ≤ w0 →
    ∃ B ≥ (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ α ∈ Set.Icc (0 : ℝ) 1 \ majorArcs N w,
        ‖Sp N w α‖ ≤ B * (N : ℝ) ^ (263 / 308 + 3 * w) := by
  obtain ⟨w0, hw0, hraw⟩ := vaughan_minor_raw215
  refine ⟨w0, hw0, ?_⟩
  intro w hw hww
  obtain ⟨B, hB, hrawB⟩ := hraw w hw hww
  have hlog := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) hw).bound (by norm_num : (0 : ℝ) < 1)
  have hlogN : ∀ᶠ N : ℕ in atTop,
      ‖Real.log (N : ℝ) ^ (3 : ℝ)‖ ≤ 1 * ‖(N : ℝ) ^ w‖ :=
    tendsto_natCast_atTop_atTop.eventually hlog
  refine ⟨2 * B, by positivity, ?_⟩
  filter_upwards [hrawB, hlogN, eventually_ge_atTop 1] with N hN hlogN hN1
  intro α hα
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hlog3 : Real.log N ^ 3 ≤ (N : ℝ) ^ w := by
    rw [← Real.rpow_natCast]
    exact (le_abs_self _).trans (by
      simpa only [Nat.cast_ofNat, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hn.le w), one_mul] using hlogN)
  have hP : (N : ℝ) * (P N w) ^ (-(1 / 2 : ℝ)) = (N : ℝ) ^ (263 / 308 + 2 * w) := by
    unfold P
    rw [← Real.rpow_mul hn.le, mul_comm, ← Real.rpow_add_one hn.ne']
    congr 1
    ring
  have hpow : (N : ℝ) ^ (4 / 5 : ℝ) ≤ (N : ℝ) ^ (263 / 308 + 2 * w) := by
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
    linarith
  apply (hN α hα).trans
  rw [hP]
  calc
    _ ≤ B * (N : ℝ) ^ w *
        ((N : ℝ) ^ (263 / 308 + 2 * w) + (N : ℝ) ^ (263 / 308 + 2 * w)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlog3 hB) (add_le_add hpow (le_refl ((N : ℝ) ^ (263 / 308 + 2 * w))))
        (by positivity) (by positivity)
    _ = (2 * B) * (N : ℝ) ^ (263 / 308 + 3 * w) := by
      rw [show B * (N : ℝ) ^ w *
        ((N : ℝ) ^ (263 / 308 + 2 * w) + (N : ℝ) ^ (263 / 308 + 2 * w)) =
          (2 * B) * ((N : ℝ) ^ w * (N : ℝ) ^ (263 / 308 + 2 * w)) by ring]
      rw [← Real.rpow_add hn]
      congr 2
      ring

/-- P0012 page 28. Off the exceptional set, remove eleven powers
of T and dominate the remaining integral by the minor arc mean square. -/
theorem mout_le_mean_square215 (N : ℕ) (w : ℝ) :
    |mout N w| ≤ ((863665 / 1000000 : ℝ) * Lpar N 13) ^ 11 *
      ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N w,
        ‖Sp N w α * Tp (Lpar N 13) α‖ ^ 2 := by
  let s := Set.Icc (0 : ℝ) 1 \ majorArcs N w
  let t := s \ exceptional N
  let f := fun α => ‖Sp N w α * Tp (Lpar N 13) α‖ ^ 2
  let g := fun α => (integrand N w α).re
  let a : ℝ := ((863665 / 1000000 : ℝ) * Lpar N 13) ^ 11
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hm : MeasurableSet (majorArcs N w) := by
    unfold majorArcs
    simp only [Set.ofPred_and, Set.ofPred_exists]
    refine measurableSet_Icc.inter (MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun q => ?_)
    measurability
  have he : MeasurableSet (exceptional N) := by
    unfold exceptional
    have hc : Continuous (fun α : ℝ => ‖Tp (Lpar N 13) α‖) := by unfold Tp ee; fun_prop
    exact measurableSet_Icc.inter (measurableSet_le measurable_const hc.measurable)
  have hs : MeasurableSet s := measurableSet_Icc.diff hm
  have ht : MeasurableSet t := hs.diff he
  have hsub : s ⊆ Set.Icc (0 : ℝ) 1 := Set.sdiff_subset
  have hts : t ⊆ s := Set.sdiff_subset
  have hfc : Continuous f := by dsimp [f]; unfold Sp Tp ee; fun_prop
  have hgc : Continuous g := by dsimp [g]; unfold integrand Sp Tp ee; fun_prop
  have hfi : IntegrableOn f s volume :=
    (hfc.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  have hgi : IntegrableOn g t volume :=
    (hgc.continuousOn.integrableOn_compact isCompact_Icc).mono_set (hts.trans hsub)
  have hfit : IntegrableOn f t volume := hfi.mono_set hts
  have hp (α : ℝ) (hα : α ∈ t) : ‖g α‖ ≤ a * f α := by
    have hT : ‖Tp (Lpar N 13) α‖ ≤ (863665 / 1000000 : ℝ) * Lpar N 13 := by
      apply le_of_lt
      apply lt_of_not_ge
      intro hh
      exact hα.2 ⟨hα.1.1, hh⟩
    have hee : ‖ee (-(α * N))‖ = 1 := by simp [ee, Complex.norm_exp]
    have hn : ‖integrand N w α‖ =
        ‖Sp N w α * Tp (Lpar N 13) α‖ ^ 2 * ‖Tp (Lpar N 13) α‖ ^ 11 := by
      simp only [integrand, norm_mul, norm_pow, hee, mul_one, mul_pow]
      ring
    have hb := (Complex.abs_re_le_norm (integrand N w α)).trans_eq hn
    change |(integrand N w α).re| ≤ _ at hb
    change ‖(integrand N w α).re‖ ≤ a * f α
    rw [Real.norm_eq_abs]
    apply hb.trans
    simpa only [a, f, mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hT 11)
        (sq_nonneg ‖Sp N w α * Tp (Lpar N 13) α‖)
  have hmono : (∫ α in t, f α) ≤ ∫ α in s, f α :=
    setIntegral_mono_set hfi (Filter.Eventually.of_forall (fun α => sq_nonneg _))
      (Filter.Eventually.of_forall (fun α hα => hts hα))
  change |∫ α in t, g α| ≤ a * ∫ α in s, f α
  rw [← Real.norm_eq_abs]
  calc
    _ ≤ ∫ α in t, ‖g α‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ α in t, a * f α :=
      setIntegral_mono_on hgi.norm (hfit.const_mul a) ht hp
    _ = a * ∫ α in t, f α := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono ha

/-- LEAF. P0012 page 25, Lemma 9, the actual minor arc mean square.
The proof uses Chen's prime pair estimate on page 20 and the major arc
mean square lower bound on pages 22 through 25.
Source https://arxiv.org/abs/math/0201299 . -/
theorem minor_mean_square215 : ∃ w0 > (0 : ℝ), ∀ w : ℝ, 0 < w → w ≤ w0 →
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      (∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N w,
        ‖Sp N w α * Tp (Lpar N 13) α‖ ^ 2) ≤
          (C0 * (78342 / 10000 - 2 + 2 * w) *
            LeanLab.HeathBrownPuchta.Lemma8Const.C2 / Real.log 2 ^ 2 +
            1 / Real.log 2 + ε) * N := by
  sorry

/-- P0012 page 27, a derived obstruction for the trivial prime sum envelope.
A linear envelope cannot imply the sublinear exponent at w equal to 10 to power negative 5. -/
theorem no_linear_minor_envelope215 :
    ¬ ∃ B : ℝ, ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ≤ B * (N : ℝ) ^ (263 / 308 + 3 / 100000 : ℝ) := by
  rintro ⟨B, hB⟩
  have hs := small_of_rpow (C := B)
    (by norm_num : (263 / 308 + 3 / 100000 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨N, hN, hsN, hp⟩ := (hB.and (hs.and (eventually_gt_atTop 0))).exists
  have hn : (0 : ℝ) < N := by exact_mod_cast hp
  linarith

/-- P0012 page 20, the full mean square is the sum of its major
and minor arc parts. This is an exact integral partition. -/
theorem mean_square_split215 (N : ℕ) (w : ℝ) :
    Jint N w (Lpar N 13) =
      (∫ α in majorArcs N w, ‖Sp N w α * Tp (Lpar N 13) α‖ ^ 2) +
      ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N w,
        ‖Sp N w α * Tp (Lpar N 13) α‖ ^ 2 := by
  let f := fun α => ‖Sp N w α * Tp (Lpar N 13) α‖ ^ 2
  have hc : Continuous f := by dsimp [f]; unfold Sp Tp ee; fun_prop
  have hi : IntegrableOn f (Set.Icc (0 : ℝ) 1) volume :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  have hm : MeasurableSet (majorArcs N w) := by
    unfold majorArcs
    simp only [Set.ofPred_and, Set.ofPred_exists]
    refine measurableSet_Icc.inter (MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun q => ?_)
    measurability
  have hsub : majorArcs N w ⊆ Set.Icc (0 : ℝ) 1 := fun α hα => hα.1
  have hs := integral_inter_add_sdiff hm hi
  rw [Set.inter_eq_right.mpr hsub] at hs
  change (∫ α in (0 : ℝ)..1, f α) = _
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact hs.symm

/-- P0012 page 25 display 40. The product over all integers above
a cutoff telescopes to this exact finite expression. -/
theorem telescoping_product215 (M n : ℕ) (hM : 2 ≤ M) (hMn : M ≤ n) :
    (∏ i ∈ Finset.Ico (M + 1) (n + 1), (1 - 1 / ((i : ℝ) - 1) ^ 2)) =
      ((M : ℝ) - 1) * n / ((M : ℝ) * ((n : ℝ) - 1)) := by
  induction n, hMn using Nat.le_induction with
  | base =>
    simp only [Finset.Ico_self, Finset.prod_empty]
    have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM
    field_simp [show (M : ℝ) ≠ 0 by linarith, show (M : ℝ) - 1 ≠ 0 by linarith]
    <;> ring
  | succ n hMn ih =>
    rw [Finset.prod_Ico_succ_top (by omega), ih]
    have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have hn : (2 : ℝ) ≤ n := by exact_mod_cast (le_trans hM hMn)
    push_cast
    field_simp [show (M : ℝ) ≠ 0 by linarith, show (n : ℝ) ≠ 0 by linarith,
      show (n : ℝ) - 1 ≠ 0 by linarith]
    <;> ring

/-- P0012 page 25 display 40. The exact integer tail product
converges to one minus the reciprocal cutoff. -/
theorem telescoping_limit215 (M : ℕ) (hM : 2 ≤ M) :
    Filter.Tendsto (fun n : ℕ =>
      ∏ i ∈ Finset.Ico (M + 1) (n + 1), (1 - 1 / ((i : ℝ) - 1) ^ 2))
      Filter.atTop (nhds (1 - 1 / (M : ℝ))) := by
  have hnat : Filter.Tendsto (fun n : ℕ => (n : ℝ) - 1) Filter.atTop Filter.atTop :=
    by simpa [sub_eq_add_neg] using
      Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp hnat
  have ht : Filter.Tendsto (fun n : ℕ =>
      (((M : ℝ) - 1) / M) * (1 + ((n : ℝ) - 1)⁻¹))
      Filter.atTop (nhds (((M : ℝ) - 1) / M)) := by
    simpa using ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1)).add hi).const_mul (((M : ℝ) - 1) / M)
  have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have heq : (fun n : ℕ =>
      ∏ i ∈ Finset.Ico (M + 1) (n + 1), (1 - 1 / ((i : ℝ) - 1) ^ 2))
      =ᶠ[Filter.atTop] (fun n => (((M : ℝ) - 1) / M) * (1 + ((n : ℝ) - 1)⁻¹)) := by
    filter_upwards [Filter.eventually_ge_atTop M] with n hn
    rw [telescoping_product215 M n hM hn]
    have hnr : (2 : ℝ) ≤ n := by exact_mod_cast (le_trans hM hn)
    field_simp [show (M : ℝ) ≠ 0 by linarith, show (n : ℝ) - 1 ≠ 0 by linarith]
    <;> ring
  have hc : ((M : ℝ) - 1) / M = 1 - 1 / (M : ℝ) := by
    field_simp [show (M : ℝ) ≠ 0 by linarith]
    <;> ring
  rw [← hc]
  exact ht.congr' heq.symm

/-- P0012 Lemma 1, pages 28 through 31. The finite moment
hypotheses give the exceptional set decay after rotation and exponent conversion. -/
theorem exceptional_decay_of_moment215
    (hF_given : 1 ≤ F (1181 / 1000) 16)
    (he0_given : 109 / 154 + 1 / 10 ^ 6 <
      (1181 / 1000 : ℝ) * (863665 / 1000000) / Real.log 2 -
        Real.log (F (1181 / 1000) 16) / (16 * Real.log 2)) : ∃ E : ℝ, 109 / 154 < E ∧
    ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      (volume (exceptional N)).toReal ≤ C * (N : ℝ) ^ (-E) := by
  let Emodel (ξ lam F0 : ℝ) (hh : ℕ) : ℝ :=
    ξ * lam / Real.log 2 - Real.log F0 / (hh * Real.log 2)
  let ξ : ℝ := 1181 / 1000
  let lam : ℝ := 863665 / 1000000
  let η : ℝ := 1 / 10 ^ 9
  let F0 : ℝ := F ξ 16
  let c : ℝ := ξ * (1 - η) * lam
  let A : ℝ := 1 + Real.log (2 * (13 : ℝ)) / Real.log 2
  let E : ℝ := c / Real.log 2 - Real.log F0 / (16 * Real.log 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hF : 1 ≤ F0 := hF_given
  have hc : 0 ≤ c := by norm_num [c, ξ, η, lam]
  have heq : E = Emodel ξ lam F0 16 - (ξ * lam / Real.log 2) * η := by
    dsimp [E, c, Emodel]
    ring
  have he0 := he0_given
  change 109 / 154 + 1 / 10 ^ 6 < Emodel ξ lam F0 16 at he0
  have hratio : ξ * lam / Real.log 2 < 10 := by
    rw [div_lt_iff₀ hlog]
    have hl := Real.log_two_gt_d9
    norm_num [ξ, lam]
    linarith
  have hE : 109 / 154 < E := by
    rw [heq]
    dsimp [η]
    nlinarith
  let D : ℝ := ((1 + ⌊2 * π / η⌋₊ : ℕ) : ℝ) *
    Real.exp (2 * ξ) * Real.exp (ξ * (16 : ℕ))
  refine ⟨E, hE, D * Real.exp (c * A), ?_, ?_⟩
  · dsimp [D]
    positivity
  · intro N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hb := large_Tp_measure215 (η := η) (ξ := ξ) (lam := lam) (by norm_num [η]) (by norm_num [η])
      (by norm_num [ξ]) (by norm_num [lam]) (by norm_num : 0 < 16) (Lpar N 13)
    change (volume (exceptional N)).toReal ≤
      D * (Real.exp (-(c * (Lpar N 13 : ℝ))) * F0 ^ (Lpar N 13 / 16)) at hb
    have hp := exponent_conversion hc hF (by norm_num : 0 < 16)
      (by exact_mod_cast hN : (1 : ℝ) ≤ N)
      (Lpar_ge_log hN (by norm_num : 1 ≤ 13))
      (Lpar_le_log hN (by norm_num : 1 ≤ 13))
    change Real.exp (-(c * (Lpar N 13 : ℝ))) * F0 ^ (Lpar N 13 / 16) ≤
      Real.exp (c * A) * (N : ℝ) ^ (-E) at hp
    have hD : 0 ≤ D := by dsimp [D]; positivity
    exact hb.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hD)

/-- P0012 pages 27 and 28. Combine exceptional set decay with
the Vaughan supremum conversion and absorb the logarithmic length. -/
theorem minor_in_from_decay215
    (hdecay : ∃ E : ℝ, 109 / 154 < E ∧
      ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
        (volume (exceptional N)).toReal ≤ C * (N : ℝ) ^ (-E)) : ∃ E : ℝ, 109 / 154 < E ∧
    ∃ w0 > (0 : ℝ), ∀ w : ℝ, 0 < w → w ≤ w0 →
      ∀ δ > 0, ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
        |minr N w| ≤ C * (N : ℝ) ^ (2 * (263 / 308 + 3 * w) - E + δ) := by
  obtain ⟨E, hE, A, hA, hmeas⟩ := hdecay
  obtain ⟨w0, hw0, hsup⟩ := vaughan_minor_sup215
  refine ⟨E, hE, w0, hw0, ?_⟩
  intro w hw hww δ hδ
  obtain ⟨B, hB, hsupB⟩ := hsup w hw hww
  refine ⟨B ^ 2 * A, ?_⟩
  filter_upwards [hsupB, length_subpower215 hδ, eventually_ge_atTop 1]
    with N hS hL hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hi := minor_in_of_measure215 hS
  have hm := hmeas N hN
  apply hi.trans
  calc
    _ ≤ (B * (N : ℝ) ^ (263 / 308 + 3 * w)) ^ 2 *
        (N : ℝ) ^ δ * (A * (N : ℝ) ^ (-E)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hL (sq_nonneg _)) hm
        (ENNReal.toReal_nonneg) (by positivity)
    _ = (B ^ 2 * A) * (N : ℝ) ^ (2 * (263 / 308 + 3 * w) - E + δ) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hn.le]
      rw [show (263 / 308 + 3 * w) * (2 : ℕ) = 2 * (263 / 308 + 3 * w) by ring]
      rw [show B ^ 2 * (N : ℝ) ^ (2 * (263 / 308 + 3 * w)) * (N : ℝ) ^ δ *
        (A * (N : ℝ) ^ (-E)) = (B ^ 2 * A) *
          ((N : ℝ) ^ (2 * (263 / 308 + 3 * w)) * (N : ℝ) ^ δ * (N : ℝ) ^ (-E)) by ring]
      rw [← Real.rpow_add hn, ← Real.rpow_add hn]
      congr 2
      ring

/-- LEAF. Paper pages 25 and 26, displays 40 and 41.
The C2 bound uses Liu, Liu and Wang 1999, display 3.9, through the paper's proof.
The C0 bound uses the finite product and telescoping tail of display 40. -/
theorem constants : 66 / 100 ≤ C0 ∧
    LeanLab.HeathBrownPuchta.Lemma8Const.C2 ≤ 22141 / 10000 := by
  exact ⟨c0_bound215, c2_bound215⟩

/-- LEAF. Paper page 20, Lemma 7, used on page 28 at K equal to 13.
The proof uses Gallagher's major arc method and the density inputs of Section 3.
All sufficiently small positive w are allowed. -/
theorem major_estimate : ∃ w0 > (0 : ℝ), ∀ w : ℝ, 0 < w → w ≤ w0 →
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      Even N → (27895 / 10000 * (1 - 3 * w) - ε) * X N ≤ maj N w := by
  obtain ⟨w0, hw0, hmajor⟩ := major_remainder215
  refine ⟨w0, hw0, ?_⟩
  intro w hw hww
  obtain ⟨r, hr, hmain⟩ := hmajor w hw hww
  exact major_from_remainder215 hw.le r hr hmain

/-- LEAF. Paper page 28, outside the exceptional set, using Lemmas 8 to 10.
Chen's prime pair bound is cited on page 21 and remains an outside input here. -/
theorem minor_out_estimate : ∃ w0 > (0 : ℝ), ∀ w : ℝ, 0 < w → w ≤ w0 →
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      |mout N w| ≤ (C9 (78342 / 10000) LeanLab.HeathBrownPuchta.Lemma8Const.C2 C0 w *
        (863665 / 1000000) ^ (13 - 2) + ε) * X N := by
  have hc0 : 0 < C0 := by linarith [show (66 / 100 : ℝ) ≤ C0 from c0_bound215]
  obtain ⟨w0, hw0, hmean⟩ := minor_mean_square215
  refine ⟨w0, hw0, ?_⟩
  intro w hw hww
  simpa only [X] using
    (lemma9_out_of_J (K := 13) (lam := (863665 / 1000000 : ℝ))
      (C0 := C0) (C1 := (78342 / 10000 : ℝ))
      (C2 := LeanLab.HeathBrownPuchta.Lemma8Const.C2) (w := w)
      (mout := fun N => mout N w)
      (Jm := fun N => ∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N w,
        ‖Sp N w α * Tp (Lpar N 13) α‖ ^ 2)
      (L := fun N => Lpar N 13) hc0 (by norm_num)
      (Filter.Eventually.of_forall fun N => mout_le_mean_square215 N w)
      (hmean w hw hww))

/-- P0012 page 25 display 40. The odd prime product is multipliable,
independently of the finite numerical lower bound. -/
theorem c0_multipliable215 : Multipliable (fun p : ℕ =>
    if p.Prime ∧ 2 < p then (1 : ℝ) - 1 / ((p : ℝ) - 1) ^ 2 else 1) := by
  let GG (n : ℕ) : ℝ :=
    if n.Prime ∧ 2 < n then 1 / ((n : ℝ) - 1) ^ 2 else 0

  have GG_nonneg (n : ℕ) : 0 ≤ GG n := by
    unfold GG
    split_ifs with h
    · have h3n : 3 ≤ n := by
        have := h.1.two_le
        omega
      have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3n
      exact div_nonneg zero_le_one (by nlinarith)
    · exact le_rfl

  /- `Σ (n+1)⁻²` converges, so `Σ GG` converges as well. -/
  have summable_GG : Summable GG := by
    rw [← summable_nat_add_iff 2]
    have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
        (summable_one_div_nat_pow (p := 2)).2 (by norm_num)
      have h3 := (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ)) ^ 2) 1).2 h2
      simpa only [Nat.cast_add, Nat.cast_one] using h3
    refine Summable.of_nonneg_of_le (fun n => GG_nonneg (n + 2)) (fun n => ?_) hbase
    unfold GG
    split_ifs with h
    · have e : (((n + 2 : ℕ)) : ℝ) - 1 = (n : ℝ) + 1 := by push_cast; ring
      rw [e]
    · exact div_nonneg zero_le_one (sq_nonneg _)

  have hsum : Summable (fun n : ℕ => -GG n) := summable_GG.neg
  have hmult : Multipliable (fun n : ℕ => 1 - GG n) := by
    simpa only [sub_eq_add_neg] using Real.multipliable_one_add_of_summable hsum
  convert hmult using 1
  funext n
  dsimp [GG]
  split_ifs <;> ring

end LeanLab.HeathBrownPuchta.Decomp130
