/-
Total variation behind 1205.5252v4 eq. (2.5), (2.6): the derivative of
`η_{2,ρ}(t) = log(ρ t) η₂(t)` is piecewise smooth with jumps at `1/4`, `1/2`, `1`; its total
variation, the `L¹` norm of the measure `η_{2,ρ}''`, is computed with Mathlib's `eVariationOn`,
including the regime `e² < ρ < 4e²` where each smooth piece has an interior extremum.
AI-written Lean code, Claude, 2026-10-21, PC run 20261021T1203Z-6472, unit U-1408.
Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.HelfgottArcs.Weights

namespace LeanLab.HelfgottArcs
open MeasureTheory Set Real Filter Topology ENNReal

/-! ### Generic facts on `eVariationOn` for real functions of a real variable -/

/-- Variation of a monotone function on `[a, b]`. -/
theorem eVar_Icc_of_monotoneOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b)) :
    eVariationOn f (Icc a b) = ENNReal.ofReal (f b - f a) := by
  have := hf.eVariationOn_eq (a := a) (b := b) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  rwa [inter_self] at this

theorem eVar_neg (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => -f x) s = eVariationOn f s := by
  simp [eVariationOn, edist_neg_neg]

/-- Variation of an antitone function on `[a, b]`. -/
theorem eVar_Icc_of_antitoneOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AntitoneOn f (Icc a b)) :
    eVariationOn f (Icc a b) = ENNReal.ofReal (f a - f b) := by
  rw [← eVar_neg, eVar_Icc_of_monotoneOn hab (fun x hx y hy hxy => neg_le_neg (hf hx hy hxy))]
  ring_nf

theorem eVar_const_zero (s : Set ℝ) : eVariationOn (fun _ : ℝ => (0 : ℝ)) s = 0 :=
  eVariationOn.constant_on (Set.subsingleton_singleton.anti (by rintro _ ⟨x, -, rfl⟩; rfl))

/-- Jump lemma. If `F = φ` on the open interval `(a, b)` and `φ` is continuous on `[a, b]`,
the variation of `F` on `[a, b]` is that of `φ` plus the two endpoint discrepancies. -/
theorem eVar_Icc_of_eqOn_Ioo {F φ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hφ : ContinuousOn φ (Icc a b)) (hF : EqOn F φ (Ioo a b)) :
    eVariationOn F (Icc a b) =
      edist (F a) (φ a) + eVariationOn φ (Icc a b) + edist (φ b) (F b) := by
  set m := (a + b) / 2 with hm
  have hm1 : a < m := by rw [hm]; linarith
  have hm2 : m < b := by rw [hm]; linarith
  have splitF := eVariationOn.Icc_add_Icc F hm1.le hm2.le (mem_univ m)
  have splitφ := eVariationOn.Icc_add_Icc φ hm1.le hm2.le (mem_univ m)
  simp only [univ_inter] at splitF splitφ
  -- left half
  have s1 : Icc a m ∩ Ioi a = Ioc a m := by
    ext x; simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.le, h.2⟩, h.1⟩⟩
  have s2 : Icc a m ∩ Ici a = Icc a m := inter_eq_left.mpr Icc_subset_Ici_self
  have nb1 : (𝓝[Icc a m ∩ Ioi a] a).NeBot := by rw [s1]; exact left_nhdsWithin_Ioc_neBot hm1
  have cφa : ContinuousWithinAt φ (Icc a m) a :=
    (hφ a ⟨le_rfl, hab.le⟩).mono (Icc_subset_Icc le_rfl hm2.le)
  have tF1 : Tendsto F (𝓝[Icc a m ∩ Ioi a] a) (𝓝 (φ a)) := by
    rw [s1]
    refine Tendsto.congr' ?_ (cφa.mono Ioc_subset_Icc_self)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hF ⟨hx.1, hx.2.trans_lt hm2⟩).symm
  have L := eVariationOn.eVariationOn_on_inter_Ici_eq_Ioi_add_edist nb1
    (⟨le_rfl, hm1.le⟩ : a ∈ Icc a m) tF1
  have Lφ := eVariationOn.eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt nb1
    (cφa.mono inter_subset_left)
  rw [s1, s2] at L Lφ
  have eL : eVariationOn F (Ioc a m) = eVariationOn φ (Ioc a m) :=
    eVariationOn.eq_of_eqOn (fun x hx => hF ⟨hx.1, hx.2.trans_lt hm2⟩)
  -- right half
  have r1 : Icc m b ∩ Iio b = Ico m b := by
    ext x; simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_Ico]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.le⟩, h.2⟩⟩
  have r2 : Icc m b ∩ Iic b = Icc m b := inter_eq_left.mpr Icc_subset_Iic_self
  have nb2 : (𝓝[Icc m b ∩ Iio b] b).NeBot := by rw [r1]; exact right_nhdsWithin_Ico_neBot hm2
  have cφb : ContinuousWithinAt φ (Icc m b) b :=
    (hφ b ⟨hab.le, le_rfl⟩).mono (Icc_subset_Icc hm1.le le_rfl)
  have tF2 : Tendsto F (𝓝[Icc m b ∩ Iio b] b) (𝓝 (φ b)) := by
    rw [r1]
    refine Tendsto.congr' ?_ (cφb.mono Ico_subset_Icc_self)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hF ⟨hm1.trans_le hx.1, hx.2⟩).symm
  have R := eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist nb2
    (⟨hm2.le, le_rfl⟩ : b ∈ Icc m b) tF2
  have Rφ := eVariationOn.eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt nb2
    (cφb.mono inter_subset_left)
  rw [r1, r2] at R Rφ
  have eR : eVariationOn F (Ico m b) = eVariationOn φ (Ico m b) :=
    eVariationOn.eq_of_eqOn (fun x hx => hF ⟨hm1.trans_le hx.1, hx.2⟩)
  rw [← splitF, ← splitφ, L, R, eL, eR, Lφ, Rφ, edist_comm (F b)]
  ring

/-- For `x ≤ y ≤ z` the two distances add up. -/
theorem edist_add_edist_of_le {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    edist x y + edist y z = ENNReal.ofReal (z - x) := by
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith),
    abs_of_nonpos (by linarith), ← ENNReal.ofReal_add (by linarith) (by linarith)]
  ring_nf

/-! ### The profile `K_c(t) = log(c t²)/t` -/

/-- `K_c(t) = log(c t²) / t`. The smooth pieces of `η_{2,ρ}'` are `4 K_{4ρ}` and `-4 K_ρ`. -/
noncomputable def Kf (c t : ℝ) : ℝ := Real.log (c * t ^ 2) / t

theorem Kf_hasDerivAt {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (Kf c) ((2 - Real.log (c * t ^ 2)) / t ^ 2) t := by
  have h1 : HasDerivAt (fun s => c * s ^ 2) (c * (2 * t)) t := by
    convert (hasDerivAt_pow 2 t).const_mul c using 1; ring
  have h2 := h1.log (by positivity)
  have h3 := h2.div (hasDerivAt_id t) ht.ne'
  convert h3 using 1
  · funext s; simp [Kf]
  · simp only [id]; field_simp

theorem Kf_continuousOn {c x y : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ContinuousOn (Kf c) (Icc x y) := fun t ht =>
  (Kf_hasDerivAt hc (hx.trans_le ht.1)).continuousAt.continuousWithinAt

theorem Kf_monotoneOn {c x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : c * y ^ 2 ≤ Real.exp 2) :
    MonotoneOn (Kf c) (Icc x y) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc x y) (Kf_continuousOn hc hx)
  · rw [interior_Icc]; intro t ht
    exact (Kf_hasDerivAt hc (hx.trans ht.1)).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro t ht
    have ht0 : 0 < t := hx.trans ht.1
    rw [(Kf_hasDerivAt hc ht0).deriv]
    apply div_nonneg _ (sq_nonneg _)
    have : c * t ^ 2 ≤ c * y ^ 2 := by gcongr; exact ht.2.le
    have := (Real.log_le_iff_le_exp (by positivity)).2 (this.trans hy)
    linarith

theorem Kf_antitoneOn {c x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : Real.exp 2 ≤ c * x ^ 2) :
    AntitoneOn (Kf c) (Icc x y) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc x y) (Kf_continuousOn hc hx)
  · rw [interior_Icc]; intro t ht
    exact (Kf_hasDerivAt hc (hx.trans ht.1)).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro t ht
    have ht0 : 0 < t := hx.trans ht.1
    rw [(Kf_hasDerivAt hc ht0).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have : c * x ^ 2 ≤ c * t ^ 2 := by gcongr; exact ht.1.le
    have := (Real.le_log_iff_exp_le (by positivity)).2 (hy.trans this)
    linarith

/-! ### The pieces of `η_{2,ρ}'` -/

/-- `η_{2,ρ}'` on `(1/4, 1/2)`: `4 log(4ρt²)/t`. -/
noncomputable def gL (ρ t : ℝ) : ℝ := 4 * Kf (4 * ρ) t
/-- `η_{2,ρ}'` on `(1/2, 1)`: `-4 log(ρt²)/t`. -/
noncomputable def gR (ρ t : ℝ) : ℝ := -4 * Kf ρ t

theorem eta2rho_hasDerivAt_left {ρ t : ℝ} (hρ : 0 < ρ) (h1 : 1 / 4 < t) (h2 : t < 1 / 2) :
    HasDerivAt (eta2rho ρ) (gL ρ t) t := by
  have ht : 0 < t := by linarith
  have hl : HasDerivAt (fun s => Real.log (ρ * s)) (ρ * 1 / (ρ * t)) t :=
    ((hasDerivAt_id t).const_mul ρ).log (by simp only [id]; positivity)
  have := hl.mul (eta2_hasDerivAt_left h1 h2)
  have e : eta2rho ρ = fun s => Real.log (ρ * s) * eta2 s := rfl
  rw [e]
  convert this using 1
  rw [eta2_of_mem_left h1.le h2.le]
  unfold gL Kf
  rw [show 4 * ρ * t ^ 2 = (4 * t) * (ρ * t) by ring,
    Real.log_mul (by positivity) (by positivity)]
  field_simp
  try ring

theorem eta2rho_hasDerivAt_right {ρ t : ℝ} (hρ : 0 < ρ) (h1 : 1 / 2 < t) (h2 : t < 1) :
    HasDerivAt (eta2rho ρ) (gR ρ t) t := by
  have ht : 0 < t := by linarith
  have hl : HasDerivAt (fun s => Real.log (ρ * s)) (ρ * 1 / (ρ * t)) t :=
    ((hasDerivAt_id t).const_mul ρ).log (by simp only [id]; positivity)
  have := hl.mul (eta2_hasDerivAt_right h1 h2)
  have e : eta2rho ρ = fun s => Real.log (ρ * s) * eta2 s := rfl
  rw [e]
  convert this using 1
  rw [eta2_of_mem_right h1.le h2.le]
  unfold gR Kf
  rw [show ρ * t ^ 2 = t * (ρ * t) by ring,
    Real.log_mul (by positivity) (by positivity)]
  field_simp
  try ring

theorem eta2rho_hasDerivAt_out {ρ t : ℝ} (h : t < 1 / 4 ∨ 1 < t) :
    HasDerivAt (eta2rho ρ) 0 t := by
  refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
  rcases h with h | h
  · filter_upwards [Iio_mem_nhds h] with s hs
    simp [eta2rho, eta2_of_lt hs]
  · filter_upwards [Ioi_mem_nhds h] with s hs
    simp [eta2rho, eta2_of_gt hs]

theorem gL_quarter (ρ : ℝ) : gL ρ (1 / 4) = 16 * Real.log (ρ / 4) := by
  unfold gL Kf; rw [show 4 * ρ * (1 / 4 : ℝ) ^ 2 = ρ / 4 by ring]; ring
theorem gL_half (ρ : ℝ) : gL ρ (1 / 2) = 8 * Real.log ρ := by
  unfold gL Kf; rw [show 4 * ρ * (1 / 2 : ℝ) ^ 2 = ρ by ring]; ring
theorem gR_half (ρ : ℝ) : gR ρ (1 / 2) = -8 * Real.log (ρ / 4) := by
  unfold gR Kf; rw [show ρ * (1 / 2 : ℝ) ^ 2 = ρ / 4 by ring]; ring
theorem gR_one (ρ : ℝ) : gR ρ 1 = -4 * Real.log ρ := by
  unfold gR Kf; rw [show ρ * (1 : ℝ) ^ 2 = ρ by ring]; ring

theorem gL_continuousOn {ρ : ℝ} (hρ : 0 < ρ) : ContinuousOn (gL ρ) (Icc (1 / 4) (1 / 2)) :=
  continuousOn_const.mul (Kf_continuousOn (by positivity) (by norm_num))
theorem gR_continuousOn {ρ : ℝ} (hρ : 0 < ρ) : ContinuousOn (gR ρ) (Icc (1 / 2) 1) :=
  continuousOn_const.mul (Kf_continuousOn hρ (by norm_num))

/-! ### Variation of each smooth piece, three regimes -/

theorem VL_lo {ρ : ℝ} (hρ : 0 < ρ) (h : ρ ≤ Real.exp 2) :
    eVariationOn (gL ρ) (Icc (1 / 4) (1 / 2)) =
      ENNReal.ofReal (gL ρ (1 / 2) - gL ρ (1 / 4)) := by
  apply eVar_Icc_of_monotoneOn (by norm_num)
  intro x hx y hy hxy
  have := Kf_monotoneOn (c := 4 * ρ) (x := 1 / 4) (y := 1 / 2) (by positivity) (by norm_num)
    (by nlinarith) hx hy hxy
  unfold gL; linarith

theorem VL_hi {ρ : ℝ} (h : 4 * Real.exp 2 ≤ ρ) :
    eVariationOn (gL ρ) (Icc (1 / 4) (1 / 2)) =
      ENNReal.ofReal (gL ρ (1 / 4) - gL ρ (1 / 2)) := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity) h
  apply eVar_Icc_of_antitoneOn (by norm_num)
  intro x hx y hy hxy
  have := Kf_antitoneOn (c := 4 * ρ) (x := 1 / 4) (y := 1 / 2) (by positivity) (by norm_num)
    (by nlinarith) hx hy hxy
  unfold gL; linarith

theorem VR_lo {ρ : ℝ} (hρ : 0 < ρ) (h : ρ ≤ Real.exp 2) :
    eVariationOn (gR ρ) (Icc (1 / 2) 1) = ENNReal.ofReal (gR ρ (1 / 2) - gR ρ 1) := by
  apply eVar_Icc_of_antitoneOn (by norm_num)
  intro x hx y hy hxy
  have := Kf_monotoneOn (c := ρ) (x := 1 / 2) (y := 1) hρ (by norm_num)
    (by nlinarith) hx hy hxy
  unfold gR; linarith

theorem VR_hi {ρ : ℝ} (h : 4 * Real.exp 2 ≤ ρ) :
    eVariationOn (gR ρ) (Icc (1 / 2) 1) = ENNReal.ofReal (gR ρ 1 - gR ρ (1 / 2)) := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity) h
  apply eVar_Icc_of_monotoneOn (by norm_num)
  intro x hx y hy hxy
  have := Kf_antitoneOn (c := ρ) (x := 1 / 2) (y := 1) hρ (by norm_num)
    (by nlinarith) hx hy hxy
  unfold gR; linarith

theorem exp_two_eq : Real.exp 2 = Real.exp 1 ^ 2 := by
  rw [← Real.exp_nat_mul]; norm_num

/-- Location of the interior extremum of `gL ρ`: `t₀ = e / (2√ρ)`, where `4ρt₀² = e²`. -/
noncomputable def t0 (ρ : ℝ) : ℝ := Real.exp 1 / (2 * Real.sqrt ρ)
/-- Location of the interior extremum of `gR ρ`: `t₁ = e / √ρ`, where `ρt₁² = e²`. -/
noncomputable def t1 (ρ : ℝ) : ℝ := Real.exp 1 / Real.sqrt ρ

theorem mid_facts {ρ : ℝ} (h1 : Real.exp 2 ≤ ρ) (h2 : ρ ≤ 4 * Real.exp 2) :
    1 / 4 ≤ t0 ρ ∧ t0 ρ ≤ 1 / 2 ∧ 1 / 2 ≤ t1 ρ ∧ t1 ρ ≤ 1 ∧
      4 * ρ * t0 ρ ^ 2 = Real.exp 2 ∧ ρ * t1 ρ ^ 2 = Real.exp 2 ∧
      gL ρ (t0 ρ) = 16 * Real.sqrt ρ / Real.exp 1 ∧
      gR ρ (t1 ρ) = -8 * Real.sqrt ρ / Real.exp 1 := by
  have he := Real.exp_pos 1
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity) h1
  have hs := Real.sqrt_pos.2 hρ
  have hsq : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ.le
  have e2 := exp_two_eq
  have lo : Real.exp 1 ≤ Real.sqrt ρ := by
    rw [← Real.sqrt_sq he.le]; exact Real.sqrt_le_sqrt (by rw [← e2]; exact h1)
  have hi : Real.sqrt ρ ≤ 2 * Real.exp 1 := by
    rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * Real.exp 1)]
    exact Real.sqrt_le_sqrt (by rw [mul_pow, ← e2]; linarith)
  have q0 : 4 * ρ * t0 ρ ^ 2 = Real.exp 2 := by
    unfold t0; rw [div_pow, mul_pow, hsq, e2]; field_simp; ring
  have q1 : ρ * t1 ρ ^ 2 = Real.exp 2 := by
    unfold t1; rw [div_pow, hsq, e2]; field_simp
  refine ⟨?_, ?_, ?_, ?_, q0, q1, ?_, ?_⟩
  · unfold t0; rw [le_div_iff₀ (by positivity)]; linarith
  · unfold t0; rw [div_le_iff₀ (by positivity)]; linarith
  · unfold t1; rw [le_div_iff₀ hs]; linarith
  · unfold t1; rw [div_le_iff₀ hs]; linarith
  · unfold gL Kf; rw [q0, Real.log_exp]; unfold t0; field_simp; ring
  · unfold gR Kf; rw [q1, Real.log_exp]; unfold t1; field_simp; try norm_num

theorem gL_mono_mid {ρ : ℝ} (h1 : Real.exp 2 ≤ ρ) (h2 : ρ ≤ 4 * Real.exp 2) :
    MonotoneOn (gL ρ) (Icc (1 / 4) (t0 ρ)) := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity) h1
  intro x hx y hy hxy
  have := Kf_monotoneOn (c := 4 * ρ) (x := 1 / 4) (y := t0 ρ) (by positivity) (by norm_num)
    (mid_facts h1 h2).2.2.2.2.1.le hx hy hxy
  unfold gL; linarith

theorem gL_anti_mid {ρ : ℝ} (h1 : Real.exp 2 ≤ ρ) (h2 : ρ ≤ 4 * Real.exp 2) :
    AntitoneOn (gL ρ) (Icc (t0 ρ) (1 / 2)) := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity) h1
  have a1 := (mid_facts h1 h2).1
  intro x hx y hy hxy
  have := Kf_antitoneOn (c := 4 * ρ) (x := t0 ρ) (y := 1 / 2) (by positivity) (by linarith)
    (mid_facts h1 h2).2.2.2.2.1.ge hx hy hxy
  unfold gL; linarith

theorem gR_anti_mid {ρ : ℝ} (h1 : Real.exp 2 ≤ ρ) (h2 : ρ ≤ 4 * Real.exp 2) :
    AntitoneOn (gR ρ) (Icc (1 / 2) (t1 ρ)) := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity) h1
  intro x hx y hy hxy
  have := Kf_monotoneOn (c := ρ) (x := 1 / 2) (y := t1 ρ) hρ (by norm_num)
    (mid_facts h1 h2).2.2.2.2.2.1.le hx hy hxy
  unfold gR; linarith

theorem gR_mono_mid {ρ : ℝ} (h1 : Real.exp 2 ≤ ρ) (h2 : ρ ≤ 4 * Real.exp 2) :
    MonotoneOn (gR ρ) (Icc (t1 ρ) 1) := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity) h1
  have b1 := (mid_facts h1 h2).2.2.1
  intro x hx y hy hxy
  have := Kf_antitoneOn (c := ρ) (x := t1 ρ) (y := 1) hρ (by linarith)
    (mid_facts h1 h2).2.2.2.2.2.1.ge hx hy hxy
  unfold gR; linarith

theorem VL_mid {ρ : ℝ} (h1 : Real.exp 2 ≤ ρ) (h2 : ρ ≤ 4 * Real.exp 2) :
    eVariationOn (gL ρ) (Icc (1 / 4) (1 / 2)) =
      ENNReal.ofReal (2 * gL ρ (t0 ρ) - gL ρ (1 / 4) - gL ρ (1 / 2)) := by
  obtain ⟨a1, a2, -, -, q0, -, -, -⟩ := mid_facts h1 h2
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity) h1
  have sp := eVariationOn.Icc_add_Icc (gL ρ) a1 a2 (mem_univ _)
  simp only [univ_inter] at sp
  have m1 : MonotoneOn (gL ρ) (Icc (1 / 4) (t0 ρ)) := by
    intro x hx y hy hxy
    have := Kf_monotoneOn (c := 4 * ρ) (x := 1 / 4) (y := t0 ρ) (by positivity) (by norm_num)
      q0.le hx hy hxy
    unfold gL; linarith
  have m2 : AntitoneOn (gL ρ) (Icc (t0 ρ) (1 / 2)) := by
    intro x hx y hy hxy
    have := Kf_antitoneOn (c := 4 * ρ) (x := t0 ρ) (y := 1 / 2) (by positivity)
      (by linarith) q0.ge hx hy hxy
    unfold gL; linarith
  have i1 := m1 ⟨le_rfl, a1⟩ ⟨a1, le_rfl⟩ a1
  have i2 := m2 ⟨le_rfl, a2⟩ ⟨a2, le_rfl⟩ a2
  rw [← sp, eVar_Icc_of_monotoneOn a1 m1, eVar_Icc_of_antitoneOn a2 m2,
    ← ENNReal.ofReal_add (by linarith) (by linarith)]
  congr 1; ring

theorem VR_mid {ρ : ℝ} (h1 : Real.exp 2 ≤ ρ) (h2 : ρ ≤ 4 * Real.exp 2) :
    eVariationOn (gR ρ) (Icc (1 / 2) 1) =
      ENNReal.ofReal (gR ρ (1 / 2) + gR ρ 1 - 2 * gR ρ (t1 ρ)) := by
  obtain ⟨-, -, a1, a2, -, q1, -, -⟩ := mid_facts h1 h2
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity) h1
  have sp := eVariationOn.Icc_add_Icc (gR ρ) a1 a2 (mem_univ _)
  simp only [univ_inter] at sp
  have m1 : AntitoneOn (gR ρ) (Icc (1 / 2) (t1 ρ)) := by
    intro x hx y hy hxy
    have := Kf_monotoneOn (c := ρ) (x := 1 / 2) (y := t1 ρ) hρ (by norm_num) q1.le hx hy hxy
    unfold gR; linarith
  have m2 : MonotoneOn (gR ρ) (Icc (t1 ρ) 1) := by
    intro x hx y hy hxy
    have := Kf_antitoneOn (c := ρ) (x := t1 ρ) (y := 1) hρ (by linarith) q1.ge hx hy hxy
    unfold gR; linarith
  have i1 := m1 ⟨le_rfl, a1⟩ ⟨a1, le_rfl⟩ a1
  have i2 := m2 ⟨le_rfl, a2⟩ ⟨a2, le_rfl⟩ a2
  rw [← sp, eVar_Icc_of_antitoneOn a1 m1, eVar_Icc_of_monotoneOn a2 m2,
    ← ENNReal.ofReal_add (by linarith) (by linarith)]
  congr 1; ring

/-! ### The total variation identity -/

/-- Hypotheses on a representative `D` of `η_{2,ρ}'`: the piece formulas off the three
breakpoints, and at each breakpoint a value between the one-sided limits. -/
structure IsEta2rhoDeriv (ρ : ℝ) (D : ℝ → ℝ) : Prop where
  lo : ∀ t, t < 1 / 4 → D t = 0
  hi : ∀ t, 1 < t → D t = 0
  left : ∀ t ∈ Ioo (1 / 4 : ℝ) (1 / 2), D t = gL ρ t
  right : ∀ t ∈ Ioo (1 / 2 : ℝ) 1, D t = gR ρ t
  at_quarter : D (1 / 4) ∈ Icc 0 (gL ρ (1 / 4))
  at_half : D (1 / 2) ∈ Icc (gR ρ (1 / 2)) (gL ρ (1 / 2))
  at_one : D 1 ∈ Icc (gR ρ 1) 0

/-- Total variation identity: jumps at `1/4`, `1/2`, `1` plus the variation of each piece. -/
theorem eta2rho_TV_identity {ρ : ℝ} (hρ : 0 < ρ) {D : ℝ → ℝ} (hD : IsEta2rhoDeriv ρ D) :
    eVariationOn D (Icc 0 2) =
      ENNReal.ofReal (gL ρ (1 / 4)) + eVariationOn (gL ρ) (Icc (1 / 4) (1 / 2)) +
        ENNReal.ofReal (gL ρ (1 / 2) - gR ρ (1 / 2)) + eVariationOn (gR ρ) (Icc (1 / 2) 1) +
        ENNReal.ofReal (-gR ρ 1) := by
  have s1 := eVariationOn.Icc_add_Icc D (a := 0) (b := 1 / 4) (c := 2) (by norm_num)
    (by norm_num) (mem_univ _)
  have s2 := eVariationOn.Icc_add_Icc D (a := 1 / 4) (b := 1 / 2) (c := 2) (by norm_num)
    (by norm_num) (mem_univ _)
  have s3 := eVariationOn.Icc_add_Icc D (a := 1 / 2) (b := 1) (c := 2) (by norm_num)
    (by norm_num) (mem_univ _)
  simp only [univ_inter] at s1 s2 s3
  have P0 : eVariationOn D (Icc 0 (1 / 4)) = edist 0 (D (1 / 4)) := by
    rw [eVar_Icc_of_eqOn_Ioo (φ := fun _ => (0 : ℝ)) (by norm_num) continuousOn_const
      (fun t ht => hD.lo t ht.2), eVar_const_zero, hD.lo 0 (by norm_num)]
    simp only [edist_self, zero_add]
  have P1 := eVar_Icc_of_eqOn_Ioo (by norm_num) (gL_continuousOn hρ) hD.left
  have P2 := eVar_Icc_of_eqOn_Ioo (by norm_num) (gR_continuousOn hρ) hD.right
  have P3 : eVariationOn D (Icc 1 2) = edist (D 1) 0 := by
    rw [eVar_Icc_of_eqOn_Ioo (φ := fun _ => (0 : ℝ)) (by norm_num) continuousOn_const
      (fun t ht => hD.hi t ht.1), eVar_const_zero, hD.hi 2 (by norm_num)]
    simp only [edist_self, add_zero]
  have e1 : edist 0 (D (1 / 4)) + edist (D (1 / 4)) (gL ρ (1 / 4)) =
      ENNReal.ofReal (gL ρ (1 / 4)) := by
    rw [edist_add_edist_of_le hD.at_quarter.1 hD.at_quarter.2, sub_zero]
  have e2 : edist (gL ρ (1 / 2)) (D (1 / 2)) + edist (D (1 / 2)) (gR ρ (1 / 2)) =
      ENNReal.ofReal (gL ρ (1 / 2) - gR ρ (1 / 2)) := by
    rw [add_comm, edist_comm (D (1 / 2)) (gR ρ (1 / 2)), edist_comm (gL ρ (1 / 2)) (D (1 / 2)),
      edist_add_edist_of_le hD.at_half.1 hD.at_half.2]
  have e3 : edist (gR ρ 1) (D 1) + edist (D 1) 0 = ENNReal.ofReal (-gR ρ 1) := by
    rw [edist_add_edist_of_le hD.at_one.1 hD.at_one.2, zero_sub]
  rw [← s1, ← s2, ← s3, P0, P1, P2, P3, ← e1, ← e2, ← e3]
  ring

/-- The same total variation over the whole line. -/
theorem eta2rho_TV_univ {ρ : ℝ} {D : ℝ → ℝ} (hD : IsEta2rhoDeriv ρ D) :
    eVariationOn D univ = eVariationOn D (Icc 0 2) := by
  have u1 := eVariationOn.union D (isGreatest_Iic (a := (0 : ℝ))) (isLeast_Ici (a := 0))
  have u2 := eVariationOn.union D (isGreatest_Icc (by norm_num : (0 : ℝ) ≤ 2))
    (isLeast_Ici (a := 2))
  rw [Iic_union_Ici] at u1
  rw [Icc_union_Ici_eq_Ici (by norm_num)] at u2
  have z1 : eVariationOn D (Iic 0) = 0 := by
    rw [eVariationOn.eq_of_eqOn (f' := fun _ => (0 : ℝ)) (s := Iic 0)
      (fun t (ht : t ≤ 0) => hD.lo t (lt_of_le_of_lt ht (by norm_num))), eVar_const_zero]
  have z2 : eVariationOn D (Ici 2) = 0 := by
    rw [eVariationOn.eq_of_eqOn (f' := fun _ => (0 : ℝ)) (s := Ici 2)
      (fun t (ht : 2 ≤ t) => hD.hi t (lt_of_lt_of_le (by norm_num) ht)), eVar_const_zero]
  rw [u1, z1, zero_add, u2, z2, add_zero]

/-! ### Closed forms -/

theorem sum5_ofReal {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) :
    ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c + ENNReal.ofReal d +
      ENNReal.ofReal e = ENNReal.ofReal (a + b + c + d + e) := by
  rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_add (by linarith) hc,
    ← ENNReal.ofReal_add (by linarith) hd, ← ENNReal.ofReal_add (by linarith) he]

theorem log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

theorem log_sixteen_eq : Real.log 16 = 4 * Real.log 2 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num

theorem exp_two_lt_sixteen : Real.exp 2 < 16 := by
  rw [exp_two_eq]; have := Real.exp_one_lt_d9; have := Real.exp_pos 1; nlinarith

theorem four_le_exp_two : 4 ≤ Real.exp 2 := by
  rw [exp_two_eq]; have := Real.add_one_le_exp 1; nlinarith

/-- Regime `4 ≤ ρ ≤ e²`: each piece is monotone, total variation `24 log ρ`. -/
theorem eta2rho_TV_lo {ρ : ℝ} (h4 : 4 ≤ ρ) (h : ρ ≤ Real.exp 2) {D : ℝ → ℝ}
    (hD : IsEta2rhoDeriv ρ D) :
    eVariationOn D (Icc 0 2) = ENNReal.ofReal (24 * Real.log ρ) := by
  have hρ : 0 < ρ := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log (ρ / 4) = Real.log ρ - 2 * Real.log 2 := by
    rw [Real.log_div hρ.ne' (by norm_num), log_four_eq]
  have hL0 : 0 ≤ Real.log (ρ / 4) := Real.log_nonneg (by linarith)
  have h16 : Real.log ρ ≤ 4 * Real.log 2 := by
    rw [← log_sixteen_eq]; exact Real.log_le_log hρ (by linarith [exp_two_lt_sixteen])
  rw [eta2rho_TV_identity hρ hD, VL_lo hρ h, VR_lo hρ h, gL_quarter, gL_half, gR_half, gR_one,
    sum5_ofReal (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
  congr 1; rw [hL]; ring

/-- Regime `ρ ≥ 4e²`: each piece is monotone, total variation `48 log(ρ/4)`. -/
theorem eta2rho_TV_hi {ρ : ℝ} (h : 4 * Real.exp 2 ≤ ρ) {D : ℝ → ℝ}
    (hD : IsEta2rhoDeriv ρ D) :
    eVariationOn D (Icc 0 2) = ENNReal.ofReal (48 * Real.log (ρ / 4)) := by
  have h16 : 16 ≤ ρ := by linarith [four_le_exp_two]
  have hρ : 0 < ρ := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log (ρ / 4) = Real.log ρ - 2 * Real.log 2 := by
    rw [Real.log_div hρ.ne' (by norm_num), log_four_eq]
  have hl16 : 4 * Real.log 2 ≤ Real.log ρ := by
    rw [← log_sixteen_eq]; exact Real.log_le_log (by norm_num) h16
  rw [eta2rho_TV_identity hρ hD, VL_hi h, VR_hi h, gL_quarter, gL_half, gR_half, gR_one,
    sum5_ofReal (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
  congr 1; rw [hL]; ring

/-- Regime `e² ≤ ρ ≤ 4e²`, the interior extremum case: total variation `48 √ρ / e`. -/
theorem eta2rho_TV_mid {ρ : ℝ} (h1 : Real.exp 2 ≤ ρ) (h2 : ρ ≤ 4 * Real.exp 2) {D : ℝ → ℝ}
    (hD : IsEta2rhoDeriv ρ D) :
    eVariationOn D (Icc 0 2) = ENNReal.ofReal (48 * Real.sqrt ρ / Real.exp 1) := by
  have h4 : 4 ≤ ρ := le_trans four_le_exp_two h1
  have hρ : 0 < ρ := by linarith
  obtain ⟨a1, a2, b1, b2, -, -, v0, v1⟩ := mid_facts h1 h2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log (ρ / 4) = Real.log ρ - 2 * Real.log 2 := by
    rw [Real.log_div hρ.ne' (by norm_num), log_four_eq]
  have hL0 : 0 ≤ Real.log (ρ / 4) := Real.log_nonneg (by linarith)
  have hlρ : 0 ≤ Real.log ρ := Real.log_nonneg (by linarith)
  -- nonnegativity of the piece variations, from the variation formulas themselves
  have i1 := gL_mono_mid h1 h2 ⟨le_rfl, a1⟩ ⟨a1, le_rfl⟩ a1
  have i2 := gL_anti_mid h1 h2 ⟨le_rfl, a2⟩ ⟨a2, le_rfl⟩ a2
  have i3 := gR_anti_mid h1 h2 ⟨le_rfl, b1⟩ ⟨b1, le_rfl⟩ b1
  have i4 := gR_mono_mid h1 h2 ⟨le_rfl, b2⟩ ⟨b2, le_rfl⟩ b2
  have nL : 0 ≤ 2 * gL ρ (t0 ρ) - gL ρ (1 / 4) - gL ρ (1 / 2) := by linarith
  have nR : 0 ≤ gR ρ (1 / 2) + gR ρ 1 - 2 * gR ρ (t1 ρ) := by linarith
  rw [eta2rho_TV_identity hρ hD, VL_mid h1 h2, VR_mid h1 h2,
    sum5_ofReal (by rw [gL_quarter]; linarith) nL
      (by rw [gL_half, gR_half]; linarith) nR (by rw [gR_one]; linarith)]
  congr 1; rw [v0, v1]; ring

/-- 1205.5252 eq. (2.6), third line, final bound: `|η_{2,ρ}''|₁ < 48 log ρ` for `ρ ≥ 4`,
with `|η_{2,ρ}''|₁` read as the total variation of `η_{2,ρ}'`. -/
theorem eta2rho_TV_lt {ρ : ℝ} (h4 : 4 ≤ ρ) {D : ℝ → ℝ} (hD : IsEta2rhoDeriv ρ D) :
    eVariationOn D (Icc 0 2) < ENNReal.ofReal (48 * Real.log ρ) := by
  have hρ : 0 < ρ := by linarith
  have hl : 0 < Real.log ρ := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt ρ (Real.exp 2) with h | h
  · rw [eta2rho_TV_lo h4 h hD, ENNReal.ofReal_lt_ofReal_iff (by positivity)]; linarith
  rcases le_or_gt (4 * Real.exp 2) ρ with h' | h'
  · rw [eta2rho_TV_hi h' hD, ENNReal.ofReal_lt_ofReal_iff (by positivity),
      Real.log_div hρ.ne' (by norm_num), log_four_eq]; nlinarith
  · rw [eta2rho_TV_mid h.le h'.le hD, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have he := Real.exp_pos 1
    have hi : Real.sqrt ρ ≤ 2 * Real.exp 1 := by
      rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * Real.exp 1)]
      exact Real.sqrt_le_sqrt (by rw [mul_pow, ← exp_two_eq]; linarith)
    have : 2 < Real.log ρ := (Real.lt_log_iff_exp_lt hρ).2 h
    rw [div_lt_iff₀ he]; nlinarith

/-! ### Comparison with the printed third line of (2.6), `printed26` from Weights.lean -/

/-- Four times the printed sum is the sum of the jumps of `η_{2,ρ}'` and of the end to end
increments of its two smooth pieces. -/
theorem four_printed26_eq {ρ : ℝ} (h4 : 4 ≤ ρ) :
    4 * printed26 ρ = gL ρ (1 / 4) + |gL ρ (1 / 4) - gL ρ (1 / 2)| +
      (gL ρ (1 / 2) - gR ρ (1 / 2)) + |gR ρ (1 / 2) - gR ρ 1| + -gR ρ 1 := by
  have hρ : 0 < ρ := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log (ρ / 4) = Real.log ρ - 2 * Real.log 2 := by
    rw [Real.log_div hρ.ne' (by norm_num), log_four_eq]
  have hl4 : 2 * Real.log 2 ≤ Real.log ρ := by
    rw [← log_four_eq]; exact Real.log_le_log (by norm_num) h4
  unfold printed26
  rw [gL_quarter, gL_half, gR_half, gR_one, hL]
  have a1 : |4 * Real.log 2 - 4 * Real.log ρ| = 4 * Real.log ρ - 4 * Real.log 2 := by
    rw [abs_of_nonpos (by linarith)]; ring
  have a2 : |Real.log ρ| = Real.log ρ := abs_of_nonneg (by linarith)
  rw [a1, a2]
  rcases le_total (Real.log ρ) (4 * Real.log 2) with h | h
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * Real.log ρ - 4 * (Real.log ρ - 2 * Real.log 2)),
      abs_of_nonpos (by linarith : Real.log ρ - 4 * Real.log 2 ≤ 0),
      abs_of_nonpos (by linarith : 16 * (Real.log ρ - 2 * Real.log 2) - 8 * Real.log ρ ≤ 0),
      abs_of_nonneg (by linarith :
        (0:ℝ) ≤ -8 * (Real.log ρ - 2 * Real.log 2) - -4 * Real.log ρ)]
    ring
  · rw [abs_of_nonpos (by linarith : 2 * Real.log ρ - 4 * (Real.log ρ - 2 * Real.log 2) ≤ 0),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.log ρ - 4 * Real.log 2),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 16 * (Real.log ρ - 2 * Real.log 2) - 8 * Real.log ρ),
      abs_of_nonpos (by linarith :
        -8 * (Real.log ρ - 2 * Real.log 2) - -4 * Real.log ρ ≤ 0)]
    ring

/-- For every `ρ ≥ 4`, four times the printed sum is at most the total variation. -/
theorem four_printed26_le_TV {ρ : ℝ} (h4 : 4 ≤ ρ) {D : ℝ → ℝ} (hD : IsEta2rhoDeriv ρ D) :
    ENNReal.ofReal (4 * printed26 ρ) ≤ eVariationOn D (Icc 0 2) := by
  have hρ : 0 < ρ := by linarith
  have hL0 : 0 ≤ Real.log (ρ / 4) := Real.log_nonneg (by linarith)
  have hlρ : 0 ≤ Real.log ρ := Real.log_nonneg (by linarith)
  have jq : 0 ≤ gL ρ (1 / 4) := by rw [gL_quarter]; linarith
  have jh : 0 ≤ gL ρ (1 / 2) - gR ρ (1 / 2) := by rw [gL_half, gR_half]; linarith
  have j1 : 0 ≤ -gR ρ 1 := by rw [gR_one]; linarith
  rw [four_printed26_eq h4, ← sum5_ofReal jq (abs_nonneg _) jh (abs_nonneg _) j1,
    eta2rho_TV_identity hρ hD]
  have vL := eVariationOn.edist_le (gL ρ) (s := Icc (1 / 4 : ℝ) (1 / 2))
    ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
  have vR := eVariationOn.edist_le (gR ρ) (s := Icc (1 / 2 : ℝ) 1)
    ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
  rw [edist_dist, Real.dist_eq] at vL vR
  gcongr

/-- Outside the open regime `e² < ρ < 4e²`, the total variation is exactly four times the
printed sum. -/
theorem TV_eq_four_printed26 {ρ : ℝ} (h4 : 4 ≤ ρ)
    (hout : ρ ≤ Real.exp 2 ∨ 4 * Real.exp 2 ≤ ρ) {D : ℝ → ℝ} (hD : IsEta2rhoDeriv ρ D) :
    eVariationOn D (Icc 0 2) = ENNReal.ofReal (4 * printed26 ρ) := by
  have hρ : 0 < ρ := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log (ρ / 4) = Real.log ρ - 2 * Real.log 2 := by
    rw [Real.log_div hρ.ne' (by norm_num), log_four_eq]
  rw [four_printed26_eq h4, gL_quarter, gL_half, gR_half, gR_one, hL]
  rcases hout with h | h
  · have h16 : Real.log ρ ≤ 4 * Real.log 2 := by
      rw [← log_sixteen_eq]; exact Real.log_le_log hρ (by linarith [exp_two_lt_sixteen])
    rw [eta2rho_TV_lo h4 h hD,
      abs_of_nonpos (by linarith : 16 * (Real.log ρ - 2 * Real.log 2) - 8 * Real.log ρ ≤ 0),
      abs_of_nonneg (by linarith :
        (0:ℝ) ≤ -8 * (Real.log ρ - 2 * Real.log 2) - -4 * Real.log ρ)]
    congr 1; ring
  · have h16 : 4 * Real.log 2 ≤ Real.log ρ := by
      rw [← log_sixteen_eq]; exact Real.log_le_log (by norm_num) (by linarith [four_le_exp_two])
    rw [eta2rho_TV_hi h hD, hL,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 16 * (Real.log ρ - 2 * Real.log 2) - 8 * Real.log ρ),
      abs_of_nonpos (by linarith :
        -8 * (Real.log ρ - 2 * Real.log 2) - -4 * Real.log ρ ≤ 0)]
    congr 1; ring

/-! ### The actual derivative `deriv η_{2,ρ}` is an admissible representative -/

theorem deriv_eq_zero_or_of_hasDerivWithinAt {f : ℝ → ℝ} {a b d : ℝ} (hab : a < b)
    (h : HasDerivWithinAt f d (Icc a b) b) : deriv f b = 0 ∨ deriv f b = d := by
  by_cases hd : DifferentiableAt ℝ f b
  · right
    exact (uniqueDiffOn_Icc hab b ⟨hab.le, le_rfl⟩).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt h
  · left; exact deriv_zero_of_not_differentiableAt hd

theorem FL_hasDerivAt {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    HasDerivAt (fun s => Real.log (ρ * s) * (4 * Real.log (4 * s))) (gL ρ t) t := by
  have hl : HasDerivAt (fun s => Real.log (ρ * s)) (ρ * 1 / (ρ * t)) t :=
    ((hasDerivAt_id t).const_mul ρ).log (by simp only [id]; positivity)
  have h4 : HasDerivAt (fun s => 4 * Real.log (4 * s)) (4 * (4 * 1 / (4 * t))) t :=
    (((hasDerivAt_id t).const_mul 4).log (by simp only [id]; positivity)).const_mul 4
  convert hl.mul h4 using 1
  unfold gL Kf
  rw [show 4 * ρ * t ^ 2 = (4 * t) * (ρ * t) by ring,
    Real.log_mul (by positivity) (by positivity)]
  field_simp
  try ring

theorem FR_hasDerivAt {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    HasDerivAt (fun s => Real.log (ρ * s) * (-4 * Real.log s)) (gR ρ t) t := by
  have hl : HasDerivAt (fun s => Real.log (ρ * s)) (ρ * 1 / (ρ * t)) t :=
    ((hasDerivAt_id t).const_mul ρ).log (by simp only [id]; positivity)
  have h4 : HasDerivAt (fun s => -4 * Real.log s) (-4 * t⁻¹) t :=
    (Real.hasDerivAt_log ht.ne').const_mul (-4)
  convert hl.mul h4 using 1
  unfold gR Kf
  rw [show ρ * t ^ 2 = t * (ρ * t) by ring,
    Real.log_mul (by positivity) (by positivity)]
  field_simp
  try ring

/-- For `ρ ≥ 4`, Mathlib's `deriv (eta2rho ρ)`, which is `0` where `η_{2,ρ}` is not
differentiable, satisfies `IsEta2rhoDeriv`. -/
theorem deriv_eta2rho_isRep {ρ : ℝ} (h4 : 4 ≤ ρ) : IsEta2rhoDeriv ρ (deriv (eta2rho ρ)) := by
  have hρ : 0 < ρ := by linarith
  have hL0 : 0 ≤ Real.log (ρ / 4) := Real.log_nonneg (by linarith)
  have hlρ : 0 ≤ Real.log ρ := Real.log_nonneg (by linarith)
  refine ⟨fun t ht => (eta2rho_hasDerivAt_out (Or.inl ht)).deriv,
    fun t ht => (eta2rho_hasDerivAt_out (Or.inr ht)).deriv,
    fun t ht => (eta2rho_hasDerivAt_left hρ ht.1 ht.2).deriv,
    fun t ht => (eta2rho_hasDerivAt_right hρ ht.1 ht.2).deriv, ?_, ?_, ?_⟩
  · have e0 : eta2 (1 / 4) = 0 := by
      rw [eta2_of_mem_left le_rfl (by norm_num)]; norm_num
    have hz : HasDerivWithinAt (eta2rho ρ) 0 (Icc 0 (1 / 4)) (1 / 4) := by
      refine (hasDerivWithinAt_const (1 / 4 : ℝ) (Icc 0 (1 / 4)) (0 : ℝ)).congr ?_ ?_
      · intro s hs
        show Real.log (ρ * s) * eta2 s = 0
        rcases hs.2.lt_or_eq with h | h
        · rw [eta2_of_lt h, mul_zero]
        · rw [h, e0, mul_zero]
      · show Real.log (ρ * (1 / 4)) * eta2 (1 / 4) = 0
        rw [e0, mul_zero]
    rcases deriv_eq_zero_or_of_hasDerivWithinAt (by norm_num) hz with h | h <;>
      rw [h, gL_quarter] <;> exact ⟨le_rfl, by linarith⟩
  · have hz : HasDerivWithinAt (eta2rho ρ) (gL ρ (1 / 2)) (Icc (1 / 4) (1 / 2)) (1 / 2) := by
      refine (FL_hasDerivAt hρ (by norm_num)).hasDerivWithinAt.congr ?_ ?_
      · intro s hs; simp only [eta2rho]; rw [eta2_of_mem_left hs.1 hs.2]
      · simp only [eta2rho]; rw [eta2_of_mem_left (by norm_num) le_rfl]
    rcases deriv_eq_zero_or_of_hasDerivWithinAt (by norm_num) hz with h | h <;>
      rw [h] <;> rw [gL_half, gR_half] <;> constructor <;> linarith
  · have hz : HasDerivWithinAt (eta2rho ρ) (gR ρ 1) (Icc (1 / 2) 1) 1 := by
      refine (FR_hasDerivAt hρ (by norm_num)).hasDerivWithinAt.congr ?_ ?_
      · intro s hs; simp only [eta2rho]; rw [eta2_of_mem_right hs.1 hs.2]
      · simp only [eta2rho]; rw [eta2_of_mem_right (by norm_num) le_rfl]
    rcases deriv_eq_zero_or_of_hasDerivWithinAt (by norm_num) hz with h | h <;>
      rw [h] <;> rw [gR_one] <;> constructor <;> linarith

/-- Headline: for `ρ ≥ 4` the total variation over `ℝ` of `deriv η_{2,ρ}` is below
`48 log ρ`, the bound printed at the end of 1205.5252 eq. (2.6). -/
theorem eVariation_deriv_eta2rho_lt {ρ : ℝ} (h4 : 4 ≤ ρ) :
    eVariationOn (deriv (eta2rho ρ)) univ < ENNReal.ofReal (48 * Real.log ρ) := by
  rw [eta2rho_TV_univ (deriv_eta2rho_isRep h4)]
  exact eta2rho_TV_lt h4 (deriv_eta2rho_isRep h4)

/-- Interior extremum regime for the actual derivative, over `ℝ`. -/
theorem eVariation_deriv_eta2rho_mid {ρ : ℝ} (h1 : Real.exp 2 ≤ ρ) (h2 : ρ ≤ 4 * Real.exp 2) :
    eVariationOn (deriv (eta2rho ρ)) univ =
      ENNReal.ofReal (48 * Real.sqrt ρ / Real.exp 1) := by
  have h4 : 4 ≤ ρ := le_trans four_le_exp_two h1
  rw [eta2rho_TV_univ (deriv_eta2rho_isRep h4)]
  exact eta2rho_TV_mid h1 h2 (deriv_eta2rho_isRep h4)

/-- Vacuity check: `ρ = 2e²` lies in the interior extremum regime, and `ρ = 4` and
`ρ = 4e²` in the outer ones. -/
example : Real.exp 2 ≤ 2 * Real.exp 2 ∧ 2 * Real.exp 2 ≤ 4 * Real.exp 2 := by
  constructor <;> linarith [Real.exp_pos 2]
example : (4 : ℝ) ≤ 4 ∧ (4 : ℝ) ≤ Real.exp 2 := ⟨le_rfl, four_le_exp_two⟩
example : IsEta2rhoDeriv 4 (deriv (eta2rho 4)) := deriv_eta2rho_isRep le_rfl

#print axioms eVar_Icc_of_monotoneOn
#print axioms eVar_neg
#print axioms eVar_Icc_of_antitoneOn
#print axioms eVar_const_zero
#print axioms eVar_Icc_of_eqOn_Ioo
#print axioms edist_add_edist_of_le
#print axioms Kf_hasDerivAt
#print axioms Kf_continuousOn
#print axioms Kf_monotoneOn
#print axioms Kf_antitoneOn
#print axioms eta2rho_hasDerivAt_left
#print axioms eta2rho_hasDerivAt_right
#print axioms eta2rho_hasDerivAt_out
#print axioms gL_quarter
#print axioms gL_half
#print axioms gR_half
#print axioms gR_one
#print axioms gL_continuousOn
#print axioms gR_continuousOn
#print axioms VL_lo
#print axioms VL_hi
#print axioms VR_lo
#print axioms VR_hi
#print axioms exp_two_eq
#print axioms mid_facts
#print axioms gL_mono_mid
#print axioms gL_anti_mid
#print axioms gR_anti_mid
#print axioms gR_mono_mid
#print axioms VL_mid
#print axioms VR_mid
#print axioms eta2rho_TV_identity
#print axioms eta2rho_TV_univ
#print axioms sum5_ofReal
#print axioms log_four_eq
#print axioms log_sixteen_eq
#print axioms exp_two_lt_sixteen
#print axioms four_le_exp_two
#print axioms eta2rho_TV_lo
#print axioms eta2rho_TV_hi
#print axioms eta2rho_TV_mid
#print axioms eta2rho_TV_lt
#print axioms four_printed26_eq
#print axioms four_printed26_le_TV
#print axioms TV_eq_four_printed26
#print axioms deriv_eq_zero_or_of_hasDerivWithinAt
#print axioms FL_hasDerivAt
#print axioms FR_hasDerivAt
#print axioms deriv_eta2rho_isRep
#print axioms eVariation_deriv_eta2rho_lt
#print axioms eVariation_deriv_eta2rho_mid

end LeanLab.HelfgottArcs
