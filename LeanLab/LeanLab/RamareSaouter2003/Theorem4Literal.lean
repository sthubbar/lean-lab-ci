import Mathlib
import LeanLab.RamareSaouter2003.Theorem4JSplit

/-!
# Ramaré-Saouter 2003, displays (15) and (16) with `δ = m u` as printed

P0099, unit U-1346, run 20261021T0203Z-29730. AI-written Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN.

VERIFY U-1333 nit: `JLower` and `JLower15` let `δ` and `u` vary independently, while the
paper fixes `δ = m u` in the first sentence of the proof of Theorem 4, "We put δ = mu and
e^u X (1 + δ(1 - a)) = Y so that X ≥ 0.999 Y", printed p. 17 of J. Number Theory 98 (2003),
no display number. Displays (15) and (16) are on p. 20 by the earlier page image check of the
lab, p. 19 by the running header of the 2026-10-21 text extraction of gap.pdf.

* `JLower15Lit NT Zs T0`: display (15) with `δ := m u` substituted, for `2 ≤ m`,
  `m u ≤ 10^-4`, the hypothesis of Theorem 4, `X ≥ 10^12`, `10^3 ≤ T ≤ T0`. CITED.
* `JLowerLit NT T0`: display (16) before the `α1` step, with `δ := m u`. CITED.
* `jLower15Lit_of_jLower15`, `jLowerLit_of_jLower`: the old free-`δ` inputs imply the literal
  ones. PROVED unconditional, pure specialisation. The converse is not claimed: the literal
  inputs are weaker Props.
* `jLowerLit_of`: (16) from (15) and Lemma 3, literal. PROVED CONDITIONAL ON `JLower15Lit`,
  `Lemma3Bound`.
* `theorem4Fm_of_lit`: Theorem 4 for `f_m` from the literal (16). PROVED CONDITIONAL ON
  `MVBrunTitchmarsh`, `SchoenfeldPT 0.998697 1.001093`, `JLowerLit`. The proof is the proof of
  `Thm4Assembly.theorem4Fm_of` with the single use of the input at `δ = m u`.
* `theorem4Fm_of_split_lit`, `theorem2At1e20_of_split_lit`: the same on `JLower15Lit` and
  `Lemma3Bound`.
-/

namespace LeanLab.RamareSaouter2003.Thm4Literal

open Real Chebyshev LeanLab.RamareSaouter2003.Smooth LeanLab.RamareSaouter2003.Thm4Parts
  LeanLab.RamareSaouter2003.Thm4Assembly LeanLab.RamareSaouter2003.Thm4JSplit

/-- **Display (15) of Ramaré-Saouter 2003, p. 20 (p. 19 by the text extraction header), with
`δ = m u` as put on p. 17**, for `f = f_m`, multiplied out by `u X ||f_m||_1`;
`Zs m T X / X` is `Σ_{|γ| > T} X^(β - 1)/|γ|^(m+1)`. CITED. -/
def JLower15Lit (NT : ℝ → ℝ) (Zs : ℕ → ℝ → ℝ → ℝ) (T0 : ℝ) : Prop :=
  ∀ (m : ℕ) (X u T : ℝ), 2 ≤ m → 10 ^ 12 ≤ X → 0 < u → (m : ℝ) * u ≤ 0.0001 →
    1000 ≤ T → T ≤ T0 →
    u * X * (1 - 1 / X ^ 2 - (1 + m * u) * (2 * NT T) / √X -
        (1 + m * u) ^ (m + 1) * muStar m * ((Real.exp u + 1) / (u * (m * u) ^ m)) *
          (Zs m T X / X)) * (∫ t in (0 : ℝ)..1, fm m t) ≤
      ∫ t in (0 : ℝ)..1, Dψ X u (m * u) t * fm m t

/-- **Display (16) of Ramaré-Saouter 2003, p. 20, before the `α1` step, with `δ = m u` as put
on p. 17**, for `f = f_m`, multiplied out by `u X ||f_m||_1`. CITED. -/
def JLowerLit (NT : ℝ → ℝ) (T0 : ℝ) : Prop :=
  ∀ (m : ℕ) (X u T : ℝ), 2 ≤ m → 10 ^ 12 ≤ X → 0 < u → (m : ℝ) * u ≤ 0.0001 →
    1000 ≤ T → T ≤ T0 →
    u * X * (1 - 1 / X ^ 2 - (1 + m * u) * (2 * NT T) / √X -
        (1 + m * u) ^ (m + 1) * muStar m * (2.0001 / (u * (m * u) ^ m)) *
          (sm m T / (√X * T ^ m) + sm m T0 / (2 * T0 ^ m))) * (∫ t in (0 : ℝ)..1, fm m t) ≤
      ∫ t in (0 : ℝ)..1, Dψ X u (m * u) t * fm m t

lemma u_small {m : ℕ} {u : ℝ} (hm : 2 ≤ m) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001) :
    u ≤ 0.00005 ∧ 0 < (m : ℝ) * u := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨?_, by positivity⟩
  have := mul_le_mul_of_nonneg_right hm2 hu.le; linarith

/-- The old free-`δ` input implies the literal one. PROVED unconditional. -/
theorem jLower15Lit_of_jLower15 {NT : ℝ → ℝ} {Zs : ℕ → ℝ → ℝ → ℝ} {T0 : ℝ}
    (h : JLower15 NT Zs T0) : JLower15Lit NT Zs T0 := by
  intro m X u T hm hX hu hmu hT hTT
  obtain ⟨hu1, hδ0⟩ := u_small hm hu hmu
  exact h m X u (m * u) T hm hX hu hu1 hδ0 hmu hT hTT

/-- The old free-`δ` (16) implies the literal one. PROVED unconditional. -/
theorem jLowerLit_of_jLower {NT : ℝ → ℝ} {T0 : ℝ} (h : JLower NT T0) : JLowerLit NT T0 := by
  intro m X u T hm hX hu hmu hT hTT
  obtain ⟨hu1, hδ0⟩ := u_small hm hu hmu
  exact h m X u (m * u) T hm hX hu hu1 hδ0 hmu hT hTT

/-- (16) from (15) and Lemma 3, both with `δ = m u`. PROVED CONDITIONAL ON `JLower15Lit` and
`Lemma3Bound`. -/
theorem jLowerLit_of {NT : ℝ → ℝ} {Zs : ℕ → ℝ → ℝ → ℝ} {T0 : ℝ} (h15 : JLower15Lit NT Zs T0)
    (hL3 : Lemma3Bound Zs T0) : JLowerLit NT T0 := by
  intro m X u T hm hX hu0 hmu hT hTT
  obtain ⟨hu, hδ0⟩ := u_small hm hu0 hmu
  have h := h15 m X u T hm hX hu0 hmu hT hTT
  set δ := (m : ℝ) * u with hδdef
  obtain ⟨hz0, hz⟩ := hL3 m T X (by omega) hT hTT (by linarith)
  have hXpos : 0 < X := by linarith
  have hsX : 0 < √X := Real.sqrt_pos.mpr hXpos
  have hXs : √X * √X = X := Real.mul_self_sqrt hXpos.le
  have hTpos : 0 < T := by linarith
  have hT0pos : 0 < T0 := by linarith
  have hTm : 0 < T ^ m := pow_pos hTpos m
  have hT0m : 0 < T0 ^ m := pow_pos hT0pos m
  -- Zs / X ≤ S
  have hZS : Zs m T X / X ≤ sm m T / (√X * T ^ m) + sm m T0 / (2 * T0 ^ m) := by
    rw [div_le_iff₀ hXpos]
    have e0 : ∀ s : ℝ, 0 < s → (sm m T / (s * T ^ m) + sm m T0 / (2 * T0 ^ m)) * (s * s) =
        sm m T * s / T ^ m + sm m T0 * (s * s) / (2 * T0 ^ m) := by
      intro s hs; field_simp
    have e := e0 √X hsX
    rw [hXs] at e
    rw [e]; exact hz
  have he : Real.exp u + 1 ≤ 2.0001 := by
    have h1 := exp_sub_one_le hu0.le (by linarith)
    have h2 : u ^ 2 ≤ 0.00005 * u := by rw [sq]; exact mul_le_mul_of_nonneg_right hu hu0.le
    linarith
  have hD : 0 < u * δ ^ m := mul_pos hu0 (pow_pos hδ0 m)
  have hc : 0 ≤ (1 + δ) ^ (m + 1) * muStar m :=
    mul_nonneg (pow_nonneg (by linarith) _) (muStar_nonneg m)
  have hZX : 0 ≤ Zs m T X / X := div_nonneg hz0 hXpos.le
  have hterm : (1 + δ) ^ (m + 1) * muStar m * ((Real.exp u + 1) / (u * δ ^ m)) * (Zs m T X / X) ≤
      (1 + δ) ^ (m + 1) * muStar m * (2.0001 / (u * δ ^ m)) *
        (sm m T / (√X * T ^ m) + sm m T0 / (2 * T0 ^ m)) := by
    rw [mul_assoc, mul_assoc ((1 + δ) ^ (m + 1) * muStar m)]
    apply mul_le_mul_of_nonneg_left _ hc
    exact mul_le_mul (div_le_div_of_nonneg_right he hD.le) hZS hZX (by positivity)
  have hF : 0 ≤ ∫ t in (0 : ℝ)..1, fm m t := by rw [norm_fm]; positivity
  have huX : 0 ≤ u * X := by positivity
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_right _ hF
  apply mul_le_mul_of_nonneg_left _ huX
  linarith

set_option maxHeartbeats 2000000 in
/-- **Theorem 4 of Ramaré-Saouter 2003 for `f = f_m`**, on the literal (16). PROVED CONDITIONAL
ON `MVBrunTitchmarsh`, `SchoenfeldPT 0.998697 1.001093` and `JLowerLit NT T0`. -/
theorem theorem4Fm_of_lit (hMV : MVBrunTitchmarsh) (hS : SchoenfeldPT 0.998697 1.001093)
    {NT : ℝ → ℝ} {T0 : ℝ} (hJ : JLowerLit NT T0) : Theorem4Fm NT T0 := by
  intro m α1 α2 α4 a Y T hm hα1 hα2 hα4 hα4' ha0 ha1 h3 hY hT hN hmu h2 hY4 hTT
  set u := uRS m α1 α2 α4 a Y T T0 with hudef
  set A3 := alpha3inv m α1 α2 α4 a with hA3
  have hYpos : 0 < Y := by linarith
  have hsY : 0 < √Y := Real.sqrt_pos.mpr hYpos
  have hu : 0 < u := by
    by_contra hneg
    push Not at hneg
    have : u * √Y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hsY.le
    linarith
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hu1 : u ≤ 0.00005 := by
    have := mul_le_mul_of_nonneg_right hm2 hu.le; linarith
  set δ := (m : ℝ) * u with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 0.0001 := hmu
  have heu1 : 1 ≤ Real.exp u := Real.one_le_exp hu.le
  have heu2 : Real.exp u ≤ 1.000101 := by
    have := exp_sub_one_le hu.le (by linarith)
    have h2 : u ^ 2 ≤ 0.00005 * u := by rw [sq]; exact mul_le_mul_of_nonneg_right hu1 hu.le
    linarith
  have hda0 : 0 ≤ δ * (1 - a) := mul_nonneg hδ0.le (by linarith)
  have hda1 : δ * (1 - a) ≤ 0.0001 := by
    have := mul_le_mul_of_nonneg_left (show 1 - a ≤ 1 by linarith) hδ0.le; linarith
  set E := Real.exp u * (1 + δ * (1 - a)) with hE
  have hE1 : 1 ≤ E := by rw [hE]; exact one_le_mul_of_one_le_of_one_le heu1 (by linarith)
  have hE2 : E ≤ 1.00021 := by
    rw [hE]
    have := mul_le_mul heu2 (show 1 + δ * (1 - a) ≤ 1.0001 by linarith) (by linarith) (by norm_num)
    linarith
  have hEpos : 0 < E := by linarith
  set X := Y / E with hXdef
  have hXE : X * E = Y := by rw [hXdef]; field_simp
  have hXpos : 0 < X := div_pos hYpos hEpos
  have hXY : X ≤ Y := by
    have := mul_le_mul_of_nonneg_left hE1 hXpos.le; linarith
  have hYX : Y ≤ 1.00021 * X := by
    have := mul_le_mul_of_nonneg_left hE2 hXpos.le; linarith
  have hX12 : 199 * 10 ^ 10 ≤ X := by linarith
  have hYeq : X * Real.exp u * (1 + δ * (1 - a)) = Y := by rw [← hXE, hE]; ring
  have hY'eq : Y * ((1 + δ * a) / (1 + δ * (1 - a))) * Real.exp (-u) = X * (1 + δ * a) := by
    rw [← hXE, hE, Real.exp_neg]
    have h1 : (0 : ℝ) < 1 + δ * (1 - a) := by linarith
    have h2 : (0 : ℝ) < Real.exp u := Real.exp_pos u
    field_simp
  rw [hY'eq]
  -- square roots
  have hsX : 0 < √X := Real.sqrt_pos.mpr hXpos
  have hsXY : √Y ≤ 1.00011 * √X := by
    have : Y ≤ (1.00011 * √X) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hXpos.le]; norm_num; linarith
    calc √Y ≤ √((1.00011 * √X) ^ 2) := Real.sqrt_le_sqrt this
      _ = 1.00011 * √X := Real.sqrt_sq (by positivity)
  have hsY3 : 1000 ≤ √Y := by
    have h := Real.sqrt_le_sqrt (show (1000 : ℝ) ^ 2 ≤ Y by norm_num; linarith)
    rwa [Real.sqrt_sq (by norm_num)] at h
  have huX : 1 < u * X := by
    have : u * Y = u * √Y * √Y := by rw [mul_assoc, Real.mul_self_sqrt hYpos.le]
    have h' : 1 * 1000 ≤ u * √Y * √Y :=
      mul_le_mul (by linarith) hsY3 (by norm_num) (by positivity)
    have := mul_le_mul_of_nonneg_left hYX hu.le
    linarith
  -- the test function
  have hfc : ContinuousOn (fm m) (Set.Icc 0 1) := (continuous_fm m).continuousOn
  have hf0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ fm m t := fun t ht => fm_nonneg m ht
  set F := ∫ t in (0 : ℝ)..1, fm m t with hF
  have hFpos : 0 < F := by rw [hF, norm_fm]; positivity
  set V := v (fm m) a with hV
  have hwV : w m a * F = V := by
    rw [show w m a = V / F from rfl]; field_simp
  have hmid : ∫ t in a..(1 - a), fm m t = F - V := by
    have ii : ∀ c d : ℝ, IntervalIntegrable (fm m) MeasureTheory.volume c d :=
      fun c d => (continuous_fm m).intervalIntegrable c d
    have e1 := intervalIntegral.integral_add_adjacent_intervals (ii 0 a) (ii a (1 - a))
    have e2 := intervalIntegral.integral_add_adjacent_intervals (ii 0 (1 - a)) (ii (1 - a) 1)
    simp only [hV, v, hF]
    linarith
  -- (10), (12) and (16)
  have h10 := step10_alpha4 hMV (X := X) (u := u) (δ := δ) (a := a) (α4 := α4) (f := fm m)
    (by linarith) hδ0.le hδ1 hu (by linarith) huX ha0 ha1 hfc hf0 (by rw [hYeq]; exact hY) hα4
    (by rw [hYeq]; exact hY4)
  rw [hYeq, hmid] at h10
  have h10' : ∫ t in (0 : ℝ)..1, Dθ X u δ t * fm m t ≤
      (θ Y - θ (X * (1 + δ * a))) * (F - V) + 2.001 / α4 * u * X * V := by
    simpa [hV, v] using h10
  have h12 := step12_int hS hX12 hu.le (by linarith) hδ0.le hδ1 hfc hf0
  have hJ' := hJ m X u T hm (by linarith) hu hmu hT hTT
  -- the N(T) term
  set n := (1 + δ) * (2 * NT T) / √X with hn
  have hnb : n ≤ 1.0007 * α1 := by
    have hq : 2 * NT T / √X ≤ 1.00011 * α1 := by
      rw [div_le_iff₀ hsX]
      linarith [mul_le_mul_of_nonneg_left hsXY hα1.le]
    rw [hn, mul_div_assoc]
    rcases le_or_gt 0 (2 * NT T / √X) with hq0 | hq0
    · linarith [mul_le_mul_of_nonneg_right hδ1 hq0]
    · linarith [mul_nonpos_of_nonneg_of_nonpos hδ0.le hq0.le]
  -- the zero term
  have hsT : 0 ≤ sm m T := sm_nonneg m hT
  have hsT0 : 0 ≤ sm m T0 := sm_nonneg m (by linarith)
  have hμ0 := muStar_nonneg m
  have hTpos : 0 < T := by linarith
  have hT0pos : 0 < T0 := by linarith
  have hA3pos : 0 < A3 := h3
  have hinner : 0 ≤ Row1.innerRS m α1 α2 α4 a Y T T0 := by
    unfold Row1.innerRS
    rw [← hA3]
    positivity
  have hpow := Row1.uRS_pow m α1 α2 α4 a Y T T0 hinner
  rw [← hudef] at hpow
  have hpow' : u ^ (m + 1) = (1.0001 / T) ^ (m + 1) * ((1 / A3) * muStar m / (m : ℝ) ^ m * T *
      (sm m T / √Y + sm m T0 / 2 * (T / T0) ^ m)) := hpow
  have hK := K_eq (δ := δ) rfl hpow' hA3pos.ne' hTpos.ne' (by positivity)
  have hSle := S_le (m := m) hsT hsT0 hsX hsY hTpos hT0pos hsXY
  have hZb := zero_term_le (m := m) hu hδ0.le hδ1 hμ0 (by positivity) (by positivity)
    (by positivity) hSle hK hA3pos (by positivity)
  -- the 0.0325 √X term
  have hα2pos : 0 < α2 := by linarith
  have hqb : 0.0325 * √X ≤ 0.0326 / α2 * (u * X) := by
    have h1 : α2 ≤ 1.00011 * u * √X := by linarith [mul_le_mul_of_nonneg_left hsXY hu.le]
    have hXs : √X * √X = X := Real.mul_self_sqrt hXpos.le
    rw [div_mul_eq_mul_div, le_div_iff₀ hα2pos]
    have e : u * √X * √X = u * X := by rw [mul_assoc, hXs]
    linarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ 0.0325 * √X by positivity), mul_pos hu hXpos]
  -- α3
  have hA3eq : 2.0012 * A3 = 0.99 - 1.0007 * α1 - 2.001 / α4 * w m a - 0.0326 / α2 := by
    rw [hA3, alpha3inv]; ring
  have hα4pos : 0 < α4 := by linarith
  have hc4ge : 2.001 ≤ 2.001 / α4 := by rw [le_div_iff₀ hα4pos]; linarith
  have hq0 : 0 < 0.0326 / α2 := div_pos (by norm_num) hα2pos
  have hw1 : w m a < 1 := by
    by_contra hge
    push Not at hge
    have : 2.001 ≤ 2.001 / α4 * w m a :=
      hc4ge.trans (le_mul_of_one_le_right (by positivity) hge)
    have : 2.0012 * A3 < 0 := by rw [hA3eq]; linarith
    linarith
  -- 1/X^2
  have hr1 : 1 / X ^ 2 ≤ 0.00001 := by
    rw [div_le_iff₀ (by positivity), sq]
    have h := mul_le_mul hX12 hX12 (by norm_num) hXpos.le
    linarith
  have hJ2 : u * X * F * (1 - 1 / X ^ 2 - (1 + δ) * (2 * NT T) / √X -
      (1 + δ) ^ (m + 1) * muStar m * (2.0001 / (u * δ ^ m)) *
        (sm m T / (√X * T ^ m) + sm m T0 / (2 * T0 ^ m))) ≤
      ∫ t in (0 : ℝ)..1, Dψ X u δ t * fm m t := by
    have e : ∀ z : ℝ, u * X * F * z = u * X * z * F := fun z => by ring
    rw [e]; exact hJ'
  have h10'' : ∫ t in (0 : ℝ)..1, Dθ X u δ t * fm m t ≤
      (θ Y - θ (X * (1 + δ * a))) * (F - V) + 2.001 / α4 * (u * X) * V := by
    have e : 2.001 / α4 * u * X * V = 2.001 / α4 * (u * X) * V := by ring
    rw [← e]; exact h10'
  have hYuX : u * Y ≤ 1.00021 * (u * X) := by
    have := mul_le_mul_of_nonneg_left hYX hu.le; linarith
  exact final_alg rfl hFpos (by positivity) h10'' h12 hJ2 hnb hZb hqb hA3eq hwV hw1 hr1 hYuX

/-- **Theorem 4 for `f_m`** from the literal (15). PROVED CONDITIONAL ON `MVBrunTitchmarsh`,
`SchoenfeldPT 0.998697 1.001093`, `JLower15Lit` and `Lemma3Bound`. -/
theorem theorem4Fm_of_split_lit (hMV : MVBrunTitchmarsh) (hS : SchoenfeldPT 0.998697 1.001093)
    {NT : ℝ → ℝ} {Zs : ℕ → ℝ → ℝ → ℝ} {T0 : ℝ} (h15 : JLower15Lit NT Zs T0)
    (hL3 : Lemma3Bound Zs T0) : Theorem4Fm NT T0 :=
  theorem4Fm_of_lit hMV hS (jLowerLit_of h15 hL3)

/-- **Table 1 row one** from the literal (15). PROVED CONDITIONAL ON `MVBrunTitchmarsh`,
`SchoenfeldPT`, `JLower15Lit` and `Lemma3Bound` with `T0 = 3.3e9`, and `Lemma1Upper NT`. -/
theorem theorem2At1e20_of_split_lit (hMV : MVBrunTitchmarsh)
    (hS : SchoenfeldPT 0.998697 1.001093) {NT : ℝ → ℝ} {Zs : ℕ → ℝ → ℝ → ℝ}
    (h15 : JLower15Lit NT Zs 3300000000) (hL3 : Lemma3Bound Zs 3300000000)
    (hN : Row1.Lemma1Upper NT) : Theorem2At1e20 :=
  Row1.theorem2At1e20_of (theorem4Fm_of_split_lit hMV hS h15 hL3) hN MuStarLower.muStar48Bounds

end LeanLab.RamareSaouter2003.Thm4Literal
