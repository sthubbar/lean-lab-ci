import Mathlib
import LeanLab.RamareSaouter2003.Theorem4Parts
import LeanLab.RamareSaouter2003.MuStarLower

/-!
# Ramaré-Saouter 2003, Theorem 4 for f_m assembled from named cited inputs

P0099, unit U-6751, session 20261020T2217Z-cloud52. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN.

`Theorem4Fm NT T0` of `Theorem3Smooth.lean` is PROVED here CONDITIONAL ON three named inputs:

* `MVBrunTitchmarsh`, Montgomery and Vaughan 1973 Theorem 2, through Lemma 5 and (10);
* `SchoenfeldPT 0.998697 1.001093`, Schoenfeld's bounds (11), through (12);
* `JLower NT T0`, the lower bound (16) of p. 20 for `J`, the ψ integral, in the form it has
  before the hypothesis on `α1` is used: display (15) with Lemma 3 and `e^u + 1 ≤ 2.0001`
  applied. In the paper `JLower` rests on Lemma 4, the explicit formula against `f`,
  RH verified to `T0`, Lemma 3 and the integration by parts (14). It is stated for `f = f_m`
  and any `δ ∈ ]0, 10^-4]`, `u ∈ ]0, 5 · 10^-5]`, the range that `m u ≤ 10^-4` with `m ≥ 2`
  gives, `X ≥ 10^12` and `10^3 ≤ T ≤ T0`.

The rest of the proof on pp. 18 to 20 is done here: the change of variables `δ = m u`,
`e^u X (1 + δ(1 - a)) = Y`, the algebra from (16) to (17) through the definition of `u`, and
(18), with constants checked: `2.0001 · 1.00011 ≤ 2.0012`, `0.0325 · 1.00011 ≤ 0.0326`,
`1.0001 · 1.00011 ≤ 1.0007`, and `1.00021/101 < 0.01 - 1/X^2`.

Corollaries: `theorem2At1e20_of_inputs`, Table 1 row one, and `theorem2_row59_of_inputs`,
Table 1 row 59, with `Lemma1Upper` for `N(T)`, which `Lemma1Rosser.lemma1Upper_of_rosser`
derives from `RosserNUpper`; row 59 also takes `MuStar55Bounds`, PROVED as
`MuStar55Cert.muStar55Bounds` in a module not imported here because it needs 13 GB to build.
-/

namespace LeanLab.RamareSaouter2003.Thm4Assembly

open Real Chebyshev LeanLab.RamareSaouter2003.Smooth LeanLab.RamareSaouter2003.Thm4Parts

/-- The ψ integrand of `J`, `ψ(X e^u (1 + δ t)) - ψ(X (1 + δ t))`. -/
noncomputable def Dψ (X u δ t : ℝ) : ℝ :=
  ψ (X * Real.exp u * (1 + δ * t)) - ψ (X * (1 + δ * t))

/-- **Display (16) of Ramaré-Saouter 2003, p. 20**, before the hypothesis on `α1` is used,
for `f = f_m`: with `J = ∫_0^1 Dψ f / ||f||_1`,
`J/(uX) ≥ 1 - 1/X^2 - (1 + δ) 2N(T)/√X - (1 + δ)^(m+1) μ*_m (2.0001/(u δ^m))
(s_m(T)/(√X T^m) + s_m(T0)/(2 T0^m))`, written multiplied out by `u X ||f_m||_1`.
`NT` is the zero counting function `N(T)` of (3). CITED, not proved here: in the paper it
follows from Lemma 4, RH verified to `T0`, Lemma 3 and (14). -/
def JLower (NT : ℝ → ℝ) (T0 : ℝ) : Prop :=
  ∀ (m : ℕ) (X u δ T : ℝ), 2 ≤ m → 10 ^ 12 ≤ X → 0 < u → u ≤ 0.00005 → 0 < δ → δ ≤ 0.0001 →
    1000 ≤ T → T ≤ T0 →
    u * X * (1 - 1 / X ^ 2 - (1 + δ) * (2 * NT T) / √X -
        (1 + δ) ^ (m + 1) * muStar m * (2.0001 / (u * δ ^ m)) *
          (sm m T / (√X * T ^ m) + sm m T0 / (2 * T0 ^ m))) * (∫ t in (0 : ℝ)..1, fm m t) ≤
      ∫ t in (0 : ℝ)..1, Dψ X u δ t * fm m t

theorem psi_affine_mono {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) :
    Monotone (fun t : ℝ => ψ (c * (1 + δ * t))) := by
  intro s t hst
  apply Chebyshev.psi_mono
  have : δ * s ≤ δ * t := mul_le_mul_of_nonneg_left hst hδ
  nlinarith

theorem Dψ_mul_intervalIntegrable {X u δ : ℝ} {f : ℝ → ℝ} (hX : 0 ≤ X) (hδ : 0 ≤ δ)
    {a b : ℝ} (hf : ContinuousOn f (Set.uIcc a b)) :
    IntervalIntegrable (fun t => Dψ X u δ t * f t) MeasureTheory.volume a b := by
  have h1 := (psi_affine_mono (c := X * Real.exp u) (by positivity) hδ).intervalIntegrable
    (μ := MeasureTheory.volume) (a := a) (b := b)
  have h2 := (psi_affine_mono (c := X) hX hδ).intervalIntegrable
    (μ := MeasureTheory.volume) (a := a) (b := b)
  exact (h1.sub h2).mul_continuousOn hf

/-- **(12), p. 19**, integrated: `∫ Dψ f - 0.0325 √X ∫ f ≤ ∫ Dθ f`, i.e. `I ≥ J - 0.0325 √X`.
PROVED CONDITIONAL ON `SchoenfeldPT 0.998697 1.001093`. -/
theorem step12_int (hS : SchoenfeldPT 0.998697 1.001093) {X u δ : ℝ} {f : ℝ → ℝ}
    (hX : 199 * 10 ^ 10 ≤ X) (hu0 : 0 ≤ u) (hu : u ≤ 0.0001) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 0.0001)
    (hf : ContinuousOn f (Set.Icc 0 1)) (hf0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t) :
    (∫ t in (0 : ℝ)..1, Dψ X u δ t * f t) - 0.0325 * √X * ∫ t in (0 : ℝ)..1, f t ≤
      ∫ t in (0 : ℝ)..1, Dθ X u δ t * f t := by
  have hXpos : 0 < X := by linarith
  have hf' : ContinuousOn f (Set.uIcc 0 1) := by rwa [Set.uIcc_of_le zero_le_one]
  have iθ := Dθ_mul_intervalIntegrable (u := u) hXpos.le hδ0 hf'
  have iψ := Dψ_mul_intervalIntegrable (u := u) hXpos.le hδ0 hf'
  have jf : IntervalIntegrable f MeasureTheory.volume 0 1 := hf'.intervalIntegrable
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub iψ (jf.const_mul _)]
  refine intervalIntegral.integral_mono_on zero_le_one (iψ.sub (jf.const_mul _)) iθ ?_
  intro t ht
  have h := step12_printed hS hX hu0 hu hδ0 hδ ht.1 ht.2
  have e1 : Real.exp u * (1 + δ * t) * X = X * Real.exp u * (1 + δ * t) := by ring
  have e2 : (1 + δ * t) * X = X * (1 + δ * t) := by ring
  rw [e1, e2] at h
  have hft := hf0 t ht
  simp only [Dθ, Dψ]
  nlinarith [mul_le_mul_of_nonneg_right h hft]

theorem fm_nonneg (m : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ fm m t := by
  unfold fm
  apply pow_nonneg
  nlinarith [ht.1, ht.2]

theorem sm_nonneg (m : ℕ) {T : ℝ} (hT : 1000 ≤ T) : 0 ≤ sm m T := by
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  have hL : 0 ≤ Real.log (T / (2 * π)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith
  unfold sm
  have h1 : 0 ≤ (1 / (m * π)) * (Real.log (T / (2 * π)) + 1 / m) := by positivity
  have h2 : 0 ≤ 1.34 / T * (2 * Real.log (T / (2 * π)) + 1) :=
    mul_nonneg (div_nonneg (by norm_num) (by linarith)) (by linarith)
  have h3 : (0 : ℝ) ≤ 1 + 1 / 10 ^ 5 := by norm_num
  exact mul_nonneg (add_nonneg h1 h2) h3

theorem muStar_nonneg (m : ℕ) : 0 ≤ muStar m := by
  unfold muStar
  apply div_nonneg
  · exact intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)
  · exact intervalIntegral.integral_nonneg zero_le_one (fun t ht => fm_nonneg m ht)

theorem K_eq {m : ℕ} {u δ A3 μ T S2 : ℝ} (hδ : δ = m * u)
    (hpow : u ^ (m + 1) = (1.0001 / T) ^ (m + 1) * ((1 / A3) * μ / (m : ℝ) ^ m * T * S2))
    (hA3 : A3 ≠ 0) (hT : T ≠ 0) (hm : (m : ℝ) ≠ 0) :
    u * δ ^ m * A3 = 1.0001 ^ (m + 1) * μ * S2 / T ^ m := by
  have e : u * δ ^ m = (m : ℝ) ^ m * u ^ (m + 1) := by rw [hδ, mul_pow, pow_succ]; ring
  rw [e, hpow, div_pow, pow_succ T m]
  have hmm : (m : ℝ) ^ m ≠ 0 := pow_ne_zero _ hm
  have hTm : T ^ m ≠ 0 := pow_ne_zero _ hT
  field_simp

theorem S_le {m : ℕ} {sT sT0 X Y T T0 : ℝ} (hsT : 0 ≤ sT) (hsT0 : 0 ≤ sT0) (hsX : 0 < √X)
    (hsY : 0 < √Y) (hT : 0 < T) (hT0 : 0 < T0) (hXY : √Y ≤ 1.00011 * √X) :
    sT / (√X * T ^ m) + sT0 / (2 * T0 ^ m) ≤
      1.00011 * (sT / √Y + sT0 / 2 * (T / T0) ^ m) / T ^ m := by
  have hTm : 0 < T ^ m := pow_pos hT m
  have hT0m : 0 < T0 ^ m := pow_pos hT0 m
  have e : sT / (√X * T ^ m) + sT0 / (2 * T0 ^ m) =
      (sT / √X + sT0 / 2 * (T / T0) ^ m) / T ^ m := by
    rw [div_pow]; field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ hTm.le
  have h1 : sT / √X ≤ 1.00011 * (sT / √Y) := by
    rw [div_le_iff₀ hsX, ← mul_div_assoc, div_mul_eq_mul_div, le_div_iff₀ hsY]
    nlinarith [mul_le_mul_of_nonneg_left hXY hsT]
  have h2 : 0 ≤ sT0 / 2 * (T / T0) ^ m := by positivity
  linarith

theorem zero_term_le {m : ℕ} {u δ μ A3 S S2 Tm : ℝ} (hu : 0 < u) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 0.0001) (hμ : 0 ≤ μ) (hS2 : 0 ≤ S2) (hTm : 0 < Tm) (hS0 : 0 ≤ S)
    (hSle : S ≤ 1.00011 * S2 / Tm) (hK : u * δ ^ m * A3 = 1.0001 ^ (m + 1) * μ * S2 / Tm)
    (hA3 : 0 < A3) (hKpos : 0 < u * δ ^ m) :
    (1 + δ) ^ (m + 1) * μ * (2.0001 / (u * δ ^ m)) * S ≤ 2.0012 * A3 := by
  have hd : (1 + δ) ^ (m + 1) ≤ 1.0001 ^ (m + 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hp0 : 0 ≤ (1 + δ) ^ (m + 1) := by positivity
  generalize hD : u * δ ^ m = D at *
  generalize hp : (1 + δ) ^ (m + 1) = p at *
  generalize hc : (1.0001 : ℝ) ^ (m + 1) = c at *
  have hR : 0 ≤ c * μ * S2 / Tm := by
    have : 0 ≤ c := by rw [← hc]; positivity
    positivity
  have e : p * μ * (2.0001 / D) * S = p * μ * 2.0001 * S / D := by ring
  rw [e, div_le_iff₀ hKpos]
  have hrhs : 2.0012 * A3 * D = 2.0012 * (c * μ * S2 / Tm) := by rw [← hK]; ring
  rw [hrhs]
  have s1 : p * μ * 2.0001 * S ≤ c * μ * 2.0001 * (1.00011 * S2 / Tm) := by
    have := mul_le_mul hd hSle hS0 (by rw [← hc]; positivity)
    nlinarith [mul_le_mul_of_nonneg_left this hμ]
  have s2 : c * μ * 2.0001 * (1.00011 * S2 / Tm) = 2.000320011 * (c * μ * S2 / Tm) := by ring
  nlinarith

theorem final_alg {C D Jψ F V w P n Z r q c4 A3 α1 uX uY sX : ℝ}
    (hP : P = uX * F) (hF : 0 < F) (huX : 0 < uX)
    (h10 : D ≤ C * (F - V) + c4 * uX * V) (h12 : Jψ - 0.0325 * sX * F ≤ D)
    (hJ : P * (1 - r - n - Z) ≤ Jψ) (hn : n ≤ 1.0007 * α1) (hZ : Z ≤ 2.0012 * A3)
    (hq : 0.0325 * sX ≤ q * uX) (hA3 : 2.0012 * A3 = 0.99 - 1.0007 * α1 - c4 * w - q)
    (hV : w * F = V) (hw : w < 1) (hr : r ≤ 0.00001) (hY : uY ≤ 1.00021 * uX) :
    uY / (101 * (1 - w)) ≤ C := by
  subst hV hP
  have hPpos : 0 < uX * F := mul_pos huX hF
  have a1 := mul_le_mul_of_nonneg_left hn hPpos.le
  have a2 := mul_le_mul_of_nonneg_left hZ hPpos.le
  have a3 := mul_le_mul_of_nonneg_right hq hF.le
  have a4 : 2.0012 * A3 * (uX * F) = (0.99 - 1.0007 * α1 - c4 * w - q) * (uX * F) := by rw [hA3]
  have key : uX * F * (0.01 - r) ≤ C * (1 - w) * F := by
    nlinarith [a1, a2, a3, a4, h10, h12, hJ]
  have h1w : 0 < 1 - w := by linarith
  rw [div_le_iff₀ (by positivity)]
  have hgoal : uY * F ≤ C * (101 * (1 - w)) * F := by
    nlinarith [mul_le_mul_of_nonneg_right hY hF.le]
  exact le_of_mul_le_mul_right hgoal hF

set_option maxHeartbeats 2000000 in
/-- **Theorem 4 of Ramaré-Saouter 2003 for `f = f_m`.** PROVED CONDITIONAL ON
`MVBrunTitchmarsh`, `SchoenfeldPT 0.998697 1.001093` and `JLower NT T0`. -/
theorem theorem4Fm_of (hMV : MVBrunTitchmarsh) (hS : SchoenfeldPT 0.998697 1.001093)
    {NT : ℝ → ℝ} {T0 : ℝ} (hJ : JLower NT T0) : Theorem4Fm NT T0 := by
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
  have hJ' := hJ m X u δ T hm (by linarith) hu (by linarith) hδ0 hδ1 hT hTT
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


/-- **Table 1 row one**, every `x ≥ 10^20` has a prime in `]x(1 - 1/81 353 847), x]`.
PROVED CONDITIONAL ON `MVBrunTitchmarsh`, `SchoenfeldPT 0.998697 1.001093`,
`JLower NT 3.3e9` and `Lemma1Upper NT`, the last one PROVED from `RosserNUpper NT` by
`Lemma1Rosser.lemma1Upper_of_rosser`. -/
theorem theorem2At1e20_of_inputs (hMV : MVBrunTitchmarsh) (hS : SchoenfeldPT 0.998697 1.001093)
    {NT : ℝ → ℝ} (hJ : JLower NT 3300000000) (hN : Row1.Lemma1Upper NT) :
    Theorem2At1e20 :=
  Row1.theorem2At1e20_of (theorem4Fm_of hMV hS hJ) hN MuStarLower.muStar48Bounds

/-- **Table 1 row 59**, CONDITIONAL ON the same inputs and `MuStar55Bounds`, which is PROVED as
`MuStar55Cert.muStar55Bounds`. -/
theorem theorem2_row59_of_inputs (hMV : MVBrunTitchmarsh) (hS : SchoenfeldPT 0.998697 1.001093)
    {NT : ℝ → ℝ} (hJ : JLower NT 3300000000) (hN : Row1.Lemma1Upper NT)
    (hμ : Row59.MuStar55Bounds) : ∀ x : ℝ, Real.exp 59 ≤ x →
      ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 209257759) < p ∧ (p : ℝ) ≤ x :=
  Row59.theorem2_row59_of (theorem4Fm_of hMV hS hJ) hN hμ

end LeanLab.RamareSaouter2003.Thm4Assembly

#print axioms LeanLab.RamareSaouter2003.Thm4Assembly.step12_int
#print axioms LeanLab.RamareSaouter2003.Thm4Assembly.theorem4Fm_of
#print axioms LeanLab.RamareSaouter2003.Thm4Assembly.theorem2At1e20_of_inputs
#print axioms LeanLab.RamareSaouter2003.Thm4Assembly.theorem2_row59_of_inputs
