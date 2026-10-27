import Mathlib
import LeanLab.PNTPort.ExplicitPsi1.ThetaRelRH
import LeanLab.ChirreHagen2025.Bilinear64
import LeanLab.ChirreHagen2025.Bilinear128
import LeanLab.ChirreHagen2025.SmoothJ
import LeanLab.ChirreHagen2025.SmoothSharp
import LeanLab.ChirreHagen2025.Lemma24
import LeanLab.ChirreHagen2025.Lemma26Proof
import LeanLab.ChirreHagen2025.Lemma26HSW
import LeanLab.ChirreHagen2025.Lemma26BPT
import LeanLab.ChirreHagen2025.Local36
import LeanLab.KanieckiGap.AssemblyEven
import LeanLab.SchnirelmannBounds.Statements

/-!
# Downstream of `ThetaRel` from RH plus the Hasanalizade-Shen-Wong zero counts

I-5260, unit U-6706, CLOUD 20261020T1816Z-cloud48, track T2. AI wrote this file; the five
long proofs are copies of the originals with one argument swapped, made by a script.

Each theorem `X_hsw` here is the lab theorem `X` with its hypothesis
`hS : RiemannHypothesis → SchoenfeldTheta`, Schoenfeld 1976 Corollary 1 CITED, removed and the
three inputs `hNz : HSWN70 gZ`, `hHz : HSWHead14 gZ`, `h14z : Ordinates14 gZ` for the true
ordinates `gZ` added. The conclusion is exactly the original one. Inside, the original proofs
used `hS` only as `thetaRel_of_schoenfeld (hS hRH)`; that term is replaced by
`ThetaRelRH.thetaRel_of_RH_hsw hRH hNz hHz h14z` of ThetaRelRH.lean.

So every theorem here is CONDITIONAL ON RH, which stays the antecedent of the conclusion as in
the originals, on the three zero-count inputs above, and on each theorem's own other inputs,
listed in its docstring: Chirre-Hagen's `J_ψ` bound or the zero inputs it rests on, the
`4 · 10^18` even Goldbach check, and for Kaniecki Liu-Wang 2002 and the 1476 gap table.
Schoenfeld's Corollary 1 is no longer an input anywhere here.

Not relabelled: `SchnirelmannBounds/Discharged.lean` imports `LeanLab.Kaniecki1995.Statements`,
which is absent from this checkout, so its bundled `KanieckiInputs`, `kaniecki1995_theorem`
and the `Kaniecki1995.TheoremOdd/Even` forms are not reachable; the `_hsw` forms of
`kaniecki_odd`, `kaniecki_even` and `kaniecki_even_RH` below state the same conclusions,
`kaniecki_odd_stmt` and `kaniecki_even_stmt` of SchnirelmannBounds/Statements.lean, with the
bundle's fields as separate hypotheses.

Binary Goldbach is OPEN.
-/

namespace LeanLab.PNTPort.ExplicitPsi1.ThetaRelDownstream

open Real Chebyshev Finset
open LeanLab.ChirreHagen2025
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ)
open LeanLab.Dudek2014.SigmaH (HSWN70)

/-! ### The five short-interval proofs, `ThetaRel` swapped -/

/-- `goldbach_10` of Bilinear64.lean with `hS` replaced by the HSW inputs; same conclusion. CONDITIONAL ON RH, `HSWN70`, `HSWHead14`, `Ordinates14` for `gZ`, the `J_ψ` bound `h2` with 2.2258 and the `4 · 10^18` even check. -/
theorem goldbach_10_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 10 * Real.log x ^ 2 := by
  intro hRH x hx
  have hlog : 0.69 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hx
    linarith
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, hn, h1, h2'⟩ := small_of hE x hx hs
    exact ⟨n, hn, h1, by nlinarith⟩
  · have hx' : 1.1 * 10 ^ 18 ≤ x := by linarith
    have hxpos : 0 < x := by linarith
    have hL : 41 ≤ Real.log x := log_ge_41 hx'
    set δ := 9.99 * Real.log x ^ 2 / x with hδ
    have hδpos : 0 < δ := by positivity
    have hδ13 : δ ≤ 1 / 10 ^ 13 := by
      have := threshold2 hx'
      have : δ ≤ 61.5 * Real.log x ^ 2 / x := by
        rw [hδ]; apply div_le_div_of_nonneg_right _ hxpos.le; nlinarith
      linarith
    have hsx : δ * √x < 1 := by
      have hc := log_cube_div_sqrt (by linarith : (10 : ℝ) ^ 18 ≤ x)
      have hsx0 : 0 < √x := Real.sqrt_pos.mpr hxpos
      have hss : √x * √x = x := Real.mul_self_sqrt hxpos.le
      have e0 : δ * √x * √x = 9.99 * Real.log x ^ 2 := by
        rw [mul_assoc, hss, hδ]; field_simp
      have e : δ * √x = 9.99 * (Real.log x ^ 2 / √x) := by
        rw [show 9.99 * (Real.log x ^ 2 / √x) = 9.99 * Real.log x ^ 2 / √x by ring,
          eq_div_iff hsx0.ne']
        exact e0
      have h23 : Real.log x ^ 2 ≤ Real.log x ^ 3 := by nlinarith
      have : Real.log x ^ 2 / √x ≤ 7.5 / 10 ^ 5 :=
        le_trans (div_le_div_of_nonneg_right h23 hsx0.le) hc
      rw [e]; linarith
    obtain ⟨n, hn, h1, h2'⟩ := large_c_of64 (c := 2.23) (H := 9.99) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
        (LeanLab.PNTPort.ExplicitPsi1.ThetaRelRH.thetaRel_of_RH_hsw hRH hNz hHz h14z) x hx'
      (fun X hX1 hX2 => by
        rw [← hδ]
        have hX : 5 * 10 ^ 17 ≤ X := by linarith
        have hsX : δ * √X < 1 :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hX2) hδpos.le) hsx
        exact Jtheta_le_223 (h2 hRH X δ (by linarith) hδpos hδ13) hX hδpos hδ13 hsX)
    exact ⟨n, hn, h1, by nlinarith⟩

/-- `goldbach_995` of Bilinear128.lean with `hS` replaced by the HSW inputs; same conclusion. CONDITIONAL ON RH, `HSWN70`, `HSWHead14`, `Ordinates14` for `gZ`, the `J_ψ` bound `h2` with 2.2258 and the `4 · 10^18` even check. -/
theorem goldbach_995_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 9.95 * Real.log x ^ 2 := by
  intro hRH x hx
  have hlog : 0.69 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hx
    linarith
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, hn, h1, h2'⟩ := small_of hE x hx hs
    exact ⟨n, hn, h1, by nlinarith⟩
  · have hx' : 1.1 * 10 ^ 18 ≤ x := by linarith
    have hxpos : 0 < x := by linarith
    have hL : 41 ≤ Real.log x := log_ge_41 hx'
    set δ := 9.94 * Real.log x ^ 2 / x with hδ
    have hδpos : 0 < δ := by positivity
    have hδ13 : δ ≤ 1 / 10 ^ 13 := by
      have := threshold2 hx'
      have : δ ≤ 61.5 * Real.log x ^ 2 / x := by
        rw [hδ]; apply div_le_div_of_nonneg_right _ hxpos.le; nlinarith
      linarith
    have hsx : δ * √x < 1 := by
      have hc := log_cube_div_sqrt (by linarith : (10 : ℝ) ^ 18 ≤ x)
      have hsx0 : 0 < √x := Real.sqrt_pos.mpr hxpos
      have hss : √x * √x = x := Real.mul_self_sqrt hxpos.le
      have e0 : δ * √x * √x = 9.94 * Real.log x ^ 2 := by
        rw [mul_assoc, hss, hδ]; field_simp
      have e : δ * √x = 9.94 * (Real.log x ^ 2 / √x) := by
        rw [show 9.94 * (Real.log x ^ 2 / √x) = 9.94 * Real.log x ^ 2 / √x by ring,
          eq_div_iff hsx0.ne']
        exact e0
      have h23 : Real.log x ^ 2 ≤ Real.log x ^ 3 := by nlinarith
      have : Real.log x ^ 2 / √x ≤ 7.5 / 10 ^ 5 :=
        le_trans (div_le_div_of_nonneg_right h23 hsx0.le) hc
      rw [e]; linarith
    obtain ⟨n, hn, h1, h2'⟩ := large_c_of128 (c := 2.23) (H := 9.94) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
        (LeanLab.PNTPort.ExplicitPsi1.ThetaRelRH.thetaRel_of_RH_hsw hRH hNz hHz h14z) x hx'
      (fun X hX1 hX2 => by
        rw [← hδ]
        have hX : 5 * 10 ^ 17 ≤ X := by linarith
        have hsX : δ * √X < 1 :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hX2) hδpos.le) hsx
        exact Jtheta_le_223 (h2 hRH X δ (by linarith) hδpos hδ13) hX hδpos hδ13 hsX)
    exact ⟨n, hn, h1, by nlinarith⟩

/-- `goldbach_10_5` of ThetaPsi.lean with `hS` replaced by the HSW inputs; same conclusion. CONDITIONAL ON RH, `HSWN70`, `HSWHead14`, `Ordinates14` for `gZ`, the `J_ψ` bound `h2` with 2.2258 and the `4 · 10^18` even check. -/
theorem goldbach_10_5_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 10.5 * Real.log x ^ 2 := by
  intro hRH x hx
  have hlog : 0.69 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hx
    linarith
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, hn, h1, h2'⟩ := small_of hE x hx hs
    exact ⟨n, hn, h1, by nlinarith⟩
  · have hx' : 1.1 * 10 ^ 18 ≤ x := by linarith
    have hxpos : 0 < x := by linarith
    have hL : 41 ≤ Real.log x := log_ge_41 hx'
    set δ := 10.4 * Real.log x ^ 2 / x with hδ
    have hδpos : 0 < δ := by positivity
    have hδ13 : δ ≤ 1 / 10 ^ 13 := by
      have := threshold2 hx'
      have : δ ≤ 61.5 * Real.log x ^ 2 / x := by
        rw [hδ]; apply div_le_div_of_nonneg_right _ hxpos.le; nlinarith
      linarith
    have hsx : δ * √x < 1 := by
      have hc := log_cube_div_sqrt (by linarith : (10 : ℝ) ^ 18 ≤ x)
      have hsx0 : 0 < √x := Real.sqrt_pos.mpr hxpos
      have hss : √x * √x = x := Real.mul_self_sqrt hxpos.le
      have e0 : δ * √x * √x = 10.4 * Real.log x ^ 2 := by
        rw [mul_assoc, hss, hδ]; field_simp
      have e : δ * √x = 10.4 * (Real.log x ^ 2 / √x) := by
        rw [show 10.4 * (Real.log x ^ 2 / √x) = 10.4 * Real.log x ^ 2 / √x by ring,
          eq_div_iff hsx0.ne']
        exact e0
      have h23 : Real.log x ^ 2 ≤ Real.log x ^ 3 := by nlinarith
      have : Real.log x ^ 2 / √x ≤ 7.5 / 10 ^ 5 :=
        le_trans (div_le_div_of_nonneg_right h23 hsx0.le) hc
      rw [e]; linarith
    obtain ⟨n, hn, h1, h2'⟩ := large_c_of (c := 2.23) (H := 10.4) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
        (LeanLab.PNTPort.ExplicitPsi1.ThetaRelRH.thetaRel_of_RH_hsw hRH hNz hHz h14z) x hx'
      (fun X hX1 hX2 => by
        rw [← hδ]
        have hX : 5 * 10 ^ 17 ≤ X := by linarith
        have hsX : δ * √X < 1 :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hX2) hδpos.le) hsx
        exact Jtheta_le_223 (h2 hRH X δ (by linarith) hδpos hδ13) hX hδpos hδ13 hsX)
    exact ⟨n, hn, h1, by nlinarith⟩

/-- `goldbach_578_of_smooth` of SmoothJ.lean with `hS` replaced by the HSW inputs; same conclusion. CONDITIONAL ON RH, `HSWN70`, `HSWHead14`, `Ordinates14` for `gZ`, the `J_ψ` bound `h2` with 1.2913 and the `4 · 10^18` even check. -/
theorem goldbach_578_of_smooth_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.2913 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 5.78 * Real.log x ^ 2 := by
  intro hRH x hx
  have hlog : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, hn, h1, h2'⟩ := small_of hE x (by linarith) hs
    exact ⟨n, hn, h1, by nlinarith⟩
  · have hx' : 1.1 * 10 ^ 18 ≤ x := by linarith
    have hxpos : 0 < x := by linarith
    have hL : 41 ≤ Real.log x := log_ge_41 hx'
    set δ := 5.77 * Real.log x ^ 2 / x with hδ
    have hδpos : 0 < δ := by positivity
    have hδ13 : δ ≤ 1 / 10 ^ 13 := by
      have := threshold2 hx'
      have : δ ≤ 61.5 * Real.log x ^ 2 / x := by
        rw [hδ]; apply div_le_div_of_nonneg_right _ hxpos.le; nlinarith
      linarith
    have hsx : δ * √x < 1 := by
      have hc := log_cube_div_sqrt (by linarith : (10 : ℝ) ^ 18 ≤ x)
      have hsx0 : 0 < √x := Real.sqrt_pos.mpr hxpos
      have hss : √x * √x = x := Real.mul_self_sqrt hxpos.le
      have e0 : δ * √x * √x = 5.77 * Real.log x ^ 2 := by
        rw [mul_assoc, hss, hδ]; field_simp
      have e : δ * √x = 5.77 * (Real.log x ^ 2 / √x) := by
        rw [show 5.77 * (Real.log x ^ 2 / √x) = 5.77 * Real.log x ^ 2 / √x by ring,
          eq_div_iff hsx0.ne']
        exact e0
      have h23 : Real.log x ^ 2 ≤ Real.log x ^ 3 := by nlinarith
      have : Real.log x ^ 2 / √x ≤ 7.5 / 10 ^ 5 :=
        le_trans (div_le_div_of_nonneg_right h23 hsx0.le) hc
      rw [e]; linarith
    obtain ⟨n, hn, h1, h2'⟩ := large_c_of128 (c := 1.001 * 1.2913 + 0.0019) (H := 5.77) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
        (LeanLab.PNTPort.ExplicitPsi1.ThetaRelRH.thetaRel_of_RH_hsw hRH hNz hHz h14z) x hx'
      (fun X hX1 hX2 => by
        rw [← hδ]
        have hX : 5 * 10 ^ 17 ≤ X := by linarith
        have hsX : δ * √X < 1 :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hX2) hδpos.le) hsx
        exact Jtheta_le_of_c (by norm_num) (h2 hRH X δ (by linarith) hδpos hδ13) hX hδpos hδ13 hsX)
    exact ⟨n, hn, h1, by nlinarith⟩

/-- `goldbach_448_of_sharp` of SharpGoldbach.lean with `hS` replaced by the HSW inputs; same conclusion. CONDITIONAL ON RH, `HSWN70`, `HSWHead14`, `Ordinates14` for `gZ`, the `J_ψ` bound `h2` with 1.0001 and the `4 · 10^18` even check. -/
theorem goldbach_448_of_sharp_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.0001 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.48 * Real.log x ^ 2 := by
  intro hRH x hx
  have hlog : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, hn, h1, h2'⟩ := small_of hE x (by linarith) hs
    exact ⟨n, hn, h1, by nlinarith⟩
  · have hx' : 1.1 * 10 ^ 18 ≤ x := by linarith
    have hxpos : 0 < x := by linarith
    have hL : 41 ≤ Real.log x := log_ge_41 hx'
    set δ := 4.47 * Real.log x ^ 2 / x with hδ
    have hδpos : 0 < δ := by positivity
    have hδ13 : δ ≤ 1 / 10 ^ 13 := by
      have := threshold2 hx'
      have : δ ≤ 61.5 * Real.log x ^ 2 / x := by
        rw [hδ]; apply div_le_div_of_nonneg_right _ hxpos.le; nlinarith
      linarith
    have hsx : δ * √x < 1 := by
      have hc := log_cube_div_sqrt (by linarith : (10 : ℝ) ^ 18 ≤ x)
      have hsx0 : 0 < √x := Real.sqrt_pos.mpr hxpos
      have hss : √x * √x = x := Real.mul_self_sqrt hxpos.le
      have e0 : δ * √x * √x = 4.47 * Real.log x ^ 2 := by
        rw [mul_assoc, hss, hδ]; field_simp
      have e : δ * √x = 4.47 * (Real.log x ^ 2 / √x) := by
        rw [show 4.47 * (Real.log x ^ 2 / √x) = 4.47 * Real.log x ^ 2 / √x by ring,
          eq_div_iff hsx0.ne']
        exact e0
      have h23 : Real.log x ^ 2 ≤ Real.log x ^ 3 := by nlinarith
      have : Real.log x ^ 2 / √x ≤ 7.5 / 10 ^ 5 :=
        le_trans (div_le_div_of_nonneg_right h23 hsx0.le) hc
      rw [e]; linarith
    obtain ⟨n, hn, h1, h2'⟩ := large_c_of128 (c := 1.001 * 1.0001 + 0.0019) (H := 4.47) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
        (LeanLab.PNTPort.ExplicitPsi1.ThetaRelRH.thetaRel_of_RH_hsw hRH hNz hHz h14z) x hx'
      (fun X hX1 hX2 => by
        rw [← hδ]
        have hX : 5 * 10 ^ 17 ≤ X := by linarith
        have hsX : δ * √X < 1 :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hX2) hδpos.le) hsx
        exact Jtheta_le_of_c (by norm_num) (h2 hRH X δ (by linarith) hδpos hδ13) hX hδpos hδ13 hsX)
    exact ⟨n, hn, h1, by nlinarith⟩

/-! ### Compositions, as in the original files -/

/-- `goldbach_448_of_zeros` of SharpGoldbach.lean with `hS` replaced by the HSW inputs; same
conclusion. CONDITIONAL ON RH, `HSWN70`, `HSWHead14`, `Ordinates14` for `gZ`, `ExplicitA`,
`HadamardK`, `Ordinates14` and `ZeroSumSharp` for `γ`, and the `4 · 10^18` even check. -/
theorem goldbach_448_of_zeros_hsw {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA γ Z δ)
    (hH : RiemannHypothesis → SmoothT2.HadamardK γ) (h14 : SmoothT2.Ordinates14 γ)
    (hZ : RiemannHypothesis → SmoothT2.ZeroSumSharp γ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.48 * Real.log x ^ 2 :=
  goldbach_448_of_sharp_hsw (fun hRH => SmoothT2.theorem2_sharp (hE hRH) (hH hRH) h14 (hZ hRH))
    hEv hNz hHz h14z

/-- `goldbach_578_of_zeros` of SmoothGoldbach.lean with `hS` replaced by the HSW inputs; same
conclusion. CONDITIONAL ON RH, `HSWN70`, `HSWHead14`, `Ordinates14` for `gZ`, `ExplicitA`,
`HadamardK`, `Ordinates14` and `Lemma26` for `γ`, and the `4 · 10^18` even check. -/
theorem goldbach_578_of_zeros_hsw {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA γ Z δ)
    (hH : RiemannHypothesis → SmoothT2.HadamardK γ) (h14 : SmoothT2.Ordinates14 γ)
    (hL : SmoothT2.Lemma26 γ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 5.78 * Real.log x ^ 2 :=
  goldbach_578_of_smooth_hsw (fun hRH => SmoothT2.theorem2_smooth_of (hE hRH) (hH hRH) h14 hL)
    hEv hNz hHz h14z

/-- `theorem1_of_zeros` of Theorem1Zeros.lean, Chirre-Hagen's Theorem 1 with 123, with `hS`
replaced by the HSW inputs; same conclusion, same proof. CONDITIONAL ON RH, `HSWN70`,
`HSWHead14`, `Ordinates14` for `gZ`, `ExplicitA`, `HadamardK`, `Ordinates14`, `Lemma26` for
`γ`, and the `4 · 10^18` even check. -/
theorem theorem1_of_zeros_hsw {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA γ Z δ)
    (hH : RiemannHypothesis → SmoothT2.HadamardK γ) (h14 : SmoothT2.Ordinates14 γ)
    (hL : SmoothT2.Lemma26 γ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 123 * Real.log x ^ 2 := by
  intro hRH x hx
  have hlog : 0.69 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hx
    linarith
  rcases lt_or_ge x 3 with h3 | h3
  · obtain ⟨n, hn, h1, h2⟩ := small_of hEv x hx (by linarith)
    exact ⟨n, hn, h1, by nlinarith⟩
  · obtain ⟨n, hn, h1, h2⟩ :=
      goldbach_578_of_zeros_hsw hE hH h14 hL hEv hNz hHz h14z hRH x h3
    exact ⟨n, hn, h1, by nlinarith⟩

/-- `goldbach_578_of_trudgian` of Lemma26Goldbach.lean with `hS` replaced by the HSW inputs;
same conclusion. CONDITIONAL ON RH, `HSWN70`, `HSWHead14`, `Ordinates14` for `gZ`, `ExplicitA`,
`HadamardK`, `Ordinates14`, `TrudgianN` for `γ`, and the `4 · 10^18` even check. -/
theorem goldbach_578_of_trudgian_hsw {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA γ Z δ)
    (hH : RiemannHypothesis → SmoothT2.HadamardK γ) (h14 : SmoothT2.Ordinates14 γ)
    (hN : Lemma26P.TrudgianN γ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 5.78 * Real.log x ^ 2 :=
  goldbach_578_of_zeros_hsw hE hH h14 (Lemma26P.lemma26_of_trudgian hN) hEv hNz hHz h14z

/-- `goldbach_578_of_hsw` of Lemma26HSWGoldbach.lean with `hS` replaced by the HSW inputs;
same conclusion. CONDITIONAL ON RH, `HSWN70`, `HSWHead14`, `Ordinates14` for `gZ`, `ExplicitA`,
`HadamardK`, `Ordinates14`, `HSWN` for `γ`, and the `4 · 10^18` even check. -/
theorem goldbach_578_of_hsw_hsw {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA γ Z δ)
    (hH : RiemannHypothesis → SmoothT2.HadamardK γ) (h14 : SmoothT2.Ordinates14 γ)
    (hN : Lemma26H.HSWN γ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 5.78 * Real.log x ^ 2 :=
  goldbach_578_of_zeros_hsw hE hH h14 (Lemma26H.lemma26_of_hsw hN) hEv hNz hHz h14z

/-- `goldbach_578_of_bpt` of Lemma26BPTGoldbach.lean with `hS` replaced by the HSW inputs;
same conclusion. CONDITIONAL ON RH, `HSWN70`, `HSWHead14`, `Ordinates14` for `gZ`, `ExplicitA`,
`HadamardK`, `Ordinates14`, `BPTN` for `γ`, and the `4 · 10^18` even check. -/
theorem goldbach_578_of_bpt_hsw {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA γ Z δ)
    (hH : RiemannHypothesis → SmoothT2.HadamardK γ) (h14 : SmoothT2.Ordinates14 γ)
    (hN : Lemma26B.BPTN γ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 5.78 * Real.log x ^ 2 :=
  goldbach_578_of_zeros_hsw hE hH h14 (Lemma26B.lemma26_of_bpt hN) hEv hNz hHz h14z

/-- `goldbach_995_of_local36` of Local36Goldbach.lean with `hS` replaced by the HSW inputs;
same conclusion. CONDITIONAL ON RH, `HSWN70`, `HSWHead14`, `Ordinates14` for `gZ`, Chirre-Hagen's
local bound (3.6) under RH, and the `4 · 10^18` even check. -/
theorem goldbach_995_of_local36_hsw (h36 : RiemannHypothesis → Local36.Local36)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 9.95 * Real.log x ^ 2 :=
  goldbach_995_hsw (Local36.theorem2_of_RH_local36 h36) hE hNz hHz h14z

/-! ### Kaniecki 1995, both halves, through `goldbach_10_hsw` -/

open LeanLab.SchnirelmannConstant LeanLab.KanieckiGap
open LeanLab.GoldbachGaps.Sumset (GapBound1476)

/-- `KanieckiGap.kaniecki_odd_of_inputs` of Assembly.lean with `hS` replaced by the HSW inputs;
same conclusion. CONDITIONAL ON RH, `HSWN70`, `HSWHead14`, `Ordinates14` for `gZ`, the `J_ψ`
bound `h2`, the `4 · 10^18` even check, Liu-Wang 2002 and `GapBound1476`. -/
theorem kaniecki_odd_of_inputs_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ)
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100)) (hG : GapBound1476) :
    RiemannHypothesis → ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n := fun hRH =>
  kaniecki_odd_of_g10 (goldbach_10_hsw h2 hE hNz hHz h14z hRH)
    log_floor_exp3100_le (above_floor_of_liuWang hLW) hG

/-- `KanieckiGap.kaniecki_even_of_inputs` of AssemblyEven.lean with `hS` replaced by the HSW
inputs; same conclusion. CONDITIONAL ON RH, `HSWN70`, `HSWHead14`, `Ordinates14` for `gZ`, the
`J_ψ` bound `h2`, the `4 · 10^18` even check and Liu-Wang 2002. -/
theorem kaniecki_even_of_inputs_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ)
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100)) :
    RiemannHypothesis → ∀ n : ℕ, Even n → AtMostPrimes 4 n := fun hRH =>
  even_atMost4_of (goldbach_10_hsw h2 hE hNz hHz h14z hRH) hE hLW

/-- `KanieckiGap.kaniecki_odd_of_inputs'` of AssemblyEven.lean, no gap table, with `hS`
replaced by the HSW inputs; same conclusion, same proof. CONDITIONAL ON RH, `HSWN70`,
`HSWHead14`, `Ordinates14` for `gZ`, the `J_ψ` bound `h2`, the `4 · 10^18` even check and
Liu-Wang 2002. -/
theorem kaniecki_odd_of_inputs'_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ)
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100)) :
    RiemannHypothesis → ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n := by
  intro hRH n ho h1
  have hev : Even (n - 3) := by obtain ⟨k, hk⟩ := ho; exact ⟨k - 1, by omega⟩
  have h4 := kaniecki_even_of_inputs_hsw h2 hE hNz hHz h14z hLW hRH (n - 3) hev
  have h' : AtMostPrimes (1 + 4) (3 + (n - 3)) := (AtMostPrimes.prime Nat.prime_three).add h4
  have e : 3 + (n - 3) = n := by obtain ⟨k, hk⟩ := ho; omega
  rw [e] at h'
  exact h'

/-- `SchnirelmannBounds.kaniecki_odd` of Discharged.lean, with the `KanieckiInputs` fields
`h2`, `hE`, `hLW` as separate hypotheses and `hS` replaced by the HSW inputs; same conclusion
`kaniecki_odd_stmt`, whose antecedent is RH. CONDITIONAL ON `HSWN70`, `HSWHead14`, `Ordinates14`
for `gZ`, the `J_ψ` bound `h2`, the `4 · 10^18` even check and Liu-Wang 2002. -/
theorem kaniecki_odd_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    LeanLab.SchnirelmannBounds.kaniecki_odd_stmt :=
  kaniecki_odd_of_inputs'_hsw h2 hE hNz hHz h14z hLW

/-- `SchnirelmannBounds.kaniecki_even` of Discharged.lean, unbundled as `kaniecki_odd_hsw`;
same conclusion `kaniecki_even_stmt`. Same inputs as `kaniecki_odd_hsw`. -/
theorem kaniecki_even_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    LeanLab.SchnirelmannBounds.kaniecki_even_stmt := fun hRH _ =>
  kaniecki_even_of_inputs_hsw h2 hE hNz hHz h14z hLW hRH

/-- `SchnirelmannBounds.kaniecki_even_RH` of Discharged.lean, unbundled; same conclusion.
Same inputs as `kaniecki_odd_hsw`. -/
theorem kaniecki_even_RH_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14z : SmoothT2.Ordinates14 gZ) :
    RiemannHypothesis → ∀ n : ℕ, Even n → AtMostPrimes 4 n :=
  LeanLab.SchnirelmannBounds.kaniecki_even_RH_of (kaniecki_even_hsw h2 hE hLW hNz hHz h14z) hE

end LeanLab.PNTPort.ExplicitPsi1.ThetaRelDownstream
