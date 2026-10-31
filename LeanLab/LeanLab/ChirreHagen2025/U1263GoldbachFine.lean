/-
P0075 line, T2, unit U-1270, run 20261020T1803Z-21834, 2026-10-20.
Under RH, a Goldbach number in `(x, x + 4.78 log² x)` for every `x ≥ 3`: `goldbach_448_of_sharp`
of SharpGoldbach.lean with the J_ψ constant 1.0661 of U1263Theorem2Fine.lean and H = 4.77, by a
script. CONDITIONAL ON ExplicitA, HadamardK, Ordinates14, BPTN (Brent-Platt-Trudgian Lemma 1),
SchoenfeldTheta and the 4·10^18 even check, under RH; it does NOT use ZeroSumSharp.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is open.
-/
import Mathlib
import LeanLab.ChirreHagen2025.SharpGoldbach
import LeanLab.ChirreHagen2025.U1263Theorem2Fine

namespace LeanLab.ChirreHagen2025
open Real Chebyshev Finset

theorem goldbach_478_of_u1263f_J
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.0661 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.78 * Real.log x ^ 2 := by
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
    set δ := 4.77 * Real.log x ^ 2 / x with hδ
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
      have e0 : δ * √x * √x = 4.77 * Real.log x ^ 2 := by
        rw [mul_assoc, hss, hδ]; field_simp
      have e : δ * √x = 4.77 * (Real.log x ^ 2 / √x) := by
        rw [show 4.77 * (Real.log x ^ 2 / √x) = 4.77 * Real.log x ^ 2 / √x by ring,
          eq_div_iff hsx0.ne']
        exact e0
      have h23 : Real.log x ^ 2 ≤ Real.log x ^ 3 := by nlinarith
      have : Real.log x ^ 2 / √x ≤ 7.5 / 10 ^ 5 :=
        le_trans (div_le_div_of_nonneg_right h23 hsx0.le) hc
      rw [e]; linarith
    obtain ⟨n, hn, h1, h2'⟩ := large_c_of128 (c := 1.001 * 1.0661 + 0.0019) (H := 4.77) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (thetaRel_of_schoenfeld (hS hRH)) x hx'
      (fun X hX1 hX2 => by
        rw [← hδ]
        have hX : 5 * 10 ^ 17 ≤ X := by linarith
        have hsX : δ * √X < 1 :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hX2) hδpos.le) hsx
        exact Jtheta_le_of_c (by norm_num) (h2 hRH X δ (by linarith) hδpos hδ13) hX hδpos hδ13 hsX)
    exact ⟨n, hn, h1, by nlinarith⟩


theorem goldbach_478_of_u1263f {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA γ Z δ)
    (hH : RiemannHypothesis → SmoothT2.HadamardK γ) (h14 : SmoothT2.Ordinates14 γ)
    (hN : RiemannHypothesis → Lemma26B.BPTN γ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.78 * Real.log x ^ 2 :=
  goldbach_478_of_u1263f_J (fun hRH => SmoothT2.theorem2_u1263f (hE hRH) (hH hRH) h14 (hN hRH)) hEv hS

end LeanLab.ChirreHagen2025
