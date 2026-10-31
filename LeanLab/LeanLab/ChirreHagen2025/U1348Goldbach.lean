/-
P0075 line, T2, unit U-1348, I-5171, PC run 20261021T0403Z-14344, 2026-10-21.
The RH Goldbach interval from the new Section 5 weight, `large_c_u1348` of U1348Bilinear.lean,
with `Jtheta_le_of_c` of SmoothJ.lean as in goldbach_451_of_u6806_J.
- `goldbach_445_of_J`: J_ψ ≤ 1.0069 δ log²(2.0001/δ) x², the conclusion of theorem2_u6806,
  gives a Goldbach number in `(x, x + 4.45 log² x)` for every `x ≥ 3`, H = 4.44.
- `goldbach_449_of_J`: the same from J_ψ constant 1.0159, the conclusion of theorem2_u6759.
- `goldbach_471_of_u1263f`: fully composed with U1263.Fine.theorem2_u1263f, J_ψ 1.0661,
  4.71 log² x against the lab's 4.78 for the same J; CONDITIONAL ON ExplicitA, HadamardK,
  Ordinates14, BPTN, SchoenfeldTheta and the 4·10^18 check, under RH.
Each is CONDITIONAL ON its J_ψ hypothesis, SchoenfeldTheta and the 4·10^18 even check, under RH.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is open.
-/
import Mathlib
import LeanLab.ChirreHagen2025.U1348Bilinear
import LeanLab.ChirreHagen2025.U1263Theorem2Fine

namespace LeanLab.ChirreHagen2025.U1348
open Real Chebyshev
open LeanLab.ChirreHagen2025

/-- The generic step: from a J_ψ constant `J` with the margin `hm`, an interval of length
`H + 1/100` times `log² x`. -/
theorem goldbach_of_J {J H : ℝ} (hJ0 : 0 ≤ J) (hH1 : 4 ≤ H) (hH : H ≤ 61.5)
    (hm : (1.001 * J + 0.0019) * 0.24922 < H * ((11 / 5 * (((5 / 11) ^ 3 - (1 / 64) ^ 3) / 3
        - ((5 / 11) ^ 4 - (1 / 64) ^ 4) / 4)
      + (((1 / 2) ^ 2 - (5 / 11) ^ 2) / 2 - ((1 / 2) ^ 3 - (5 / 11) ^ 3) / 3))
      - (11 / 10 * (10 * (5 / 11 - 1 / 64) + 2 * (5 / 11) + 2 * (1 / 64))
        + (3 * (1 / 2 - 5 / 11) + 2 * (1 / 2) + 2 * (5 / 11))
        + 11 / 10 * (16 * (63 / 64 - 6 / 11) + 2 * (63 / 64) + 2 * (6 / 11))
        + (3 * (6 / 11 - 1 / 2) + 2 * (6 / 11) + 2 * (1 / 2))) / 10 ^ 6))
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ J * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + (H + 1 / 100) * Real.log x ^ 2 := by
  intro hRH x hx
  have hlog : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, hn, h1, h2'⟩ := small_of hE x (by linarith) hs
    exact ⟨n, hn, h1, by nlinarith [hlog]⟩
  · have hx' : 1.1 * 10 ^ 18 ≤ x := by linarith
    have hxpos : 0 < x := by linarith
    have hL : 41 ≤ Real.log x := log_ge_41 hx'
    set δ := H * Real.log x ^ 2 / x with hδ
    have hδpos : 0 < δ := div_pos (mul_pos (by linarith) (by positivity)) hxpos
    have hδ13 : δ ≤ 1 / 10 ^ 13 := by
      have := threshold2 hx'
      have : δ ≤ 61.5 * Real.log x ^ 2 / x := by
        rw [hδ]; apply div_le_div_of_nonneg_right _ hxpos.le; nlinarith [sq_nonneg (Real.log x)]
      linarith
    have hsx : δ * √x < 1 := by
      have hc := log_cube_div_sqrt (by linarith : (10 : ℝ) ^ 18 ≤ x)
      have hsx0 : 0 < √x := Real.sqrt_pos.mpr hxpos
      have hss : √x * √x = x := Real.mul_self_sqrt hxpos.le
      have e0 : δ * √x * √x = H * Real.log x ^ 2 := by
        rw [mul_assoc, hss, hδ]; field_simp
      have e : δ * √x = H * (Real.log x ^ 2 / √x) := by
        rw [show H * (Real.log x ^ 2 / √x) = H * Real.log x ^ 2 / √x by ring,
          eq_div_iff hsx0.ne']
        exact e0
      have h23 : Real.log x ^ 2 ≤ Real.log x ^ 3 := by nlinarith
      have h4 : Real.log x ^ 2 / √x ≤ 7.5 / 10 ^ 5 :=
        le_trans (div_le_div_of_nonneg_right h23 hsx0.le) hc
      have h5 : 0 ≤ Real.log x ^ 2 / √x := by positivity
      rw [e]
      have : H * (Real.log x ^ 2 / √x) ≤ 61.5 * (7.5 / 10 ^ 5) :=
        mul_le_mul hH h4 h5 (by norm_num)
      linarith
    obtain ⟨n, hn, h1, h2'⟩ := large_c_u1348 (c := 1.001 * J + 0.0019) (H := H)
      (by linarith) (by linarith) hH hm (thetaRel6_of_schoenfeld (hS hRH)) x hx'
      (fun X hX1 hX2 => by
        rw [← hδ]
        have hX : 5 * 10 ^ 17 ≤ X := by linarith
        have hsX : δ * √X < 1 :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hX2) hδpos.le) hsx
        exact Jtheta_le_of_c hJ0 (h2 hRH X δ (by linarith) hδpos hδ13) hX hδpos hδ13 hsX)
    exact ⟨n, hn, h1, by nlinarith [sq_nonneg (Real.log x)]⟩

/-- Under RH, from J_ψ constant 1.0069, the conclusion of theorem2_u6806: a Goldbach number in
`(x, x + 4.45 log² x)` for every `x ≥ 3`. -/
theorem goldbach_445_of_J
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.0069 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.45 * Real.log x ^ 2 := by
  have := goldbach_of_J (J := 1.0069) (H := 4.44) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h2 hE hS
  intro hRH x hx
  obtain ⟨n, hn, h1, h3⟩ := this hRH x hx
  have e : (4.44 : ℝ) + 1 / 100 = 4.45 := by norm_num
  rw [e] at h3
  exact ⟨n, hn, h1, h3⟩

/-- Under RH, from J_ψ constant 1.0159, the conclusion of theorem2_u6759: `4.49 log² x`. -/
theorem goldbach_449_of_J
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.0159 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.49 * Real.log x ^ 2 := by
  have := goldbach_of_J (J := 1.0159) (H := 4.48) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h2 hE hS
  intro hRH x hx
  obtain ⟨n, hn, h1, h3⟩ := this hRH x hx
  have e : (4.48 : ℝ) + 1 / 100 = 4.49 := by norm_num
  rw [e] at h3
  exact ⟨n, hn, h1, h3⟩

/-- Under RH, from J_ψ constant 1.0661 of theorem2_u1263f: `4.71 log² x`. -/
theorem goldbach_471_of_J
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.0661 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.71 * Real.log x ^ 2 := by
  have := goldbach_of_J (J := 1.0661) (H := 4.70) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h2 hE hS
  intro hRH x hx
  obtain ⟨n, hn, h1, h3⟩ := this hRH x hx
  have e : (4.70 : ℝ) + 1 / 100 = 4.71 := by norm_num
  rw [e] at h3
  exact ⟨n, hn, h1, h3⟩

/-- Fully composed: `goldbach_471_of_J` with U1263.Fine's theorem2_u1263f, the same six inputs
as goldbach_478_of_u1263f. -/
theorem goldbach_471_of_u1263f {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA γ Z δ)
    (hH : RiemannHypothesis → SmoothT2.HadamardK γ) (h14 : SmoothT2.Ordinates14 γ)
    (hN : RiemannHypothesis → Lemma26B.BPTN γ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.71 * Real.log x ^ 2 :=
  goldbach_471_of_J (fun hRH => SmoothT2.theorem2_u1263f (hE hRH) (hH hRH) h14 (hN hRH)) hEv hS

end LeanLab.ChirreHagen2025.U1348
