/-
P0051 D. A. Goldston, A. I. Suriajaya, On an average Goldbach representation formula of Fujii,
arXiv 2110.14250v2, Corollary 2, eq. (34), page 6: if `1/2 ≤ Θ < 3/4` then
`Σ_{n ≤ N} ψ₂(n) = N²/2 - 2 Σ_{β ≥ 1/2} N^{ρ+1}/(ρ(ρ+1)) + o(N^{3/2})`.
Paper's proof, Section 4, page 20: eq. (13) of Theorem 1, the zeros with `β < 1/2` give
`o(N^{3/2})` by absolute convergence, and `E(N) ≪ N^{2Θ} log⁵ N` by Theorem 6 (Bhowmik,
Halupczok, Matsumoto, Suzuki), which is `o(N^{3/2})` when `Θ < 3/4`.

Here:
* `low_small`: the zeros with `β < 1/2` give `o(N^{3/2})`, unconditional, by Tannery's theorem.
* `cor2_of_E`: if `E(N) = o(N^{3/2})` then eq. (34) holds, unconditional reduction.
* `rh_of_Theta_le`: `Θ ≤ 1/2` implies Mathlib's `RiemannHypothesis`, unconditional.
* `gs_corollary2_at_half`: Corollary 2 in the case `Θ = 1/2`, PROVED unconditional as an
  implication, from `EGS_bound` of LZTheorem1RH.lean.
* `BHMSTheorem6E`: the cited input, P0051 Theorem 6, eq. (33), second half, a named hypothesis.
* `gs_corollary2_of_bhms`: Corollary 2, CONDITIONAL ON `BHMSTheorem6E`.
* `bhms_of_RH`: vacuity test, RH implies `BHMSTheorem6E`.
Unit U-1350, run PC 20261021T0403Z-14344. AI wrote this Lean code, Claude. Known mathematics.
Binary Goldbach is open; this is an average over n.
-/
import LeanLab.GoldbachAverage.LZTheorem1RH
import LeanLab.GoldbachAverage.LZ2012Lemma1
import LeanLab.GoldbachAverage.Converse

open Finset Complex Filter Topology Asymptotics
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage.GSCor2

open LeanLab.GoldbachAverage LeanLab.PNTPort.ExplicitPsi1

/-- The zero term `N^{ρ+1}/(ρ(ρ+1))`. -/
def zt (N : ℕ) (ρ : ℂ) : ℂ := (N : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))

/-- Zeros with `β ≥ 1/2`, exactly the summand of the paper's eq. (34) and of `gs_corollary2`. -/
def high (N : ℕ) (ρ : ℂ) : ℂ := if 1 / 2 ≤ ρ.re then (N : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) else 0

/-- Zeros with `β < 1/2`. -/
def low (N : ℕ) (ρ : ℂ) : ℂ := if ρ.re < 1 / 2 then zt N ρ else 0

lemma norm_mult_zt {N : ℕ} (hN : 1 ≤ N) (ρ : ℂ) :
    ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * zt N ρ‖ = (N : ℝ) ^ (ρ.re + 1) * hw ρ := by
  rw [norm_mul, zt, norm_div, norm_natCast_cpow_of_pos (by omega), Complex.norm_natCast, hw]
  simp only [add_re, one_re]
  ring

lemma norm_mult_zt_le {N : ℕ} (hN : 1 ≤ N) (ρ : NontrivialZero) :
    ‖(analyticOrderNatAt riemannZeta ρ.1 : ℂ) * zt N ρ.1‖ ≤ (N : ℝ) ^ (2 : ℝ) * hw ρ.1 := by
  rw [norm_mult_zt hN]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have : (N : ℝ) ^ (ρ.1.re + 1) ≤ (N : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [ρ.2.2.2])
  exact mul_le_mul_of_nonneg_right this (hw_nonneg _)

lemma summable_hw' : Summable (fun ρ : NontrivialZero => hw ρ.1) := LZ2012.summable_hw_NZ

lemma summable_high {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun ρ : NontrivialZero => (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * high N ρ.1) := by
  refine Summable.of_norm_bounded (summable_hw'.mul_left ((N : ℝ) ^ (2 : ℝ))) (fun ρ => ?_)
  have h := norm_mult_zt_le hN ρ
  by_cases hc : 1 / 2 ≤ ρ.1.re
  · simp only [high, if_pos hc]; exact h
  · simp only [high, if_neg hc, mul_zero, norm_zero]
    exact mul_nonneg (by positivity) (hw_nonneg _)

lemma summable_low {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun ρ : NontrivialZero => (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * low N ρ.1) := by
  refine Summable.of_norm_bounded (summable_hw'.mul_left ((N : ℝ) ^ (2 : ℝ))) (fun ρ => ?_)
  have h := norm_mult_zt_le hN ρ
  by_cases hc : ρ.1.re < 1 / 2
  · simp only [low, if_pos hc]; exact h
  · simp only [low, if_neg hc, mul_zero, norm_zero]
    exact mul_nonneg (by positivity) (hw_nonneg _)

/-- `Σ_ρ = Σ_{β ≥ 1/2} + Σ_{β < 1/2}`. -/
lemma Z1_split {N : ℕ} (hN : 1 ≤ N) :
    Z1 (N : ℝ) = zeroSum (high N) + zeroSum (low N) := by
  rw [Z1, zeroSum, zeroSum, zeroSum, ← (summable_high hN).tsum_add (summable_low hN)]
  refine tsum_congr (fun ρ => ?_)
  simp only [high, low, zt, Complex.ofReal_natCast]
  by_cases h1 : 1 / 2 ≤ ρ.1.re
  · have h2 : ¬ ρ.1.re < 1 / 2 := not_lt.mpr h1
    rw [if_pos h1, if_neg h2]; ring
  · have h2 : ρ.1.re < 1 / 2 := lt_of_not_ge h1
    rw [if_neg h1, if_pos h2]; ring

/-- **The zeros with `β < 1/2` contribute `o(N^{3/2})`**, unconditional: the paper's proof of
Corollary 2, page 20, "since the sum over zeros is absolutely convergent". -/
theorem low_small : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ‖zeroSum (low N)‖ ≤ ε * (N : ℝ) ^ ((3 : ℝ) / 2) := by
  set f : ℕ → NontrivialZero → ℂ := fun N ρ =>
    (((N : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((analyticOrderNatAt riemannZeta ρ.1 : ℂ) * low N ρ.1)
    with hf
  have hnorm : ∀ N : ℕ, 1 ≤ N → ∀ ρ : NontrivialZero, ρ.1.re < 1 / 2 →
      ‖f N ρ‖ = hw ρ.1 * (N : ℝ) ^ (ρ.1.re - 1 / 2) := by
    intro N hN ρ hc
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [hf, low, if_pos hc]
    rw [norm_mul, norm_mult_zt hN, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hN0 _)]
    rw [show ρ.1.re - 1 / 2 = -(3 / 2 : ℝ) + (ρ.1.re + 1) by ring, Real.rpow_add hN0 (-(3 / 2 : ℝ)) (ρ.1.re + 1)]
    ring
  have hzero : ∀ N : ℕ, ∀ ρ : NontrivialZero, ¬ ρ.1.re < 1 / 2 → f N ρ = 0 := by
    intro N ρ hc; simp only [hf, low, if_neg hc, mul_zero]
  have hT : Tendsto (fun N : ℕ => ∑' ρ, f N ρ) atTop (𝓝 (∑' _ρ : NontrivialZero, (0 : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence summable_hw' (fun ρ => ?_) ?_
    · by_cases hc : ρ.1.re < 1 / 2
      · show Tendsto (fun N => f N ρ) atTop (𝓝 0)
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hp : Tendsto (fun N : ℕ => hw ρ.1 * (N : ℝ) ^ (ρ.1.re - 1 / 2)) atTop
            (𝓝 (hw ρ.1 * 0)) := by
          refine Tendsto.const_mul _ ?_
          have h := (tendsto_rpow_neg_atTop (y := 1 / 2 - ρ.1.re) (by linarith)).comp
            tendsto_natCast_atTop_atTop
          refine h.congr (fun N => ?_)
          simp only [Function.comp_apply, neg_sub]
        rw [mul_zero] at hp
        refine hp.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with N hN
        rw [hnorm N hN ρ hc]
      · show Tendsto (fun N => f N ρ) atTop (𝓝 0)
        simp only [hzero _ ρ hc]; exact tendsto_const_nhds
    · filter_upwards [eventually_ge_atTop 1] with N hN
      intro ρ
      by_cases hc : ρ.1.re < 1 / 2
      · rw [hnorm N hN ρ hc]
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
        have : (N : ℝ) ^ (ρ.1.re - 1 / 2) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
        calc hw ρ.1 * (N : ℝ) ^ (ρ.1.re - 1 / 2) ≤ hw ρ.1 * 1 :=
              mul_le_mul_of_nonneg_left this (hw_nonneg _)
          _ = hw ρ.1 := mul_one _
      · rw [hzero N ρ hc, norm_zero]; exact hw_nonneg _
  rw [tsum_zero] at hT
  intro ε hε
  have hev := (hT.eventually (Metric.ball_mem_nhds (0 : ℂ) hε))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hb, hN1⟩ := hN₀ N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [dist_zero_right] at hb
  have e : ∑' ρ, f N ρ = (((N : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * zeroSum (low N) := by
    simp only [hf, zeroSum]; exact tsum_mul_left
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hN0 _)] at hb
  have hp : 0 < (N : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hN0 _
  have hinv : (N : ℝ) ^ (-(3 / 2 : ℝ)) * (N : ℝ) ^ ((3 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hN0]; norm_num
  have := mul_lt_mul_of_pos_right hb hp
  calc ‖zeroSum (low N)‖ = (N : ℝ) ^ (-(3 / 2 : ℝ)) * ‖zeroSum (low N)‖ * (N : ℝ) ^ ((3 : ℝ) / 2) := by
        rw [mul_comm ((N : ℝ) ^ (-(3 / 2 : ℝ))), mul_assoc, hinv, mul_one]
    _ ≤ ε * (N : ℝ) ^ ((3 : ℝ) / 2) := this.le

/-- A power of `log N` loses to any positive power of `N`. -/
lemma eventually_le_rpow (C a s : ℝ) (k : ℕ) (has : a < s) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C * (N : ℝ) ^ a * Real.log N ^ k ≤ ε * (N : ℝ) ^ s := by
  have hO := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (sub_pos.mpr has)).comp_tendsto
    tendsto_natCast_atTop_atTop
  have hc : 0 < ε / (|C| + 1) := div_pos hε (by positivity)
  have hb := hO.def hc
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hb.and (eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h1, hN1⟩ := hN₀ N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  simp only [Function.comp_apply, Real.rpow_natCast, Real.norm_eq_abs] at h1
  rw [abs_of_pos (Real.rpow_pos_of_pos hN0 (s - a))] at h1
  have hpa : 0 < (N : ℝ) ^ a := Real.rpow_pos_of_pos hN0 _
  have hsplit : (N : ℝ) ^ s = (N : ℝ) ^ a * (N : ℝ) ^ (s - a) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hCle : C * Real.log N ^ k ≤ |C| * |Real.log N ^ k| := by
    rw [← abs_mul]; exact le_abs_self _
  have hstep : |C| * |Real.log N ^ k| ≤ |C| * (ε / (|C| + 1) * (N : ℝ) ^ (s - a)) :=
    mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hq : |C| * (ε / (|C| + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith [abs_nonneg C]
  have hpos : 0 ≤ (N : ℝ) ^ (s - a) := (Real.rpow_pos_of_pos hN0 _).le
  calc C * (N : ℝ) ^ a * Real.log N ^ k = (N : ℝ) ^ a * (C * Real.log N ^ k) := by ring
    _ ≤ (N : ℝ) ^ a * (|C| * (ε / (|C| + 1) * (N : ℝ) ^ (s - a))) :=
        mul_le_mul_of_nonneg_left (hCle.trans hstep) hpa.le
    _ = (N : ℝ) ^ a * ((|C| * (ε / (|C| + 1))) * (N : ℝ) ^ (s - a)) := by ring
    _ ≤ (N : ℝ) ^ a * (ε * (N : ℝ) ^ (s - a)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq hpos) hpa.le
    _ = ε * (N : ℝ) ^ s := by rw [hsplit]; ring

/-- **Reduction**, unconditional: if `E(N) = o(N^{3/2})` along some admissible `r = r(N)`, then
the paper's eq. (34) holds. -/
theorem cor2_of_E (r : ℕ → ℝ) (hr : ∀ N : ℕ, 2 ≤ N → 0 < r N ∧ r N < 1)
    (hE : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖EGS N (r N)‖ ≤ ε * (N : ℝ) ^ ((3 : ℝ) / 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * zeroSum (high N)‖
        ≤ ε * (N : ℝ) ^ ((3 : ℝ) / 2) := by
  intro ε hε
  obtain ⟨K, hK⟩ := gs_theorem1_proved
  obtain ⟨N₁, h₁⟩ := hE (ε / 3) (by positivity)
  obtain ⟨N₂, h₂⟩ := low_small (ε / 6) (by positivity)
  obtain ⟨N₃, h₃⟩ := eventually_le_rpow K 1 (3 / 2) 0 (by norm_num) (ε / 3) (by positivity)
  refine ⟨max (max N₁ N₂) (max N₃ 2), fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN4 : 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hr0, hr1⟩ := hr N hN4
  set A : ℂ := ((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N - EGS N (r N)
    with hA
  have key : ((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * zeroSum (high N) =
      A + EGS N (r N) - 2 * zeroSum (low N) := by
    rw [hA, Z1_split (by omega)]; ring
  rw [key]
  have hAK : ‖A‖ ≤ ε / 3 * (N : ℝ) ^ ((3 : ℝ) / 2) := by
    have := h₃ N hN3
    simp only [Real.rpow_one, pow_zero, mul_one] at this
    exact (hK N hN4 (r N) hr0 hr1).trans this
  have hL : ‖2 * zeroSum (low N)‖ ≤ 2 * (ε / 6 * (N : ℝ) ^ ((3 : ℝ) / 2)) := by
    rw [norm_mul, Complex.norm_two]; exact mul_le_mul_of_nonneg_left (h₂ N hN2) (by norm_num)
  calc ‖A + EGS N (r N) - 2 * zeroSum (low N)‖
      ≤ ‖A‖ + ‖EGS N (r N)‖ + ‖2 * zeroSum (low N)‖ := by
        have a1 := norm_sub_le (A + EGS N (r N)) (2 * zeroSum (low N))
        have a2 := norm_add_le A (EGS N (r N))
        linarith
    _ ≤ ε / 3 * (N : ℝ) ^ ((3 : ℝ) / 2) + ε / 3 * (N : ℝ) ^ ((3 : ℝ) / 2)
        + 2 * (ε / 6 * (N : ℝ) ^ ((3 : ℝ) / 2)) := by
        have := h₁ N hN1
        linarith
    _ = ε * (N : ℝ) ^ ((3 : ℝ) / 2) := by ring

/-- Every nontrivial zero has real part at most `Θ`. -/
lemma re_le_Theta (ρ : NontrivialZero) : ρ.1.re ≤ Theta := by
  unfold Theta
  refine le_csSup ⟨1, ?_⟩ ⟨ρ, rfl⟩
  rintro _ ⟨σ, rfl⟩
  exact σ.2.2.2.le

open LeanLab.PNTPort.ZetaZeros in
/-- `Θ ≤ 1/2` implies Mathlib's `RiemannHypothesis`, unconditional, by the functional equation;
same case split as `Converse.rh_of_avgRH`. -/
theorem rh_of_Theta_le (h : Theta ≤ 1 / 2) : RiemannHypothesis := by
  intro s hz htriv hs1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · by_cases h0 : 0 < s.re
    · have hz' := zeta_one_sub_eq_zero h0 (by linarith) hz
      have : (1 - s).re ≤ Theta := re_le_Theta ⟨1 - s, hz',
        by simp only [Complex.sub_re, Complex.one_re]; linarith,
        by simp only [Complex.sub_re, Complex.one_re]; linarith⟩
      simp only [Complex.sub_re, Complex.one_re] at this; linarith
    · push_neg at h0
      by_cases him : s.im = 0
      · exact Converse.zeta_ne_zero_real_nonpos h0 him htriv hz
      · exact zeta_ne_zero_of_re_nonpos h0 him hz
  · by_cases h1 : s.re < 1
    · have : s.re ≤ Theta := re_le_Theta ⟨s, hz, by linarith, h1⟩
      linarith
    · exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h1) hz

/-- Under RH, `Θ ≤ 1/2`; with no nontrivial zero `Θ = sSup ∅ = 0`. -/
lemma Theta_le_of_RH (hRH : RiemannHypothesis) : Theta ≤ 1 / 2 := by
  unfold Theta
  refine Real.sSup_le ?_ (by norm_num)
  rintro _ ⟨ρ, rfl⟩
  have h := hRH ρ.1 ρ.2.1 (by
      rintro ⟨n, hn⟩
      have hre : ρ.1.re = -2 * ((n : ℝ) + 1) := by rw [hn]; simp
      have h0 := ρ.2.2.1
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
    (by intro h1; have := ρ.2.2.2; rw [h1] at this; simp at this)
  exact h.le

/-- **P0051 Corollary 2 in the case `Θ = 1/2`**, PROVED unconditional as an implication:
`Θ ≤ 1/2` gives RH, and under RH `E(N) ≪ N log³ N` by the lab's `EGS_bound`. -/
theorem gs_corollary2_at_half (hlo : 1 / 2 ≤ Theta) (hhi : Theta ≤ 1 / 2) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2
        + 2 * zeroSum (fun ρ => if 1 / 2 ≤ ρ.re then (N : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) else 0)‖
        ≤ ε * (N : ℝ) ^ ((3 : ℝ) / 2) := by
  have hRH := rh_of_Theta_le hhi
  obtain ⟨K, hK⟩ := EGS_bound hRH
  refine cor2_of_E (fun N => Real.exp (-(1 / (N : ℝ)))) (fun N hN => ⟨Real.exp_pos _, ?_⟩) ?_
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    calc Real.exp (-(1 / (N : ℝ))) < Real.exp 0 :=
          Real.exp_lt_exp.mpr (by have := one_div_pos.mpr hN0; linarith)
      _ = 1 := Real.exp_zero
  · intro ε hε
    obtain ⟨N₀, hN₀⟩ := eventually_le_rpow K 1 (3 / 2) 3 (by norm_num) ε hε
    refine ⟨max N₀ 2, fun N hN => ?_⟩
    have h := hN₀ N (le_trans (le_max_left _ _) hN)
    rw [Real.rpow_one] at h
    exact (hK N (le_trans (le_max_right _ _) hN)).trans h

/-- **The cited input**: P0051 Theorem 6, eq. (33), second half, page 6, due to Bhowmik,
Halupczok, Matsumoto and Suzuki, Mathematika 65 (2019): assuming `1/2 < Θ < 1`, for `N ≥ 2`,
`E(N) ≪ N^{2Θ} log⁵ N`. The paper bounds `𝓔(N) ≥ |E(N)|`, eq. (18); `E(N)` does not depend on
`r`, eq. (12). A named hypothesis, not asserted. -/
def BHMSTheorem6E : Prop :=
  1 / 2 < Theta → Theta < 1 → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ r : ℝ, 0 < r → r < 1 →
    ‖EGS N r‖ ≤ C * (N : ℝ) ^ (2 * Theta) * Real.log N ^ 5

/-- Vacuity test: the hypothesis `BHMSTheorem6E` holds under RH, where `Θ ≤ 1/2`. -/
theorem bhms_of_RH (hRH : RiemannHypothesis) : BHMSTheorem6E := by
  intro h; exact absurd h (not_lt.mpr (Theta_le_of_RH hRH))

/-- **P0051 Corollary 2**, CONDITIONAL ON `BHMSTheorem6E`: if `1/2 ≤ Θ < 3/4` then
`Σ_{n ≤ N} ψ₂(n) = N²/2 - 2 Σ_{β ≥ 1/2} N^{ρ+1}/(ρ(ρ+1)) + o(N^{3/2})`. The case `Θ = 1/2`
uses no hypothesis, see `gs_corollary2_at_half`. -/
theorem gs_corollary2_of_bhms (h6 : BHMSTheorem6E) : 1 / 2 ≤ Theta → Theta < 3 / 4 →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2
        + 2 * zeroSum (fun ρ => if 1 / 2 ≤ ρ.re then (N : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) else 0)‖
        ≤ ε * (N : ℝ) ^ ((3 : ℝ) / 2) := by
  intro hlo hhi
  by_cases hgt : 1 / 2 < Theta
  · obtain ⟨C, hC⟩ := h6 hgt (by linarith)
    refine cor2_of_E (fun _ => 1 / 2) (fun _ _ => ⟨by norm_num, by norm_num⟩) ?_
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := eventually_le_rpow C (2 * Theta) (3 / 2) 5 (by linarith) ε hε
    refine ⟨max N₀ 2, fun N hN => ?_⟩
    exact (hC N (le_trans (le_max_right _ _) hN) _ (by norm_num) (by norm_num)).trans
      (hN₀ N (le_trans (le_max_left _ _) hN))
  · exact gs_corollary2_at_half hlo (not_lt.mp hgt)

/-- Faithfulness: given the cited input, the conclusion has exactly the type of the cited
`gs_corollary2` in Unconditional.lean. -/
example (h6 : BHMSTheorem6E) : type_of% gs_corollary2 := gs_corollary2_of_bhms h6

end LeanLab.GoldbachAverage.GSCor2
