/-
P0095 W. C. Lu 2010, Exceptional set of Goldbach number, J. Number Theory 130, 2359-2392.
Unit U-1545, run 20261026T0808Z-17522, ARCHITECT DECOMPOSE, track T1.

File c of three: Lemma 5 at the paper's parameters, the display on p. 2369 between (39) and (40),
  `|∫_a^b (td)^{ρ₁-1} (N - td)^{ρ₂-1} dt| ≤ θ₁ M^{-1/2} d⁻¹ N^{β₁+β₂-1}`
for `M < |γ₁| + |γ₂|`, "using Lemma 5 again with v₁ = u₁ = u₂ = 0 and v₂ = d", with
`d = N^{0.9999}`, `a = N^{0.0001}/3`, `b = N/d - a` of p. 2360. Here `θ₁ = 384`: from
`ad - d - 1 ≥ N/4` for large `N` one gets `(ad - d - 1)^{β₁+β₂-2} ≤ 16 N^{β₁+β₂-2}`, and
`24 · 16 = 384`. The integral times `d` is the lab's `Lu2010ZeroIntegral.J` at real `N`.

Leaves: `paper_valid`, `paper_m_ge`, `rpow_m_le`. Assemblies, zero sorry, CONDITIONAL ON these
leaves and on the leaves of Decomp1545b: `zero_integral_bound`, `zero_integral_M`.

AI wrote this Lean code, Claude, unit U-1545. Checked only by the Lean kernel.
KNOWN mathematics. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.Decomp1545b

namespace LeanLab.ExceptionalSet.Decomp1545c

open Real Set
open LeanLab.ExceptionalSet.Decomp1545b

/-- `d = N^{0.9999}`, p. 2360, at real `N`; the same as `Lu2010Assembly.dd`. -/
noncomputable def dR (N : ℝ) : ℝ := N ^ (0.9999 : ℝ)

/-- `a = N^{0.0001}/3`, p. 2360. -/
noncomputable def aR (N : ℝ) : ℝ := N ^ (0.0001 : ℝ) / 3

/-- `b = N/d - a`, p. 2360. -/
noncomputable def bR (N : ℝ) : ℝ := N / dR N - aR N

/-- The data of Lemma 5 as used on p. 2369: `v₁ = u₁ = u₂ = 0`, `v₂ = d`. -/
noncomputable def pp (N : ℝ) : Prm := ⟨N, dR N, aR N, bR N, 0, 0, dR N, 0⟩

lemma Asymptotics_trick (N : ℝ) (hN : (30:ℝ) ^ (10000:ℝ) ≤ N) : N ^ (0.9999 : ℝ) + 1 ≤ N / 12 := by
  have h_pos : 0 < N := by
    calc 0 < (30:ℝ) ^ (10000:ℝ) := by positivity
         _ ≤ N := hN
  have h_pow : N ^ (0.9999 : ℝ) = N / N ^ (0.0001 : ℝ) := by
    calc N ^ (0.9999 : ℝ) = N ^ (1 - 0.0001 : ℝ) := by congr 1; norm_num
         _ = N ^ (1:ℝ) / N ^ (0.0001 : ℝ) := by exact Real.rpow_sub h_pos 1 0.0001
         _ = N / N ^ (0.0001 : ℝ) := by rw [Real.rpow_one]
  rw [h_pow]
  have h_bound : 24 ≤ N ^ (0.0001 : ℝ) := by
    have h_pos_30 : 0 ≤ (30:ℝ) := by norm_num
    calc (24:ℝ) ≤ 30 := by norm_num
         _ = (30:ℝ) ^ (1:ℝ) := by exact Eq.symm (Real.rpow_one 30)
         _ = (30:ℝ) ^ (10000 * 0.0001 : ℝ) := by congr 1; norm_num
         _ = ((30:ℝ) ^ (10000 : ℝ)) ^ (0.0001 : ℝ) := by rw [Real.rpow_mul h_pos_30 10000 0.0001]
         _ ≤ N ^ (0.0001 : ℝ) := Real.rpow_le_rpow (by positivity) hN (by norm_num)
  have h_N_div : N / N ^ (0.0001 : ℝ) ≤ N / 24 := by
    exact div_le_div_of_nonneg_left h_pos.le (by norm_num) h_bound
  have h_1_le : 1 ≤ N / 24 := by
    calc (1:ℝ) = 24 / 24 := by norm_num
         _ ≤ (30:ℝ) ^ (10000:ℝ) / 24 := by
           apply div_le_div_of_nonneg_right _ (by norm_num)
           have h24 : (24:ℝ) ≤ (30:ℝ) ^ (1:ℝ) := by norm_num
           calc (24:ℝ) ≤ (30:ℝ) ^ (1:ℝ) := h24
                _ ≤ (30:ℝ) ^ (10000:ℝ) := by
                  apply Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
         _ ≤ N / 24 := by apply div_le_div_of_nonneg_right hN (by norm_num)
  calc N / N ^ (0.0001 : ℝ) + 1 ≤ N / 24 + N / 24 := add_le_add h_N_div h_1_le
       _ = N / 12 := by ring

lemma m_lower (N : ℝ) (hN : (30:ℝ) ^ (10000:ℝ) ≤ N) : N / 4 ≤ (pp N).m := by
  have hN_pos : 0 < N := by
    calc 0 < (30:ℝ) ^ (10000:ℝ) := by positivity
         _ ≤ N := hN
  have h_m : (pp N).m = N / 3 - N ^ (0.9999 : ℝ) - 1 := by
    simp only [pp, Prm.m, aR, dR]
    have h_pow : N ^ (0.0001:ℝ) * N ^ (0.9999:ℝ) = N ^ (1:ℝ) := by
      rw [← Real.rpow_add hN_pos]
      norm_num
    calc (N ^ (0.0001:ℝ) / 3) * N ^ (0.9999:ℝ) - N ^ (0.9999:ℝ) - 1
      _ = (N ^ (0.0001:ℝ) * N ^ (0.9999:ℝ)) / 3 - N ^ (0.9999:ℝ) - 1 := by ring
      _ = N / 3 - N ^ (0.9999:ℝ) - 1 := by rw [h_pow, Real.rpow_one]
  rw [h_m]
  have h_bound := Asymptotics_trick N hN
  have h_N_div_4 : N / 4 = N / 3 - N / 12 := by ring
  rw [h_N_div_4]
  linarith

/-- LEAF. Unit U-1545. The paper's parameters satisfy the hypotheses of Lemma 5 for large `N`:
`d > 0`, `a ≤ b`, `bd + ad = N`, `ad - d - 1 = N/3 - N^{0.9999} - 1 > 0`, `v₂ = d`. -/
theorem paper_valid : ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N → (pp N).Valid := by
  use (30:ℝ) ^ (10000:ℝ)
  intro N hN
  have hN_pos : 0 < N := by
    calc 0 < (30:ℝ) ^ (10000:ℝ) := by positivity
         _ ≤ N := hN
  have hd : 0 < dR N := Real.rpow_pos_of_pos hN_pos _
  unfold Prm.Valid
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hd
  · have hm : N / 4 ≤ (pp N).m := m_lower N hN
    have hm_pos : 0 < (pp N).m := by
      calc 0 < N / 4 := div_pos hN_pos (by norm_num)
           _ ≤ (pp N).m := hm
    have h_aR_bR : (pp N).a ≤ (pp N).b ↔ 2 * (pp N).a ≤ (pp N).N / (pp N).d := by
      change aR N ≤ bR N ↔ 2 * aR N ≤ N / dR N
      change aR N ≤ N / dR N - aR N ↔ 2 * aR N ≤ N / dR N
      constructor
      · intro h; linarith
      · intro h; linarith
    have hb : 2 * aR N ≤ N / dR N := by
      change 2 * (N ^ (0.0001:ℝ) / 3) ≤ N / N ^ (0.9999:ℝ)
      have h4 : N / N ^ (0.9999:ℝ) = N ^ (0.0001:ℝ) := by
        calc N / N ^ (0.9999:ℝ) = N ^ (1:ℝ) / N ^ (0.9999:ℝ) := by rw [Real.rpow_one]
             _ = N ^ (1 - 0.9999:ℝ) := by exact (Real.rpow_sub hN_pos 1 0.9999).symm
             _ = N ^ (0.0001:ℝ) := by congr 1; norm_num
      rw [h4]
      have h5 : 0 ≤ N ^ (0.0001:ℝ) := by positivity
      linarith
    exact h_aR_bR.mpr hb
  · change bR N * dR N + aR N * dR N = N
    change (N / dR N - aR N) * dR N + aR N * dR N = N
    calc (N / dR N - aR N) * dR N + aR N * dR N = (N / dR N) * dR N - aR N * dR N + aR N * dR N := by ring
         _ = (N / dR N) * dR N := by ring
         _ = N := div_mul_cancel₀ _ hd.ne'
  · have hm : N / 4 ≤ (pp N).m := m_lower N hN
    calc 0 < N / 4 := div_pos hN_pos (by norm_num)
         _ ≤ (pp N).m := hm
  · simp only [pp, le_refl]
  · simp only [pp]
    exact hd.le
  · simp only [pp]
    norm_num
  · simp only [pp, le_refl]
  · simp only [pp]
    exact hd.le
  · simp only [pp, le_refl]
  · simp only [pp]
    norm_num
  · simp only [pp, le_refl]

/-- LEAF. Unit U-1545. `ad - d - 1 ≥ N/4` for large `N`, since `ad = N/3` and `d = o(N)`. -/
theorem paper_m_ge : ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N → N / 4 ≤ (pp N).m := by
  use (30:ℝ) ^ (10000:ℝ)
  intro N hN
  exact m_lower N hN

/-- LEAF. Unit U-1545. For `N > 0`, `m ≥ N/4` and `-2 ≤ e ≤ 0`, `m^e ≤ 16 N^e`. -/
theorem rpow_m_le {N m e : ℝ} (hN : 0 < N) (hm : N / 4 ≤ m) (he1 : -2 ≤ e) (he2 : e ≤ 0) :
    m ^ e ≤ 16 * N ^ e := by
  have hm_pos : 0 < m := by linarith
  have hN4_pos : 0 < N / 4 := by linarith
  have h1 : m ^ e ≤ (N / 4) ^ e := Real.rpow_le_rpow_of_nonpos hN4_pos hm he2
  have h2 : (N / 4) ^ e = N ^ e / (4:ℝ) ^ e := by
    have h4_nonneg : (0:ℝ) ≤ 4 := by norm_num
    exact @Real.div_rpow N 4 hN.le h4_nonneg e
  have h3 : N ^ e / (4:ℝ) ^ e = (4:ℝ) ^ (-e) * N ^ e := by
    rw [Real.rpow_neg (by norm_num)]
    ring
  have h4 : (4:ℝ) ^ (-e) ≤ (4:ℝ) ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h5 : (4:ℝ) ^ (2:ℝ) = 16 := by norm_num
  rw [h5] at h4
  have h6 : (4:ℝ) ^ (-e) * N ^ e ≤ 16 * N ^ e := mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hN.le e)
  linarith

/-- ASSEMBLY, CONDITIONAL ON `paper_valid`, `paper_m_ge`, `rpow_m_le` and, through `lemma5`, the
leaves of Decomp1545b: for large `N`, all `0 ≤ β_j ≤ 1` and `|γ₁| + |γ₂| > 0`,
`|d ∫_a^b (td)^{ρ₁-1} (N - td)^{ρ₂-1} dt| ≤ 384 (|γ₁| + |γ₂|)^{-1/2} N^{β₁+β₂-1}`. -/
theorem zero_integral_bound : ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N → ∀ ρ1 ρ2 : ℂ,
    0 ≤ ρ1.re → ρ1.re ≤ 1 → 0 ≤ ρ2.re → ρ2.re ≤ 1 → 0 < |ρ1.im| + |ρ2.im| →
    ‖(dR N : ℂ) * ∫ t in aR N..bR N,
        ((t * dR N : ℝ) : ℂ) ^ (ρ1 - 1) * ((N - t * dR N : ℝ) : ℂ) ^ (ρ2 - 1)‖ ≤
      384 * (|ρ1.im| + |ρ2.im|) ^ (-(1 / 2) : ℝ) * N ^ (ρ1.re + ρ2.re - 1) := by
  obtain ⟨N1, hN1⟩ := paper_valid
  obtain ⟨N2, hN2⟩ := paper_m_ge
  refine ⟨max N1 N2, fun N hN ρ1 ρ2 h10 h11 h20 h21 hG => ?_⟩
  have hv := hN1 N (le_trans (le_max_left _ _) hN)
  have hm := hN2 N (le_trans (le_max_right _ _) hN)
  have hNpos : 0 < N := hv.N_pos
  have hd : 0 < dR N := hv.d_pos
  have hL := lemma5 hv ρ1 ρ2 h11 h21 hG
  have hint : ∫ t in aR N..bR N,
        ((t * dR N : ℝ) : ℂ) ^ (ρ1 - 1) * ((N - t * dR N : ℝ) : ℂ) ^ (ρ2 - 1) =
      ∫ t in (pp N).a..(pp N).b,
        (((pp N).A t : ℝ) : ℂ) ^ (ρ1 - 1) * (((pp N).B t : ℝ) : ℂ) ^ (ρ2 - 1) := by
    apply intervalIntegral.integral_congr
    intro t _
    have hA : (pp N).A t = t * dR N := by simp only [pp, Prm.A]; ring
    have hB : (pp N).B t = N - t * dR N := by simp only [pp, Prm.B]; ring
    simp only [hA, hB]
  have hpow := rpow_m_le hNpos hm (e := ρ1.re + ρ2.re - 2) (by linarith) (by linarith)
  have hGp : 0 ≤ (|ρ1.im| + |ρ2.im|) ^ (-(1 / 2) : ℝ) := by positivity
  have hNe : N * N ^ (ρ1.re + ρ2.re - 2) = N ^ (ρ1.re + ρ2.re - 1) := by
    rw [show ρ1.re + ρ2.re - 1 = 1 + (ρ1.re + ρ2.re - 2) by ring, Real.rpow_add hNpos,
      Real.rpow_one]
  rw [hint, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  calc dR N * ‖∫ t in (pp N).a..(pp N).b,
        (((pp N).A t : ℝ) : ℂ) ^ (ρ1 - 1) * (((pp N).B t : ℝ) : ℂ) ^ (ρ2 - 1)‖
      ≤ dR N * (24 * (pp N).N * (pp N).d⁻¹ * (pp N).m ^ (ρ1.re + ρ2.re - 2) *
          (|ρ1.im| + |ρ2.im|) ^ (-(1 / 2) : ℝ)) := mul_le_mul_of_nonneg_left hL hd.le
    _ = 24 * N * (pp N).m ^ (ρ1.re + ρ2.re - 2) * (|ρ1.im| + |ρ2.im|) ^ (-(1 / 2) : ℝ) := by
        simp only [pp]; field_simp
    _ ≤ 24 * N * (16 * N ^ (ρ1.re + ρ2.re - 2)) * (|ρ1.im| + |ρ2.im|) ^ (-(1 / 2) : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hGp
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 384 * (|ρ1.im| + |ρ2.im|) ^ (-(1 / 2) : ℝ) * N ^ (ρ1.re + ρ2.re - 1) := by
        rw [← hNe]; ring

/-- ASSEMBLY. The display of p. 2369 with `θ₁ = 384`, CONDITIONAL ON the leaves through
`zero_integral_bound`: for large `N`, `M > 0`, `M < |γ₁| + |γ₂|` and `0 ≤ β_j ≤ 1`,
`|d ∫_a^b (td)^{ρ₁-1} (N - td)^{ρ₂-1} dt| ≤ 384 M^{-1/2} N^{β₁+β₂-1}`; Lu writes it as
`θ₁ M^{-1/2} d⁻¹ N^{β₁+β₂-1}` for the integral without the factor `d`. -/
theorem zero_integral_M : ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N → ∀ (M : ℝ) (ρ1 ρ2 : ℂ), 0 < M →
    M < |ρ1.im| + |ρ2.im| → 0 ≤ ρ1.re → ρ1.re ≤ 1 → 0 ≤ ρ2.re → ρ2.re ≤ 1 →
    ‖(dR N : ℂ) * ∫ t in aR N..bR N,
        ((t * dR N : ℝ) : ℂ) ^ (ρ1 - 1) * ((N - t * dR N : ℝ) : ℂ) ^ (ρ2 - 1)‖ ≤
      384 * M ^ (-(1 / 2) : ℝ) * N ^ (ρ1.re + ρ2.re - 1) := by
  obtain ⟨N0, h0⟩ := zero_integral_bound
  refine ⟨max N0 1, fun N hN M ρ1 ρ2 hM hMG h10 h11 h20 h21 => ?_⟩
  have hG : 0 < |ρ1.im| + |ρ2.im| := lt_trans hM hMG
  have h := h0 N (le_trans (le_max_left _ _) hN) ρ1 ρ2 h10 h11 h20 h21 hG
  have hN1 : (1 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hmono : (|ρ1.im| + |ρ2.im|) ^ (-(1 / 2) : ℝ) ≤ M ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hM hMG.le (by norm_num)
  have hNp : 0 ≤ N ^ (ρ1.re + ρ2.re - 1) := Real.rpow_nonneg (by linarith) _
  refine le_trans h ?_
  have := mul_le_mul_of_nonneg_right hmono hNp
  nlinarith

end LeanLab.ExceptionalSet.Decomp1545c
