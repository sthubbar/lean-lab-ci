/-
Cited wall decision for `U1539.lemma9`, P0082, J. Brüdern and A. Perelli,
Goldbach numbers in sparse sequences, Ann. Inst. Fourier 48 (1998) 353-378,
Lemma 9 page 368, proved in section 7 page 370. Run CLOUD-cited-lemma9, 2026-11-20.

VERDICT: FORMALIZE. Lemma 9 is not a cited result. It is the paper's own statement,
proved on half a page, whose only inputs are the paper's Theorem 2, page 354, and
Lemma 4, page 359. Both already exist as the Props `Theorem2` and `Lemma4` of
State1539Data264. Proved here with no open step of their own:

* `shift_minor_of_theorem2`: the DQ5 leaf B, `leaf_shift_minor_dq5`, from `Theorem2`;
* `large_value_shift_of_lemma4`: the DQ5 leaf A, `leaf_large_value_shift_dq5`, from
  `Lemma4` and the two LEAF statements below;
* `lemma9_of_theorem2_lemma4`: the exact type `Lemma9` from `Theorem2` and `Lemma4`;
* `leaf_inv_sq_tail_l9`, the tail bound for the sum of `1/h^2`.

The two LEAF statements of classical Fourier analysis for the explicit trapezoid
`trapL9`, display 40 page 370, are proved below: the decay of its Fourier
coefficients and the pointwise convergence of its Fourier series. `PhiDQ5` of
DQ5Decisions is written out here as its defining sum, so the leaf A and leaf B types
match DQ5 up to unfolding that definition.

QUESTION, page 370: the printed `ψ(α) = Σ_k w_e(k - 2α)` has period 1/2, so it cannot
vanish on `[1/2, 1]` as printed. The intended function is `Σ_k w_e(2k - 2α)`, which is
the trapezoid `trapL9`. The paper's closing "contrary to the
hypothesis" also needs explicit constants; the proof below takes `Δ = (9/5) ℰ^{-1/3}`
and the sharp decay `|c_h| ≤ 4/(π² Δ h²)`, with total error at most `0.94 N ℰ^{-1/3}`.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539
import LeanLab.ExceptionalSet.Decomp547a

namespace LeanLab.ExceptionalSet.DQLemma9

open Real Finset Filter
open scoped Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539

/-! ### Small helpers -/

theorem calE_rpow_l9 (γ κ : ℝ) (N : ℕ) (r : ℝ) :
    calE γ κ N ^ r = Real.exp (κ * Real.log N ^ (3 - 2 * γ) * r) := by
  rw [calE, ← Real.exp_mul]

theorem eC_add_l9 (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_phi_le_l9 (γ : ℝ) (N : ℕ) (β : ℝ) :
    ‖∑ n ∈ Ioc (N / 2) N, eC (β * F γ n)‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Ioc (N / 2) N, ‖eC (β * F γ n)‖ := norm_sum_le _ _
    _ = ((N - N / 2 : ℕ) : ℝ) := by simp [norm_eC, Nat.card_Ioc]
    _ ≤ _ := by exact_mod_cast (show N - N / 2 ≤ N by omega)

theorem tendsto_L_l9 (γ : ℝ) (hγ2 : γ < 3 / 2) :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (3 - 2 * γ)) atTop atTop :=
  (tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem tendsto_logpow_l9 (p : ℝ) (hp : 0 < p) :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ p) atTop atTop :=
  (tendsto_rpow_atTop hp).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-! ### Leaf B of DQ5 from Theorem 2, page 370 last paragraph -/

set_option maxHeartbeats 1000000 in
/-- DQ5 leaf B, `leaf_shift_minor_dq5`, P0082 page 370 last paragraph: Theorem 2 on the
shifted window. CONDITIONAL ON `Theorem2`, nothing else open. -/
theorem shift_minor_of_theorem2 (hT : Theorem2) :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ δ : ℝ, 0 < δ → δ < γ - 1 →
      ∃ κ₁ : ℝ, 0 < κ₁ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₁ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ β : ℝ, F γ N ^ (δ - 1) < |β| → |β| ≤ 2 * F γ N ^ δ + 2 →
          ‖∑ n ∈ Ioc (N / 2) N, eC (β * F γ n)‖ ≤ N * calE γ κ N ^ (-(1 : ℝ)) := by
  intro γ hγ1 hγ2 δ hδ hδγ
  set C := (δ + (γ - 1)) / 2 with hCdef
  have hC : 0 < C := by rw [hCdef]; linarith
  have hCγ : C < γ - 1 := by rw [hCdef]; linarith
  have hδC : δ < C := by rw [hCdef]; linarith
  obtain ⟨η, A, hη, hsum⟩ := hT γ hγ1 hγ2 (1 - δ) C (by linarith) (by linarith) hC hCγ
  have hp0 : 0 < 3 - 2 * γ := by linarith
  have hp1 : 3 - 2 * γ < 1 := by linarith
  refine ⟨η / 4, by positivity, fun κ hκ hκη => ?_⟩
  -- eventual conditions
  set ε := (C - δ) / (2 * C) with hεdef
  have hε : 0 < ε := by rw [hεdef]; apply div_pos <;> linarith
  have hεC : C * (1 - ε) = (C + δ) / 2 := by rw [hεdef]; field_simp; ring
  obtain ⟨Nb, hNb⟩ := Decomp547a.upper_half_power_lower γ ε (by linarith) hε
  obtain ⟨Nc, hNc⟩ := eventually_atTop.mp ((tendsto_logpow_l9 γ (by linarith)).eventually_ge_atTop
    (Real.log 4 / ((C - δ) / 2)))
  have hLt := tendsto_L_l9 γ hγ2
  obtain ⟨Nd, hNd⟩ := eventually_atTop.mp (hLt.eventually_ge_atTop
    (Real.log (2 * |A| + 1) / (η / 4)))
  have hratio : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (1 - (3 - 2 * γ))) atTop atTop :=
    tendsto_logpow_l9 _ (by linarith)
  obtain ⟨Ne, hNe⟩ := eventually_atTop.mp (hratio.eventually_ge_atTop (η / 2))
  refine ⟨max 16 (max Nb (max Nc (max Nd Ne))), fun N hN β hβlo hβhi => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNb' := hNb N (((le_max_left _ _).trans (le_max_right _ _)).trans hN)
  have hNc' := hNc N ((((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans hN)
  have hNd' := hNd N (((((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)).trans hN)
  have hNe' := hNe N (((((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)).trans hN)
  set M := (N + 1) / 2 with hMdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hL : 0 ≤ Real.log (N : ℝ) := hlogpos.le
  set L := Real.log (N : ℝ) ^ (3 - 2 * γ) with hLdef
  have hLnn : 0 ≤ L := Real.rpow_nonneg hL _
  obtain ⟨hmL, hlog⟩ := Decomp547a.upper_half_log N hN16
  -- frequency range
  have hXδ : 1 ≤ F γ N ^ δ := by
    rw [F, ← Real.exp_mul]
    exact Real.one_le_exp (mul_nonneg (Real.rpow_nonneg hL _) hδ.le)
  have hupper : |β| ≤ F γ M ^ C := by
    have h4 : |β| ≤ 4 * F γ N ^ δ := by linarith
    have hrw : 4 * F γ N ^ δ = Real.exp (Real.log 4 + Real.log (N : ℝ) ^ γ * δ) := by
      rw [Real.exp_add, Real.exp_log (by norm_num), F, ← Real.exp_mul]
    have hrw2 : F γ M ^ C = Real.exp (Real.log (M : ℝ) ^ γ * C) := by
      rw [F, ← Real.exp_mul]
    rw [hrw2]
    refine h4.trans (hrw ▸ Real.exp_le_exp.mpr ?_)
    have hc1 : Real.log 4 ≤ (C - δ) / 2 * Real.log (N : ℝ) ^ γ := by
      have := (div_le_iff₀ (by linarith : (0 : ℝ) < (C - δ) / 2)).mp hNc'
      linarith
    have hc2 := mul_le_mul_of_nonneg_left hNb' hC.le
    rw [← mul_assoc, hεC] at hc2
    nlinarith
  have hlower : F γ (2 * (M : ℕ)) ^ (-(1 - δ)) ≤ |β| := by
    refine le_trans ?_ hβlo.le
    have hdouble : (N : ℝ) ≤ 2 * (M : ℕ) := by
      exact_mod_cast (show N ≤ 2 * ((N + 1) / 2) by omega)
    have hpow : Real.log (N : ℝ) ^ γ ≤ Real.log (2 * (M : ℕ) : ℝ) ^ γ :=
      Real.rpow_le_rpow hL (Real.log_le_log hNpos hdouble) (by linarith)
    simp only [F, ← Real.exp_mul]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hraw := hsum M (by omega) β hlower hupper
  -- compare log M with log N
  have hpow : L ≤ 2 * Real.log (M : ℝ) ^ (3 - 2 * γ) := by
    calc
      L ≤ (2 * Real.log (M : ℝ)) ^ (3 - 2 * γ) := Real.rpow_le_rpow hL hlog hp0.le
      _ = (2 : ℝ) ^ (3 - 2 * γ) * Real.log (M : ℝ) ^ (3 - 2 * γ) :=
        Real.mul_rpow (by norm_num) hmL.le
      _ ≤ 2 * Real.log (M : ℝ) ^ (3 - 2 * γ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hmL.le _)
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp1.le
  have hdecay : Real.exp (-η * Real.log (M : ℝ) ^ (3 - 2 * γ)) ≤
      Real.exp (-(η / 2) * L) := Real.exp_le_exp.mpr (by nlinarith)
  have hMN : (M : ℝ) ≤ N := by exact_mod_cast (show (N + 1) / 2 ≤ N by omega)
  have hexp1 : ‖expSumF γ β M‖ ≤ |A| * N * Real.exp (-(η / 2) * L) := by
    refine hraw.trans ?_
    have hA : A ≤ |A| := le_abs_self A
    have hMnn : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    calc A * M * Real.exp (-η * Real.log (M : ℝ) ^ (3 - 2 * γ))
        ≤ |A| * M * Real.exp (-η * Real.log (M : ℝ) ^ (3 - 2 * γ)) := by gcongr
      _ ≤ |A| * N * Real.exp (-(η / 2) * L) := by gcongr
  have hend := Decomp547a.upper_half_sum_norm_le γ β N
  -- the two small terms
  have hd : |A| * Real.exp (-(η / 4) * L) ≤ 1 / 2 := by
    have hlogle : Real.log (2 * |A| + 1) ≤ η / 4 * L := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < η / 4)).mp hNd'
      linarith
    have he : 2 * |A| + 1 ≤ Real.exp (η / 4 * L) := by
      calc 2 * |A| + 1 = Real.exp (Real.log (2 * |A| + 1)) :=
            (Real.exp_log (by positivity)).symm
        _ ≤ _ := Real.exp_le_exp.mpr hlogle
    have hpos := Real.exp_pos (-(η / 4) * L)
    have hprod : Real.exp (η / 4 * L) * Real.exp (-(η / 4) * L) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [abs_nonneg A]
  have he' : 1 ≤ N * Real.exp (-(η / 4) * L) / 2 := by
    -- (η/4) L ≤ log N - log 2
    have hscale : η / 2 * L ≤ Real.log (N : ℝ) := by
      have he : (3 - 2 * γ) + (1 - (3 - 2 * γ)) = 1 := by ring
      calc η / 2 * L = L * (η / 2) := by ring
        _ ≤ L * Real.log (N : ℝ) ^ (1 - (3 - 2 * γ)) := mul_le_mul_of_nonneg_left hNe' hLnn
        _ = Real.log (N : ℝ) := by rw [hLdef, ← Real.rpow_add hlogpos, he, Real.rpow_one]
    have hlog4 : Real.log 4 ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 4 ≤ N))
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have hlog2 : η / 4 * L + Real.log 2 ≤ Real.log (N : ℝ) := by linarith
    have hE : Real.exp (η / 4 * L) * 2 ≤ N := by
      calc Real.exp (η / 4 * L) * 2 = Real.exp (η / 4 * L + Real.log 2) := by
            rw [Real.exp_add, Real.exp_log (by norm_num)]
        _ ≤ Real.exp (Real.log (N : ℝ)) := Real.exp_le_exp.mpr hlog2
        _ = N := Real.exp_log hNpos
    have hprod : Real.exp (η / 4 * L) * Real.exp (-(η / 4) * L) = 1 := by
      rw [← Real.exp_add]; simp
    have hq := Real.exp_pos (-(η / 4) * L)
    have h2 : 2 ≤ N * Real.exp (-(η / 4) * L) :=
      calc (2 : ℝ) = Real.exp (η / 4 * L) * 2 * Real.exp (-(η / 4) * L) := by
            rw [mul_right_comm, hprod]; ring
        _ ≤ N * Real.exp (-(η / 4) * L) := mul_le_mul_of_nonneg_right hE hq.le
    linarith
  have hmain : ‖∑ n ∈ Ioc (N / 2) N, eC (β * F γ n)‖ ≤ N * Real.exp (-(η / 4) * L) := by
    have hq := Real.exp_pos (-(η / 4) * L)
    have hsplit : Real.exp (-(η / 2) * L) =
        Real.exp (-(η / 4) * L) * Real.exp (-(η / 4) * L) := by
      rw [← Real.exp_add]; ring_nf
    have h1 : |A| * N * Real.exp (-(η / 2) * L) ≤ N * Real.exp (-(η / 4) * L) / 2 := by
      rw [hsplit]
      calc |A| * N * (Real.exp (-(η / 4) * L) * Real.exp (-(η / 4) * L))
          = (N * Real.exp (-(η / 4) * L)) * (|A| * Real.exp (-(η / 4) * L)) := by ring
        _ ≤ (N * Real.exp (-(η / 4) * L)) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hd (mul_nonneg hNpos.le hq.le)
        _ = N * Real.exp (-(η / 4) * L) / 2 := by ring
    linarith
  refine hmain.trans ?_
  rw [calE_rpow_l9]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hNpos.le
  have := mul_le_mul_of_nonneg_right hκη hLnn
  rw [← hLdef]
  linarith

/-! ### The two open leaves, page 370 -/

/-- The smoothed parity cutoff of P0082 page 370, `ψ(α) = Σ_k w_e(2k - 2α)` with `w_e` of
display 31 page 367, read with the page 370 misprint fixed, see the header QUESTION:
the 1-periodic trapezoid in `t = {α}` that rises on `[0, Δ/4]`, is 1 on `[Δ/4, 1/2 - Δ/4]`,
falls on `[1/2 - Δ/4, 1/2]` and is 0 on `[1/2, 1)`. -/
noncomputable def trapL9 (Δ β : ℝ) : ℝ :=
  max 0 (min 1 (min (4 * Int.fract β / Δ) (4 * (1 / 2 - Int.fract β) / Δ)))

/-! Proved helpers for the coefficient leaf below, AI written, run CLOUD-burst20261120b-lemma9_fourier. -/

theorem trapL9_profile_zero_one (Δ : ℝ) (hΔ0 : 0 < Δ) :
    max 0 (min 1 (min (4 * (0 : ℝ) / Δ) (4 * (1 / 2 - 0) / Δ))) =
      max 0 (min 1 (min (4 * (1 : ℝ) / Δ) (4 * (1 / 2 - 1) / Δ))) := by
  rw [max_eq_left, max_eq_left]
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hΔ0.le))
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans (by simp))

theorem trapL9_continuous (Δ : ℝ) (hΔ0 : 0 < Δ) : Continuous (fun β => trapL9 Δ β) := by
  have hg : Continuous (fun x : ℝ => max 0 (min 1 (min (4 * x / Δ) (4 * (1 / 2 - x) / Δ)))) := by
    fun_prop
  exact (hg.continuousOn (s := Set.Icc 0 1)).comp_fract'' (trapL9_profile_zero_one Δ hΔ0)

theorem trapL9_eq_profile (Δ : ℝ) (hΔ0 : 0 < Δ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    trapL9 Δ t = max 0 (min 1 (min (4 * t / Δ) (4 * (1 / 2 - t) / Δ))) := by
  rcases h1.lt_or_eq with h1 | rfl
  · unfold trapL9; rw [Int.fract_eq_self.2 ⟨h0, h1⟩]
  · unfold trapL9; rw [Int.fract_one]; exact trapL9_profile_zero_one Δ hΔ0

theorem trapL9_piece1 (d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1 / 4) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ d) :
    trapL9 (4 * d) t = 1 / d * t + 0 := by
  have h4 : 0 < 4 * d := by linarith
  rw [trapL9_eq_profile _ h4 h0 (by linarith)]
  have e : 4 * t / (4 * d) = 1 / d * t := by field_simp
  have a1 : 4 * t / (4 * d) ≤ 4 * (1 / 2 - t) / (4 * d) :=
    div_le_div_of_nonneg_right (by linarith) h4.le
  have a2 : 4 * t / (4 * d) ≤ 1 := (div_le_one h4).2 (by linarith)
  have a3 : 0 ≤ 4 * t / (4 * d) := div_nonneg (by linarith) h4.le
  rw [min_eq_left a1, min_eq_right a2, max_eq_right a3, e, add_zero]

theorem trapL9_piece2 (d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1 / 4) {t : ℝ} (h0 : d ≤ t)
    (h1 : t ≤ 1 / 2 - d) : trapL9 (4 * d) t = 0 * t + 1 := by
  have h4 : 0 < 4 * d := by linarith
  rw [trapL9_eq_profile _ h4 (by linarith) (by linarith)]
  have a1 : 1 ≤ 4 * t / (4 * d) := (le_div_iff₀ h4).2 (by linarith)
  have a2 : 1 ≤ 4 * (1 / 2 - t) / (4 * d) := (le_div_iff₀ h4).2 (by linarith)
  rw [min_eq_left (le_min a1 a2), max_eq_right zero_le_one]; ring

theorem trapL9_piece3 (d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1 / 4) {t : ℝ} (h0 : 1 / 2 - d ≤ t)
    (h1 : t ≤ 1 / 2) : trapL9 (4 * d) t = -(1 / d) * t + 1 / (2 * d) := by
  have h4 : 0 < 4 * d := by linarith
  rw [trapL9_eq_profile _ h4 (by linarith) (by linarith)]
  have e : 4 * (1 / 2 - t) / (4 * d) = -(1 / d) * t + 1 / (2 * d) := by field_simp; ring
  have a1 : 4 * (1 / 2 - t) / (4 * d) ≤ 4 * t / (4 * d) :=
    div_le_div_of_nonneg_right (by linarith) h4.le
  have a2 : 4 * (1 / 2 - t) / (4 * d) ≤ 1 := (div_le_one h4).2 (by linarith)
  have a3 : 0 ≤ 4 * (1 / 2 - t) / (4 * d) := div_nonneg (by linarith) h4.le
  rw [min_eq_right a1, min_eq_right a2, max_eq_right a3, e]

theorem trapL9_piece4 (d : ℝ) (hd0 : 0 < d) {t : ℝ} (h0 : 1 / 2 ≤ t) (h1 : t ≤ 1) :
    trapL9 (4 * d) t = 0 * t + 0 := by
  have h4 : 0 < 4 * d := by linarith
  rw [trapL9_eq_profile _ h4 (by linarith) h1]
  have a : 4 * (1 / 2 - t) / (4 * d) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) h4.le
  rw [max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans a))]; ring

theorem integral_lin_exp_l9 (a : ℂ) (ha : a ≠ 0) (p q x y : ℝ) :
    ∫ t in x..y, ((p : ℂ) * t + q) * Complex.exp (a * t) =
      Complex.exp (a * y) * (((p : ℂ) * y + q) / a - p / a ^ 2) -
        Complex.exp (a * x) * (((p : ℂ) * x + q) / a - p / a ^ 2) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s _
    have hl : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by
      simpa using (hasDerivAt_id s).ofReal_comp
    have he : HasDerivAt (fun s : ℝ => Complex.exp (a * s)) (Complex.exp (a * s) * (a * 1)) s :=
      (hl.const_mul a).cexp
    have hp : HasDerivAt (fun s : ℝ => ((p : ℂ) * s + q) / a - p / a ^ 2) (p * 1 / a) s :=
      (((hl.const_mul (p : ℂ)).add_const (q : ℂ)).div_const a).sub_const _
    convert he.mul hp using 1
    field_simp
    ring
  · apply Continuous.intervalIntegrable
    fun_prop


theorem hcheck_trapL9_eq (d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1 / 4) (h : ℤ) (hh : h ≠ 0) :
    hcheck (fun t => (trapL9 (4 * d) t : ℂ)) h =
      1 / ((d : ℂ) * (-(2 * π * Complex.I * h)) ^ 2) *
        (1 - Complex.exp (-(2 * π * Complex.I * h) * d) -
          Complex.exp (-(2 * π * Complex.I * h) * (1 / 2 - d)) +
          Complex.exp (-(2 * π * Complex.I * h) * (1 / 2))) := by
  set a : ℂ := -(2 * π * Complex.I * h) with ha_def
  have ha : a ≠ 0 := by
    rw [ha_def, neg_ne_zero]
    simp [Real.pi_ne_zero, Complex.I_ne_zero, hh]
  have h4 : 0 < 4 * d := by linarith
  have hc : Continuous (fun t : ℝ => (trapL9 (4 * d) t : ℂ) * Complex.exp (a * t)) :=
    (Complex.continuous_ofReal.comp (trapL9_continuous _ h4)).mul (by fun_prop)
  have hii : ∀ x y : ℝ, IntervalIntegrable
      (fun t : ℝ => (trapL9 (4 * d) t : ℂ) * Complex.exp (a * t)) MeasureTheory.volume x y :=
    fun x y => hc.intervalIntegrable x y
  have hI : hcheck (fun t => (trapL9 (4 * d) t : ℂ)) h =
      ∫ t in (0 : ℝ)..1, (trapL9 (4 * d) t : ℂ) * Complex.exp (a * t) := by
    unfold hcheck
    apply intervalIntegral.integral_congr
    intro t _
    simp only [eC, ha_def]
    congr 2
    push_cast
    ring
  have piece : ∀ (x y p q : ℝ), x ≤ y → (∀ t, x ≤ t → t ≤ y → trapL9 (4 * d) t = p * t + q) →
      ∫ t in x..y, (trapL9 (4 * d) t : ℂ) * Complex.exp (a * t) =
        Complex.exp (a * y) * (((p : ℂ) * y + q) / a - p / a ^ 2) -
          Complex.exp (a * x) * (((p : ℂ) * x + q) / a - p / a ^ 2) := by
    intro x y p q hxy hpq
    rw [← integral_lin_exp_l9 a ha p q x y]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    simp only
    rw [hpq t ht.1 ht.2]
    push_cast
    ring
  rw [hI, ← intervalIntegral.integral_add_adjacent_intervals (hii 0 d) (hii d 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hii d (1 / 2 - d)) (hii (1 / 2 - d) 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hii (1 / 2 - d) (1 / 2)) (hii (1 / 2) 1),
    piece 0 d (1 / d) 0 hd0.le (fun t h0 h1 => trapL9_piece1 d hd0 hd1 h0 h1),
    piece d (1 / 2 - d) 0 1 (by linarith) (fun t h0 h1 => trapL9_piece2 d hd0 hd1 h0 h1),
    piece (1 / 2 - d) (1 / 2) (-(1 / d)) (1 / (2 * d)) (by linarith)
      (fun t h0 h1 => trapL9_piece3 d hd0 hd1 h0 h1),
    piece (1 / 2) 1 0 0 (by norm_num) (fun t h0 h1 => trapL9_piece4 d hd0 h0 h1)]
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  push_cast
  field_simp
  simp only [mul_zero, Complex.exp_zero]
  ring


theorem norm_exp_l9 (h : ℤ) (x : ℝ) : ‖Complex.exp (-(2 * π * Complex.I * h) * x)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem hcheck_trapL9_le_half (d : ℝ) (hd0 : 0 < d) (h : ℤ) :
    ‖hcheck (fun t => (trapL9 (4 * d) t : ℂ)) h‖ ≤ 1 / 2 := by
  have h4 : 0 < 4 * d := by linarith
  have hc : Continuous (fun t : ℝ => (trapL9 (4 * d) t : ℂ) * eC (-(t * h))) :=
    (Complex.continuous_ofReal.comp (trapL9_continuous _ h4)).mul (by unfold eC; fun_prop)
  unfold hcheck
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (1 / 2))
    (hc.intervalIntegrable (1 / 2) 1)]
  have h2 : ∫ t in (1 / 2 : ℝ)..1, (trapL9 (4 * d) t : ℂ) * eC (-(t * h)) = 0 := by
    rw [← intervalIntegral.integral_zero (a := (1 / 2 : ℝ)) (b := 1) (μ := MeasureTheory.volume)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    simp only
    rw [trapL9_piece4 d hd0 ht.1 ht.2]
    simp
  rw [h2, add_zero]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1 / 2)
    (C := 1) (f := fun t : ℝ => (trapL9 (4 * d) t : ℂ) * eC (-(t * h))) (fun t _ => by
      rw [norm_mul, norm_eC, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_max_left _ _)]
      exact max_le zero_le_one (min_le_left _ _))
  refine hb.trans (le_of_eq ?_)
  norm_num

/-- LEAF: P0082 page 370 display 40. The Fourier coefficients `c_h = ∫_0^1 ψ(t) e(-ht) dt`
of the trapezoid `ψ = trapL9 Δ` satisfy `|c_h| ≤ 1/2` and, for `h ≠ 0`,
`|c_h| ≤ 4/(π² Δ h²) ≤ 41/(100 Δ h²)`. The paper derives the decay "by the Poisson summation
formula, (4) and `|K_e(α)| ≤ ½|K(α/2)|`"; directly, `ψ` is the convolution of the indicator
of an interval of length `1/2 - Δ/4` with the normalized indicator of `[0, Δ/4]`, so
`|c_h| ≤ |sin(π h Δ/4)| / (π² h² Δ/4)`. No cited input. -/
theorem leaf_trapezoid_coeff_l9 (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (h : ℤ) :
    ‖hcheck (fun t => (trapL9 Δ t : ℂ)) h‖ ≤ 1 / 2 ∧
      (h ≠ 0 → ‖hcheck (fun t => (trapL9 Δ t : ℂ)) h‖ ≤ 41 / 100 / (Δ * (h : ℝ) ^ 2)) := by
  obtain ⟨d, rfl⟩ : ∃ d, Δ = 4 * d := ⟨Δ / 4, by ring⟩
  have hd0 : 0 < d := by linarith
  have hd1 : d ≤ 1 / 4 := by linarith
  refine ⟨hcheck_trapL9_le_half d hd0 h, fun hh => ?_⟩
  rw [hcheck_trapL9_eq d hd0 hd1 h hh]
  have e1 := norm_exp_l9 h d
  have e2 := norm_exp_l9 h (1 / 2 - d)
  have e3 := norm_exp_l9 h (1 / 2)
  push_cast at e2 e3
  have hS : ‖1 - Complex.exp (-(2 * π * Complex.I * h) * d) -
          Complex.exp (-(2 * π * Complex.I * h) * (1 / 2 - d)) +
          Complex.exp (-(2 * π * Complex.I * h) * (1 / 2))‖ ≤ 4 := by
    have t1 := norm_add_le (1 - Complex.exp (-(2 * π * Complex.I * h) * d) -
      Complex.exp (-(2 * π * Complex.I * h) * (1 / 2 - d)))
      (Complex.exp (-(2 * π * Complex.I * h) * (1 / 2)))
    have t2 := norm_sub_le (1 - Complex.exp (-(2 * π * Complex.I * h) * d))
      (Complex.exp (-(2 * π * Complex.I * h) * (1 / 2 - d)))
    have t3 := norm_sub_le (1 : ℂ) (Complex.exp (-(2 * π * Complex.I * h) * d))
    rw [norm_one] at t3
    linarith
  have hh2 : (0 : ℝ) < (h : ℝ) ^ 2 := by positivity
  have hpi : (3.14 : ℝ) < π := Real.pi_gt_d2
  have hN : ‖1 / ((d : ℂ) * (-(2 * π * Complex.I * h)) ^ 2)‖ = 1 / (d * (4 * π ^ 2 * (h : ℝ) ^ 2)) := by
    rw [norm_div, norm_one, norm_mul, norm_pow, norm_neg]
    simp [Complex.norm_real, abs_of_pos hd0, abs_of_pos Real.pi_pos, mul_pow]
    norm_num
  rw [norm_mul, hN]
  have hD : 0 < d * (4 * π ^ 2 * (h : ℝ) ^ 2) := by positivity
  calc 1 / (d * (4 * π ^ 2 * (h : ℝ) ^ 2)) * ‖_‖ ≤ 1 / (d * (4 * π ^ 2 * (h : ℝ) ^ 2)) * 4 :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ 41 / 100 / (4 * d * (h : ℝ) ^ 2) := by
        rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hD (by positivity)]
        have : (9.8 : ℝ) < π ^ 2 := by nlinarith
        nlinarith [mul_pos hd0 hh2]

theorem trapL9_periodic (Δ : ℝ) : Function.Periodic (fun t : ℝ => (trapL9 Δ t : ℂ)) 1 := by
  intro t
  simp only [trapL9, Int.fract_add_one]

/-- LEAF: P0082 page 370, the expansion `ψ(α) = Σ_h c_h e(hα)` written below display 39.
`trapL9 Δ` is continuous and 1-periodic and its coefficients are absolutely summable by
`leaf_trapezoid_coeff_l9`, so its Fourier series converges to it at every point, as in
Mathlib's `hasSum_fourier_series_of_summable`. No cited input. -/
theorem leaf_trapezoid_series_l9 (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (β : ℝ) :
    HasSum (fun h : ℤ => hcheck (fun t => (trapL9 Δ t : ℂ)) h * eC (h * β))
      (trapL9 Δ β : ℂ) := by
  let F : C(UnitAddCircle, ℂ) :=
    ⟨(trapL9_periodic Δ).lift, continuous_coinduced_dom.mpr
      (Complex.continuous_ofReal.comp (trapL9_continuous Δ hΔ0))⟩
  have hcoef : ∀ n : ℤ, fourierCoeff F n = hcheck (fun t => (trapL9 Δ t : ℂ)) n := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add, one_div_one, one_smul]
    unfold hcheck
    apply intervalIntegral.integral_congr
    intro t _
    simp only [F, ContinuousMap.coe_mk, Function.Periodic.lift_coe, fourier_coe_apply, smul_eq_mul,
      eC]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hsum : Summable (fourierCoeff F) := by
    rw [show fourierCoeff F = fun n => hcheck (fun t => (trapL9 Δ t : ℂ)) n from funext hcoef]
    refine Summable.of_norm_bounded_eventually (g := fun n : ℤ => 41 / 100 / Δ * (1 / (n : ℝ) ^ 2))
      ((Real.summable_one_div_int_pow.mpr one_lt_two).mul_left _) ?_
    have : {(0 : ℤ)}ᶜ ∈ Filter.cofinite := (Set.finite_singleton 0).compl_mem_cofinite
    filter_upwards [this] with n hn
    refine ((leaf_trapezoid_coeff_l9 Δ hΔ0 hΔ1 n).2 hn).trans (le_of_eq ?_)
    field_simp
  have := has_pointwise_sum_fourier_series_of_summable hsum (β : UnitAddCircle)
  convert this using 1
  · funext n
    rw [hcoef, smul_eq_mul, fourier_coe_apply]
    congr 1
    unfold eC
    congr 1
    push_cast
    ring
  · simp [F, Function.Periodic.lift_coe]

/-- P0082 page 370 display 40 and the expansion above it, in the form used below:
the smoothed parity cutoff, its shape, its Fourier series and the decay of its
coefficients. Proved from the two LEAF lemmas above; the shape is checked here. -/
theorem leaf_trapezoid_fourier_l9 (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∃ (ψ : ℝ → ℝ) (c : ℤ → ℂ),
      (∀ β : ℝ, 0 ≤ ψ β ∧ ψ β ≤ 1) ∧
      (∀ β : ℝ, 1 / 2 ≤ Int.fract β → ψ β = 0) ∧
      (∀ β : ℝ, Δ / 4 ≤ Int.fract β → Int.fract β ≤ 1 / 2 - Δ / 4 → ψ β = 1) ∧
      (∀ β : ℝ, HasSum (fun h : ℤ => c h * eC (h * β)) (ψ β : ℂ)) ∧
      (∀ h : ℤ, ‖c h‖ ≤ 1 / 2) ∧
      (∀ h : ℤ, h ≠ 0 → ‖c h‖ ≤ 41 / 100 / (Δ * (h : ℝ) ^ 2)) := by
  refine ⟨trapL9 Δ, hcheck (fun t => (trapL9 Δ t : ℂ)), fun β => ?_, fun β hβ => ?_,
    fun β h1 h2 => ?_, leaf_trapezoid_series_l9 Δ hΔ0 hΔ1,
    fun h => (leaf_trapezoid_coeff_l9 Δ hΔ0 hΔ1 h).1,
    fun h => (leaf_trapezoid_coeff_l9 Δ hΔ0 hΔ1 h).2⟩
  · exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  · have h1 : 4 * (1 / 2 - Int.fract β) / Δ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hΔ0.le
    unfold trapL9
    apply max_eq_left
    exact (min_le_right _ _).trans ((min_le_right _ _).trans h1)
  · unfold trapL9
    have ha : 1 ≤ 4 * Int.fract β / Δ := by rw [le_div_iff₀ hΔ0]; linarith
    have hb : 1 ≤ 4 * (1 / 2 - Int.fract β) / Δ := by rw [le_div_iff₀ hΔ0]; linarith
    rw [min_eq_left (le_min ha hb), max_eq_right zero_le_one]

theorem inv_sq_telescope_l9 (m : ℝ) (hm : 1 ≤ m) :
    1 / m ^ 2 ≤ 1 / (m - 1 / 2) - 1 / (m + 1 / 2) := by
  have h1 : 0 < m - 1 / 2 := by linarith
  have h2 : 0 < m + 1 / 2 := by linarith
  have h3 : 0 < m ^ 2 := by positivity
  rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ h3 (mul_pos h1 h2)]
  nlinarith

theorem partial_inv_sq_aux_l9 (K : ℕ) :
    ∀ m : ℕ, K + 1 ≤ m →
      ∑ n ∈ Finset.range m, (if K < n then 1 / (n : ℝ) ^ 2 else 0) ≤
        1 / ((K : ℝ) + 1 / 2) - 1 / ((m : ℝ) - 1 / 2) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero (fun n hn => by
      rw [Finset.mem_range] at hn; rw [if_neg (by omega)])]
    push_cast
    have : (K : ℝ) + 1 - 1 / 2 = K + 1 / 2 := by ring
    rw [this, sub_self]
  | succ m hm ih =>
    rw [Finset.sum_range_succ, if_pos (by omega)]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have ht := inv_sq_telescope_l9 (m : ℝ) hm1
    push_cast
    have : (m : ℝ) + 1 - 1 / 2 = m + 1 / 2 := by ring
    rw [this]
    linarith

theorem partial_inv_sq_l9 (K m : ℕ) :
    ∑ n ∈ Finset.range m, (if K < n then 1 / (n : ℝ) ^ 2 else 0) ≤ 1 / ((K : ℝ) + 1 / 2) := by
  by_cases hm : K + 1 ≤ m
  · have h := partial_inv_sq_aux_l9 K m hm
    have hpos : 0 ≤ 1 / ((m : ℝ) - 1 / 2) := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      apply div_nonneg zero_le_one; linarith
    linarith
  · rw [Finset.sum_eq_zero (fun n hn => by
      rw [Finset.mem_range] at hn; rw [if_neg (by omega)])]
    positivity

theorem tail_of_nat_l9 (f : ℤ → ℝ) (a : ℕ → ℝ) (B : ℝ) (ha0 : ∀ n, 0 ≤ a n)
    (hpart : ∀ m, ∑ n ∈ Finset.range m, a n ≤ B) (h0 : a 0 = 0)
    (hf1 : ∀ n : ℕ, f n = a n) (hf2 : ∀ n : ℕ, f (-(n + 1)) = a (n + 1)) :
    Summable f ∧ ∑' h, f h ≤ 2 * B := by
  have hA : Summable a := summable_of_sum_range_le ha0 hpart
  have hAle : ∑' n, a n ≤ B := Real.tsum_le_of_sum_range_le ha0 hpart
  have hA1 : Summable (fun n : ℕ => a (n + 1)) := (summable_nat_add_iff 1).mpr hA
  have hA1le : ∑' n, a (n + 1) ≤ B := by
    refine Real.tsum_le_of_sum_range_le (fun n => ha0 _) (fun m => ?_)
    have h := hpart (m + 1)
    rw [Finset.sum_range_succ', h0, add_zero] at h
    exact h
  have e1 : (fun n : ℕ => f n) = a := funext hf1
  have e2 : (fun n : ℕ => f (-(n + 1))) = fun n => a (n + 1) := funext hf2
  have hs := HasSum.of_nat_of_neg_add_one (f := f) (e1 ▸ hA.hasSum) (e2 ▸ hA1.hasSum)
  refine ⟨hs.summable, ?_⟩
  rw [hs.tsum_eq]
  simp only [hf1, hf2]
  linarith

/-- P0082 page 370, the removal of the terms with `|h| > ℰ^{2/3}` "by (40)", in the
elementary form `Σ_{|h| > K} h^{-2} ≤ 2/(K + 1/2)`, from `h^{-2} ≤ 1/(h - 1/2) - 1/(h + 1/2)`.
No cited input. Proved here, it was planned as a LEAF. -/
theorem leaf_inv_sq_tail_l9 (K : ℕ) :
    Summable (fun h : ℤ => if (K : ℤ) < |h| then 1 / (h : ℝ) ^ 2 else 0) ∧
      ∑' h : ℤ, (if (K : ℤ) < |h| then 1 / (h : ℝ) ^ 2 else 0) ≤ 2 / ((K : ℝ) + 1 / 2) := by
  have h := tail_of_nat_l9 (fun h : ℤ => if (K : ℤ) < |h| then 1 / (h : ℝ) ^ 2 else 0)
    (fun n : ℕ => if K < n then 1 / (n : ℝ) ^ 2 else 0) (1 / ((K : ℝ) + 1 / 2))
    (fun n => by split_ifs <;> positivity) (partial_inv_sq_l9 K) (by simp)
    (fun n => by
      have : |(n : ℤ)| = n := abs_of_nonneg (by positivity)
      rw [this]; simp only [Nat.cast_lt, Int.cast_natCast])
    (fun n => by
      have : |(-((n : ℤ) + 1))| = ((n + 1 : ℕ) : ℤ) := by
        rw [abs_neg, abs_of_nonneg (by positivity)]; push_cast; rfl
      rw [this]; simp only [Nat.cast_lt]
      split_ifs <;> push_cast <;> ring)
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  ring

/-! ### Display 41 for one `N`, no asymptotics -/

theorem even_floor_iff_l9 (y : ℝ) : Even ⌊y⌋ ↔ Int.fract (1 / 2 * y) < 1 / 2 := by
  set m := ⌊1 / 2 * y⌋ with hm
  set t := Int.fract (1 / 2 * y) with ht
  have hy : y = 2 * m + 2 * t := by
    rw [hm, ht, Int.fract]; ring
  have ht0 : 0 ≤ t := Int.fract_nonneg _
  have ht1 : t < 1 := Int.fract_lt_one _
  constructor
  · intro he
    by_contra hlt
    push_neg at hlt
    have hfl : ⌊y⌋ = 2 * m + 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [hfl] at he
    exact (Int.not_even_iff_odd.mpr ⟨m, rfl⟩) he
  · intro hlt
    have hfl : ⌊y⌋ = 2 * m := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [hfl]
    exact ⟨m, by ring⟩

/-- The bad set of the smoothing step: `{F(n)/2}` in a ramp of `ψ`. -/
theorem smoothing_l9 (γ : ℝ) (N : ℕ) (α Δ : ℝ) (ψ : ℝ → ℝ)
    (hψ01 : ∀ β : ℝ, 0 ≤ ψ β ∧ ψ β ≤ 1)
    (hψ0 : ∀ β : ℝ, 1 / 2 ≤ Int.fract β → ψ β = 0)
    (hψ1 : ∀ β : ℝ, Δ / 4 ≤ Int.fract β → Int.fract β ≤ 1 / 2 - Δ / 4 → ψ β = 1) :
    ‖Phie γ N α - ∑ n ∈ Ioc (N / 2) N, (ψ (1 / 2 * F γ n) : ℂ) * eC (α * F γ n)‖ ≤
      (((Ioc (N / 2) N).filter (fun n : ℕ =>
        (0 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < Δ / 4) ∨
        (1 / 2 - Δ / 4 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < 1 / 2))).card
        : ℝ) := by
  classical
  have hPhie : Phie γ N α = ∑ n ∈ Ioc (N / 2) N,
      ((if Even (nu γ n) then (1 : ℝ) else 0 : ℝ) : ℂ) * eC (α * F γ n) := by
    rw [Phie, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    split_ifs <;> simp
  rw [hPhie, ← Finset.sum_sub_distrib, Finset.card_filter, Nat.cast_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
  rw [← sub_mul, norm_mul, norm_eC, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  set t := Int.fract (1 / 2 * F γ n) with ht
  have ht0 : 0 ≤ t := Int.fract_nonneg _
  have hev : Even (nu γ n) ↔ t < 1 / 2 := even_floor_iff_l9 (F γ n)
  obtain ⟨hp0, hp1⟩ := hψ01 (1 / 2 * F γ n)
  by_cases hbad : (0 ≤ t ∧ t < Δ / 4) ∨ (1 / 2 - Δ / 4 ≤ t ∧ t < 1 / 2)
  · rw [if_pos hbad]
    push_cast
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  · rw [if_neg hbad]
    push_neg at hbad
    push_cast
    by_cases hhalf : 1 / 2 ≤ t
    · have hne : ¬ Even (nu γ n) := fun h => by linarith [hev.mp h]
      rw [if_neg hne, hψ0 _ hhalf]; simp
    · push_neg at hhalf
      have hlo : Δ / 4 ≤ t := hbad.1 ht0
      have hle : t ≤ 1 / 2 - Δ / 4 := by
        by_contra h; push_neg at h; linarith [hbad.2 h.le]
      rw [if_pos (hev.mpr hhalf), hψ1 _ hlo hle]; simp

/-- Second line of display 41: the smoothed sum is `Σ_h c_h Φ(α + h/2)`. -/
theorem expansion_l9 (γ : ℝ) (N : ℕ) (α : ℝ) (ψ : ℝ → ℝ) (c : ℤ → ℂ)
    (hser : ∀ β : ℝ, HasSum (fun h : ℤ => c h * eC (h * β)) (ψ β : ℂ)) :
    HasSum (fun h : ℤ => c h * ∑ n ∈ Ioc (N / 2) N, eC ((α + h / 2) * F γ n))
      (∑ n ∈ Ioc (N / 2) N, (ψ (1 / 2 * F γ n) : ℂ) * eC (α * F γ n)) := by
  have hsum := hasSum_sum (s := Ioc (N / 2) N)
    (fun n _ => (hser (1 / 2 * F γ n)).mul_right (eC (α * F γ n)))
  convert hsum using 1
  funext h
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [mul_assoc, ← eC_add_l9]
  congr 2
  ring

/-- Display 41 truncated at `|h| ≤ K`, for one `N`, with the two leaves. -/
theorem truncated_l9 (γ : ℝ) (N : ℕ) (α Δ : ℝ) (hΔ0 : 0 < Δ) (c : ℤ → ℂ) (T : ℂ)
    (hT : HasSum (fun h : ℤ => c h * ∑ n ∈ Ioc (N / 2) N, eC ((α + h / 2) * F γ n)) T)
    (hc0 : ∀ h : ℤ, ‖c h‖ ≤ 1 / 2)
    (hc : ∀ h : ℤ, h ≠ 0 → ‖c h‖ ≤ 41 / 100 / (Δ * (h : ℝ) ^ 2))
    (K : ℕ) (Mb : ℝ)
    (hsmall : ∀ h : ℤ, |h| ≤ (K : ℤ) →
      ‖∑ n ∈ Ioc (N / 2) N, eC ((α + h / 2) * F γ n)‖ ≤ Mb) :
    ‖T‖ ≤ N * (41 / 100 / Δ) * (2 / ((K : ℝ) + 1 / 2)) + Mb * (1 / 2 + 41 / 100 / Δ * 4) := by
  classical
  set g : ℤ → ℂ := fun h => c h * ∑ n ∈ Ioc (N / 2) N, eC ((α + h / 2) * F γ n) with hg
  set S : Finset ℤ := Finset.Icc (-(K : ℤ)) K with hS
  have hmem : ∀ h : ℤ, h ∈ S ↔ |h| ≤ (K : ℤ) := by
    intro h; rw [hS, Finset.mem_Icc, abs_le]
  have hgS : HasSum (fun h => if h ∈ S then g h else 0) (∑ h ∈ S, g h) := by
    have : HasSum (fun h => if h ∈ S then g h else 0)
        (∑ b ∈ S, (if b ∈ S then g b else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => by simp [hb])
    convert this using 1
    exact Finset.sum_congr rfl (fun h hh => by simp [hh])
  obtain ⟨hsum2, htail2⟩ := leaf_inv_sq_tail_l9 K
  obtain ⟨hsum0, htail0⟩ := leaf_inv_sq_tail_l9 0
  have hΦ : ∀ h : ℤ, ‖∑ n ∈ Ioc (N / 2) N, eC ((α + h / 2) * F γ n)‖ ≤ (N : ℝ) :=
    fun h => norm_phi_le_l9 γ N _
  have hA : 0 ≤ 41 / 100 / Δ := by positivity
  -- the tail
  have htail : ‖T - ∑ h ∈ S, g h‖ ≤
      N * (41 / 100 / Δ) * ∑' h : ℤ, (if (K : ℤ) < |h| then 1 / (h : ℝ) ^ 2 else 0) := by
    have hb := (hsum2.hasSum.mul_left ((N : ℝ) * (41 / 100 / Δ)))
    refine (hT.sub hgS).norm_le_of_bounded hb (fun h => ?_)
    by_cases hh : h ∈ S
    · simp only [if_pos hh, sub_self, norm_zero]
      have := (hmem h).mp hh
      rw [if_neg (not_lt.mpr this)]; simp
    · simp only [if_neg hh, sub_zero]
      have hK : (K : ℤ) < |h| := lt_of_not_ge (fun h' => hh ((hmem h).mpr h'))
      rw [if_pos hK]
      have hne : h ≠ 0 := by
        rintro rfl; simp at hK; omega
      rw [hg, norm_mul]
      have hc' := hc h hne
      have hpos : (0 : ℝ) < (h : ℝ) ^ 2 := by positivity
      calc ‖c h‖ * ‖∑ n ∈ Ioc (N / 2) N, eC ((α + h / 2) * F γ n)‖
          ≤ 41 / 100 / (Δ * (h : ℝ) ^ 2) * N :=
            mul_le_mul hc' (hΦ h) (norm_nonneg _) (by positivity)
        _ = N * (41 / 100 / Δ) * (1 / (h : ℝ) ^ 2) := by field_simp
  -- the main part
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (hsmall 0 (by simp))
  have hmain : ‖∑ h ∈ S, g h‖ ≤ Mb * (1 / 2 + 41 / 100 / Δ * 4) := by
    have h1 : ‖∑ h ∈ S, g h‖ ≤ ∑ h ∈ S, ‖c h‖ * Mb := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun h hh => ?_))
      rw [hg, norm_mul]
      exact mul_le_mul_of_nonneg_left (hsmall h ((hmem h).mp hh)) (norm_nonneg _)
    have h2 : ∑ h ∈ S, ‖c h‖ ≤ ∑ h ∈ S, ((if h = 0 then (1 / 2 : ℝ) else 0) +
        41 / 100 / Δ * (if ((0 : ℕ) : ℤ) < |h| then 1 / (h : ℝ) ^ 2 else 0)) := by
      refine Finset.sum_le_sum (fun h _ => ?_)
      by_cases h0 : h = 0
      · subst h0; simpa using hc0 0
      · have hpos : ((0 : ℕ) : ℤ) < |h| := by simpa using h0
        rw [if_neg h0, if_pos hpos, zero_add]
        have hpos' : (0 : ℝ) < (h : ℝ) ^ 2 := by positivity
        calc ‖c h‖ ≤ 41 / 100 / (Δ * (h : ℝ) ^ 2) := hc h h0
          _ = 41 / 100 / Δ * (1 / (h : ℝ) ^ 2) := by field_simp
    have h3 : ∑ h ∈ S, ((if h = 0 then (1 / 2 : ℝ) else 0) +
        41 / 100 / Δ * (if ((0 : ℕ) : ℤ) < |h| then 1 / (h : ℝ) ^ 2 else 0)) ≤
        1 / 2 + 41 / 100 / Δ * 4 := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.mul_sum]
      have h0S : (0 : ℤ) ∈ S := (hmem 0).mpr (by simp)
      rw [if_pos h0S]
      have hle : ∑ h ∈ S, (if ((0 : ℕ) : ℤ) < |h| then 1 / (h : ℝ) ^ 2 else 0) ≤ 4 := by
        refine (hsum0.sum_le_tsum S (fun h _ => ?_)).trans ?_
        · split_ifs <;> positivity
        · calc _ ≤ 2 / (((0 : ℕ) : ℝ) + 1 / 2) := htail0
            _ = 4 := by norm_num
      have := mul_le_mul_of_nonneg_left hle hA
      linarith
    calc ‖∑ h ∈ S, g h‖ ≤ ∑ h ∈ S, ‖c h‖ * Mb := h1
      _ = Mb * ∑ h ∈ S, ‖c h‖ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      _ ≤ Mb * (1 / 2 + 41 / 100 / Δ * 4) := mul_le_mul_of_nonneg_left (h2.trans h3) hMb
  have htail' := mul_le_mul_of_nonneg_left htail2 (by positivity : (0 : ℝ) ≤ N * (41 / 100 / Δ))
  calc ‖T‖ = ‖(T - ∑ h ∈ S, g h) + ∑ h ∈ S, g h‖ := by ring_nf
    _ ≤ ‖T - ∑ h ∈ S, g h‖ + ‖∑ h ∈ S, g h‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- The constant bookkeeping behind "contrary to the hypothesis", page 370, with
`Δ = (9/5) x`, `x = ℰ^{-1/3} ≤ 1/100`, `K = ⌊ℰ^{2/3}⌋` and the Lemma 4 error `E ≤ x/100`. -/
theorem numeric_l9 (N x K E : ℝ) (hN : 0 ≤ N) (hx0 : 0 < x) (hx : x ≤ 1 / 100)
    (hK : 1 / x ^ 2 - 1 ≤ K) (hE : E ≤ x / 100) :
    N * (9 / 5 * x) / 4 + 2 * N * E +
      (N * (41 / 100 / (9 / 5 * x)) * (2 / (K + 1 / 2)) +
        N * x ^ 3 * (1 / 2 + 41 / 100 / (9 / 5 * x) * 4)) ≤ 95 / 100 * (N * x) := by
  have hx2 : x ^ 2 ≤ 1 / 10000 := by nlinarith
  have hx2p : 0 < x ^ 2 := by positivity
  have hinv : 10000 ≤ 1 / x ^ 2 := by
    rw [le_div_iff₀ hx2p]; nlinarith
  have hKlow : 99 / 100 * (1 / x ^ 2) ≤ K + 1 / 2 := by linarith
  have hKpos : 0 < 99 / 100 * (1 / x ^ 2) := by positivity
  have hfrac : 2 / (K + 1 / 2) ≤ 200 / 99 * x ^ 2 := by
    calc 2 / (K + 1 / 2) ≤ 2 / (99 / 100 * (1 / x ^ 2)) :=
          div_le_div_of_nonneg_left (by norm_num) hKpos hKlow
      _ = 200 / 99 * x ^ 2 := by field_simp; ring
  have hc : 41 / 100 / (9 / 5 * x) = 41 / 180 * (1 / x) := by field_simp; ring
  rw [hc]
  have hcpos : 0 ≤ N * (41 / 180 * (1 / x)) := by positivity
  have h3 : N * (41 / 180 * (1 / x)) * (2 / (K + 1 / 2)) ≤ 8200 / 17820 * (N * x) := by
    calc N * (41 / 180 * (1 / x)) * (2 / (K + 1 / 2))
        ≤ N * (41 / 180 * (1 / x)) * (200 / 99 * x ^ 2) :=
          mul_le_mul_of_nonneg_left hfrac hcpos
      _ = 8200 / 17820 * (N * x) := by field_simp; ring
  have h4 : N * x ^ 3 * (1 / 2 + 41 / 180 * (1 / x) * 4) ≤ 1 / 100 * (N * x) := by
    have he : N * x ^ 3 * (1 / 2 + 41 / 180 * (1 / x) * 4) =
        (N * x) * (x ^ 2 / 2 + 164 / 180 * x) := by field_simp; ring
    rw [he]
    have hNx : 0 ≤ N * x := by positivity
    have hq : x ^ 2 / 2 + 164 / 180 * x ≤ 1 / 100 := by nlinarith
    calc (N * x) * (x ^ 2 / 2 + 164 / 180 * x) ≤ (N * x) * (1 / 100) :=
          mul_le_mul_of_nonneg_left hq hNx
      _ = 1 / 100 * (N * x) := by ring
  have h2 : 2 * N * E ≤ 2 / 100 * (N * x) := by
    have := mul_le_mul_of_nonneg_left hE hN
    nlinarith
  have h1 : N * (9 / 5 * x) / 4 = 45 / 100 * (N * x) := by ring
  have hNx : 0 ≤ N * x := by positivity
  linarith

/-! ### Leaf A of DQ5 from Lemma 4 and the two leaves, page 370 displays 40 and 41 -/

set_option maxHeartbeats 1000000 in
/-- DQ5 leaf A, `leaf_large_value_shift_dq5`, P0082 page 370 displays 40 and 41:
a large even sum `Φ_e(α)` forces a large full sum `Φ(α - h/2)` with `|h| ≤ ℰ^{2/3}`.
CONDITIONAL ON `Lemma4`; its only open inputs are the two LEAF lemmas of this file. -/
theorem large_value_shift_of_lemma4 (h4 : Lemma4) :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ α : ℝ, |α| ≤ F γ N ^ δ → N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖Phie γ N α‖ →
          ∃ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (2 / 3 : ℝ) ∧
            N * calE γ κ N ^ (-(1 : ℝ)) <
              ‖∑ n ∈ Ioc (N / 2) N, eC ((α - h / 2) * F γ n)‖ := by
  intro γ hγ1 hγ2
  obtain ⟨κ₄, B₄, hκ₄, hL4⟩ := h4 γ hγ1 hγ2
  refine ⟨1, one_pos, fun δ _ _ => ⟨κ₄, hκ₄, fun κ hκ hκκ => ?_⟩⟩
  set B' := |B₄| + 1 with hB'
  have hB'pos : 0 < B' := by positivity
  have hLt := tendsto_L_l9 γ hγ2
  obtain ⟨Na, hNa⟩ := eventually_atTop.mp (hLt.eventually_ge_atTop (3 * Real.log 100 / κ))
  obtain ⟨Nb, hNb⟩ := eventually_atTop.mp
    (hLt.eventually_ge_atTop (Real.log (100 * B') / (2 * κ₄ / 3)))
  obtain ⟨Nc, hNc⟩ := eventually_atTop.mp
    ((tendsto_logpow_l9 γ (by linarith)).eventually_ge_atTop (2 * Real.log 2 + 1))
  refine ⟨max 2 (max Na (max Nb Nc)), fun N hN α _ hbig => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNa' := hNa N (((le_max_left _ _).trans (le_max_right _ _)).trans hN)
  have hNb' := hNb N ((((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans hN)
  have hNc' := hNc N ((((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans hN)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set L := Real.log (N : ℝ) ^ (3 - 2 * γ) with hLdef
  have hLnn : 0 ≤ L := Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))) _
  set x := Real.exp (-(κ * L / 3)) with hxdef
  have hx0 : 0 < x := Real.exp_pos _
  have hE13 : calE γ κ N ^ (-(1 / 3 : ℝ)) = x := by
    rw [calE_rpow_l9, hxdef]; congr 1; ring
  have hE1 : calE γ κ N ^ (-(1 : ℝ)) = x ^ 3 := by
    rw [calE_rpow_l9, hxdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE23 : calE γ κ N ^ (2 / 3 : ℝ) = 1 / x ^ 2 := by
    rw [calE_rpow_l9, hxdef, ← Real.exp_nat_mul, one_div, ← Real.exp_neg]; congr 1; push_cast; ring
  have hx : x ≤ 1 / 100 := by
    have h1 : Real.log 100 ≤ κ * L / 3 := by
      have := (div_le_iff₀ hκ).mp hNa'
      linarith
    calc x ≤ Real.exp (-Real.log 100) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 100 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hEerr : B' * Real.exp (-κ₄ * L) ≤ x / 100 := by
    have h1 : Real.log (100 * B') ≤ 2 * κ₄ / 3 * L := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * κ₄ / 3)).mp hNb'
      linarith
    have h2 : 100 * B' ≤ Real.exp (2 * κ₄ / 3 * L) := by
      calc 100 * B' = Real.exp (Real.log (100 * B')) := (Real.exp_log (by positivity)).symm
        _ ≤ _ := Real.exp_le_exp.mpr h1
    have h3 : Real.exp (-κ₄ * L) * Real.exp (2 * κ₄ / 3 * L) ≤ x := by
      rw [← Real.exp_add, hxdef]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hκκ hLnn
      nlinarith
    have hq := Real.exp_pos (-κ₄ * L)
    nlinarith
  -- the Fourier data
  set Δ := 9 / 5 * x with hΔdef
  have hΔ0 : 0 < Δ := by positivity
  have hΔ1 : Δ < 1 := by rw [hΔdef]; linarith
  obtain ⟨ψ, c, hψ01, hψ0, hψ1, hser, hc0, hc⟩ := leaf_trapezoid_fourier_l9 Δ hΔ0 hΔ1
  set K := ⌊1 / x ^ 2⌋₊ with hKdef
  have hK : 1 / x ^ 2 - 1 ≤ (K : ℝ) := by
    have := Nat.lt_floor_add_one (1 / x ^ 2); linarith
  have hKle : (K : ℝ) ≤ 1 / x ^ 2 := Nat.floor_le (by positivity)
  -- Lemma 4 count
  have hhalf : F γ N ^ (-(1 / 2 : ℝ)) < |(1 / 2 : ℝ)| := by
    rw [F, ← Real.exp_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc Real.exp (Real.log (N : ℝ) ^ γ * (-(1 / 2))) ≤ Real.exp (-(Real.log 2 + 1 / 2)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ < Real.exp (-Real.log 2) := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hcnt := fun z₁ z₂ (h0 : (0 : ℝ) ≤ z₂) (h1 : z₂ < z₁) (h2 : z₁ ≤ 1) =>
    hL4 N (by omega) (1 / 2) hhalf (by norm_num) z₁ z₂ h0 h1 h2
  set E := Real.exp (-κ₄ * Real.log N ^ (3 - 2 * γ)) with hEdef
  have hc1 := hcnt (Δ / 4) 0 le_rfl (by positivity) (by linarith)
  have hc2 := hcnt (1 / 2) (1 / 2 - Δ / 4) (by linarith) (by linarith) (by norm_num)
  have hB4 : B₄ * N * E ≤ N * (B' * E) := by
    have : B₄ ≤ B' := by rw [hB']; linarith [le_abs_self B₄]
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    calc B₄ * N * E = B₄ * (N * E) := by ring
      _ ≤ B' * (N * E) := mul_le_mul_of_nonneg_right this (mul_nonneg hNpos.le hE0)
      _ = N * (B' * E) := by ring
  have hbad : (((Ioc (N / 2) N).filter (fun n : ℕ =>
        (0 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < Δ / 4) ∨
        (1 / 2 - Δ / 4 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < 1 / 2))).card
        : ℝ) ≤ N * (9 / 5 * x) / 4 + 2 * N * (B' * E) := by
    rw [Finset.filter_or]
    have hu := Finset.card_union_le
      ((Ioc (N / 2) N).filter (fun n : ℕ =>
        0 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < Δ / 4))
      ((Ioc (N / 2) N).filter (fun n : ℕ =>
        1 / 2 - Δ / 4 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < 1 / 2))
    have hu' : (((Ioc (N / 2) N).filter (fun n : ℕ =>
        0 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < Δ / 4) ∪
      (Ioc (N / 2) N).filter (fun n : ℕ =>
        1 / 2 - Δ / 4 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < 1 / 2)).card
        : ℝ) ≤ (((Ioc (N / 2) N).filter (fun n : ℕ =>
        0 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < Δ / 4)).card : ℝ) +
      (((Ioc (N / 2) N).filter (fun n : ℕ =>
        1 / 2 - Δ / 4 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < 1 / 2)).card
        : ℝ) := by exact_mod_cast hu
    refine hu'.trans ?_
    rw [abs_le] at hc1 hc2
    rw [hΔdef] at hc1 hc2 ⊢
    nlinarith [hc1.2, hc2.2]
  -- the contrapositive
  by_contra hno
  push_neg at hno
  have hsmall : ∀ h : ℤ, |h| ≤ (K : ℤ) →
      ‖∑ n ∈ Ioc (N / 2) N, eC ((α + h / 2) * F γ n)‖ ≤ N * x ^ 3 := by
    intro h hh
    have hh' : (|((-h : ℤ) : ℝ)|) ≤ calE γ κ N ^ (2 / 3 : ℝ) := by
      rw [hE23]
      refine le_trans ?_ hKle
      push_cast
      rw [abs_neg, ← Int.cast_abs]
      exact_mod_cast hh
    have := hno (-h) hh'
    rw [hE1] at this
    convert this using 4
    push_cast; ring
  have hT := expansion_l9 γ N α ψ c hser
  have htr := truncated_l9 γ N α Δ hΔ0 c _ hT hc0 hc K (N * x ^ 3) hsmall
  have hsm := smoothing_l9 γ N α Δ ψ hψ01 hψ0 hψ1
  have hnum := numeric_l9 N x K (B' * E) hNpos.le hx0 hx hK (by rw [hEdef]; exact hEerr)
  have htot : ‖Phie γ N α‖ ≤ 95 / 100 * (N * x) := by
    calc ‖Phie γ N α‖ ≤ ‖Phie γ N α - ∑ n ∈ Ioc (N / 2) N,
            (ψ (1 / 2 * F γ n) : ℂ) * eC (α * F γ n)‖ +
          ‖∑ n ∈ Ioc (N / 2) N, (ψ (1 / 2 * F γ n) : ℂ) * eC (α * F γ n)‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := by rw [hΔdef] at htr hsm; linarith
  rw [hE13] at hbig
  have hNx : 0 < N * x := by positivity
  linarith

/-! ### Lemma 9 -/

/-- Page 370: eventually `ℰ^(2/3) < 2 X^δ + 2`. Same proof as DQ5 `height_below_window_dq5`. -/
theorem height_below_window_l9 (γ : ℝ) (hγ₁ : 1 < γ) (δ κ : ℝ) (hδ : 0 < δ) :
    ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → calE γ κ N ^ (2 / 3 : ℝ) < 2 * F γ N ^ δ + 2 := by
  have ht : Tendsto (fun N : ℕ => δ * Real.log (N : ℝ) ^ (3 * γ - 3)) atTop atTop :=
    (tendsto_logpow_l9 _ (by linarith)).const_mul_atTop hδ
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (κ * (2 / 3)))
  refine ⟨max 2 N₀, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hrate := hN₀ N ((le_max_right _ _).trans hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have he : (3 - 2 * γ) + (3 * γ - 3) = γ := by ring
  have hexponent : (κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) * (2 / 3) ≤
      Real.log (N : ℝ) ^ γ * δ := by
    calc (κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) * (2 / 3)
        = Real.log (N : ℝ) ^ (3 - 2 * γ) * (κ * (2 / 3)) := by ring
      _ ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) * (δ * Real.log (N : ℝ) ^ (3 * γ - 3)) :=
        mul_le_mul_of_nonneg_left hrate (Real.rpow_nonneg hlog.le _)
      _ = Real.log (N : ℝ) ^ γ * δ := by
        rw [mul_left_comm _ δ, ← Real.rpow_add hlog, he]
        ring
  have hreverse : calE γ κ N ^ (2 / 3 : ℝ) ≤ F γ N ^ δ := by
    rw [calE, F, ← Real.exp_mul, ← Real.exp_mul]
    exact Real.exp_le_exp.mpr hexponent
  have hpos : 0 < F γ N ^ δ := Real.rpow_pos_of_pos (Real.exp_pos _) δ
  linarith

/-- `Lemma9`, P0082 page 368, by the page 370 proof. CONDITIONAL ON `Theorem2` and
`Lemma4`; its only other open inputs are the two LEAF lemmas of this file. The type is
exactly the sealed `Lemma9` of State1539Data264. -/
theorem lemma9_of_theorem2_lemma4 (hT : Theorem2) (h4 : Lemma4) : Lemma9 := by
  intro γ hγ₁ hγ₂
  obtain ⟨δ₀, hδ₀, hA⟩ := large_value_shift_of_lemma4 h4 γ hγ₁ hγ₂
  refine ⟨min δ₀ (γ - 1), lt_min hδ₀ (by linarith), fun δ hδ hδlt => ?_⟩
  have hδA : δ < δ₀ := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδB : δ < γ - 1 := lt_of_lt_of_le hδlt (min_le_right _ _)
  obtain ⟨κ₀, hκ₀, hA⟩ := hA δ hδ hδA
  obtain ⟨κ₁, hκ₁, hB⟩ := shift_minor_of_theorem2 hT γ hγ₁ hγ₂ δ hδ hδB
  set κ := min κ₀ κ₁
  have hκ : 0 < κ := lt_min hκ₀ hκ₁
  obtain ⟨NA, hNA⟩ := hA κ hκ (min_le_left _ _)
  obtain ⟨NB, hNB⟩ := hB κ hκ (min_le_right _ _)
  obtain ⟨NH, hNH⟩ := height_below_window_l9 γ hγ₁ δ κ hδ
  refine ⟨κ, hκ, max NA (max NB NH), fun N hN α hα hlarge => ?_⟩
  have hNA' : NA ≤ N := (le_max_left _ _).trans hN
  have hNB' : NB ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNH' : NH ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  obtain ⟨h, hh, hbig⟩ := hNA N hNA' α hα hlarge
  refine ⟨h, hh, ?_⟩
  by_contra hfar
  rw [not_le] at hfar
  have hheight := hNH N hNH'
  have hFpos : 0 < F γ N ^ δ := Real.rpow_pos_of_pos (Real.exp_pos _) δ
  have hhalf : |(h : ℝ) / 2| ≤ F γ N ^ δ + 1 := by
    rw [abs_div, abs_two]
    linarith
  have hwin : |α - h / 2| ≤ 2 * F γ N ^ δ + 2 := by
    calc |α - h / 2| ≤ |α| + |(h : ℝ) / 2| := abs_sub _ _
      _ ≤ 2 * F γ N ^ δ + 2 := by linarith
  have hsmall := hNB N hNB' (α - h / 2) hfar hwin
  linarith

/-- `Lemma9` from Karacuba's `Lemma10` and `Lemma4`, through the clean
`theorem2_of_all_leaves` of Decomp1539a. CONDITIONAL ON `Lemma10` and `Lemma4`, the named
hypotheses `Lemma10DQ5` and `Lemma4DQ5` of DQ5Decisions, plus the two LEAF statements. -/
theorem lemma9_of_lemma10_lemma4 (h10 : Lemma10) (h4 : Lemma4) : Lemma9 :=
  lemma9_of_theorem2_lemma4 (theorem2_of_all_leaves h10) h4

/-- Twin check: the conclusion type above is the sealed `Lemma9` itself. -/
theorem lemma9_twin_l9 (hT : Theorem2) (h4 : Lemma4) : U1539.Lemma9 :=
  lemma9_of_theorem2_lemma4 hT h4

/-- Vacuity guard for the leaf hypotheses: `Δ = 9/500` satisfies `0 < Δ < 1`. -/
theorem vacuity_l9 : (0 : ℝ) < 9 / 500 ∧ (9 / 500 : ℝ) < 1 := by norm_num

end LeanLab.ExceptionalSet.DQLemma9

#print axioms LeanLab.ExceptionalSet.DQLemma9.shift_minor_of_theorem2
#print axioms LeanLab.ExceptionalSet.DQLemma9.even_floor_iff_l9
#print axioms LeanLab.ExceptionalSet.DQLemma9.smoothing_l9
#print axioms LeanLab.ExceptionalSet.DQLemma9.expansion_l9
#print axioms LeanLab.ExceptionalSet.DQLemma9.truncated_l9
#print axioms LeanLab.ExceptionalSet.DQLemma9.numeric_l9
#print axioms LeanLab.ExceptionalSet.DQLemma9.large_value_shift_of_lemma4
#print axioms LeanLab.ExceptionalSet.DQLemma9.height_below_window_l9
#print axioms LeanLab.ExceptionalSet.DQLemma9.lemma9_of_theorem2_lemma4
#print axioms LeanLab.ExceptionalSet.DQLemma9.lemma9_of_lemma10_lemma4
#print axioms LeanLab.ExceptionalSet.DQLemma9.leaf_trapezoid_fourier_l9
#print axioms LeanLab.ExceptionalSet.DQLemma9.leaf_trapezoid_coeff_l9
#print axioms LeanLab.ExceptionalSet.DQLemma9.leaf_trapezoid_series_l9
#print axioms LeanLab.ExceptionalSet.DQLemma9.leaf_inv_sq_tail_l9
