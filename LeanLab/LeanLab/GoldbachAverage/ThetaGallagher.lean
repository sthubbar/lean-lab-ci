import LeanLab.GoldbachAverage.ThetaLemma1
import LeanLab.PNTPort.Selberg.GallagherEdge

/-!
Gallagher's lemma for the theta route of P0051 page 20.
The remaining input bounds weighted short interval windows including cutoff edges.
The coefficient at zero is minus one, as required by the geometric comparison sum.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.ThetaLayers
open Complex Finset MeasureTheory Filter Topology
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.PNTPort.Gallagher LeanLab.PNTPort.Selberg LeanLab.PNTPort.LargeSieve
open LeanLab.LZCesaroShort
local notation "eL" => LeanLab.PNTPort.LargeSieve.e

/-- The exponentially weighted coefficient Lambda minus one. -/
def weightedCoeff (N n : ℕ) : ℂ := (Real.exp (-(n / N)) : ℂ) * lam1 n

/-- Missing weighted window variance input.
This includes the finite cutoff edges. It is not asserted. -/
def ThetaWeightedVariance (theta : ℝ) : Prop := ∃ K : ℝ, 0 ≤ K ∧
  ∀ N L M : ℕ, 2 ≤ N → 1 ≤ L → L ≤ N →
    ∑ m ∈ range (M + L), ‖win (weightedCoeff N) M L m‖ ^ 2 ≤
      K * L * (N : ℝ) ^ (2 * theta) * (1 + Real.log N) ^ 4

set_option maxHeartbeats 2000000 in
/-- Fourier mean square on reciprocal integer windows, CONDITIONAL ON weighted variance. -/
theorem theta_lemma1_range (theta : ℝ) (htheta0 : 0 ≤ theta) (hv : ThetaWeightedVariance theta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N L : ℕ, 2 ≤ N → 1 ≤ L → L ≤ N →
      ∫ α in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖St N α - 1 / zz N α‖ ^ 2 ≤
        C * (N : ℝ) ^ (2 * theta) * (1 + Real.log N) ^ 4 / L := by
  obtain ⟨Kv, hKv, hvar⟩ := hv
  set Cw := Real.pi ^ 2 / 4 * Kv with hCwdef
  have hCw : 0 ≤ Cw := by positivity
  refine ⟨2 * Cw + 128, by positivity, fun N L hN2 hL hLN => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hN : 1 ≤ N := hL.trans hLN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set W := (N : ℝ) ^ (2 * theta) * (1 + Real.log N) ^ 4 / L with hW
  set ξ := 1 / (2 * (L : ℝ)) with hξ
  have hξ0 : 0 < ξ := by positivity
  have hξle : -ξ ≤ ξ := by linarith
  set St := LeanLab.LZCesaroShort.St N with hStd
  set zz := LeanLab.LZCesaroShort.zz N with hzzd
  set D : ℝ → ℂ := fun α => St α - 1 / (1 - Complex.exp (-(zz α))) with hD
  set g : ℕ → ℝ → ℂ := fun n α => (Real.exp (-(n / N)) : ℂ) * (lam1 n * eL (n * α)) with hg
  -- the dominating series
  set q := Real.exp (-(1 / (N : ℝ))) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    have : 0 < 1 / (N : ℝ) := by positivity
    have h := Real.exp_lt_exp.mpr (show -(1 / (N : ℝ)) < 0 by linarith)
    rwa [Real.exp_zero] at h
  have hpow : ∀ n : ℕ, Real.exp (-(n / N)) = q ^ n := by
    intro n; rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  set u : ℕ → ℝ := fun n => ((n : ℝ) + 1) * q ^ n with hu
  have hus : Summable u := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
      (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
    have h2 := summable_geometric_of_lt_one hq0.le hq1
    refine (h1.add h2).congr fun n => ?_
    simp only [hu, pow_one]; ring
  have hu0 : ∀ n, 0 ≤ u n := fun n => by simp only [hu]; positivity
  have hgu : ∀ n α, ‖g n α‖ ≤ u n := by
    intro n α
    simp only [hg, hu]
    rw [norm_mul, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hpow, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_lam1_le_succ n) (pow_nonneg hq0.le n)
  have hgc : ∀ n, Continuous (g n) := fun n =>
    continuous_const.mul (continuous_const.mul (continuous_e_mul _))
  -- (i) the limit
  have hlimint : ∫ α in (-ξ)..ξ, ‖D α‖ ^ 2 ≤ Cw * W := by
    have hT : Tendsto (fun M : ℕ => ∫ α in (-ξ)..ξ, ‖∑ n ∈ range M, g n α‖ ^ 2) atTop
        (𝓝 (∫ α in (-ξ)..ξ, ‖D α‖ ^ 2)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun _ => (∑' n, u n) ^ 2) ?_ ?_ intervalIntegrable_const ?_
      · exact Eventually.of_forall fun M =>
          ((continuous_finsetSum _ fun n _ => hgc n).norm.pow 2).aestronglyMeasurable
      · refine Eventually.of_forall fun M => ae_of_all _ fun α _ => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h1 : ‖∑ n ∈ range M, g n α‖ ≤ ∑' n, u n :=
          (norm_sum_le _ _).trans ((sum_le_sum fun n _ => hgu n α).trans
            (hus.sum_le_tsum _ fun n _ => hu0 n))
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      · refine ae_of_all _ fun α _ => ?_
        exact ((hasSum_weighted hN α).tendsto_sum_nat.norm).pow 2
    refine le_of_tendsto' hT fun M => ?_
    have hgall := gallagher (weightedCoeff N) M L (by omega)
    have hv := hvar N L M hN2 hL hLN
    have hb := mul_le_mul_of_nonneg_left hv (sq_nonneg (Real.pi / (2 * L)))
    have he : (Real.pi / (2 * (L : ℝ))) ^ 2 *
        (Kv * L * (N : ℝ) ^ (2 * theta) * (1 + Real.log N) ^ 4) = Cw * W := by
      dsimp [Cw, W]
      field_simp
      ring
    rw [he] at hb
    have hsumEq : ∀ α : ℝ, (∑ n ∈ range M, g n α) =
        ∑ n ∈ range M, weightedCoeff N n * eL (n * α) := by
      intro α
      apply sum_congr rfl
      intro n _
      simp only [hg, weightedCoeff]
      ring
    simp_rw [hsumEq]
    exact hgall.trans hb
  -- (ii) the pointwise comparison
  have hpt : ∀ α ∈ Set.uIcc (-ξ) ξ, ‖St α - 1 / zz α‖ ^ 2 ≤ 2 * ‖D α‖ ^ 2 + 128 := by
    intro α hα
    rw [Set.uIcc_of_le hξle] at hα
    have hre : (zz α).re = 1 / N := by simp [hzzd, LeanLab.LZCesaroShort.zz]
    have him : (zz α).im = -(2 * Real.pi * α) := by simp [hzzd, LeanLab.LZCesaroShort.zz]
    have hαb : |α| ≤ 1 / 2 := by
      rw [abs_le]
      have : ξ ≤ 1 / 2 := by rw [hξ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      constructor <;> linarith [hα.1, hα.2]
    have hb := geom_sub_inv_le (z := zz α) (by rw [hre]; positivity)
      (by rw [hre, div_le_one hN0]; exact hN1)
      (by rw [him, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
          nlinarith [Real.pi_pos])
    have hsplit : St α - 1 / zz α = D α + (1 / (1 - Complex.exp (-(zz α))) - 1 / zz α) := by
      simp only [hD]; ring
    rw [hsplit]
    have h1 := norm_add_le (D α) (1 / (1 - Complex.exp (-(zz α))) - 1 / zz α)
    have h2 : (‖D α‖ + ‖1 / (1 - Complex.exp (-(zz α))) - 1 / zz α‖) ^ 2 ≤ 2 * ‖D α‖ ^ 2 + 128 := by
      nlinarith [sq_nonneg (‖D α‖ - ‖1 / (1 - Complex.exp (-(zz α))) - 1 / zz α‖),
        norm_nonneg (1 / (1 - Complex.exp (-(zz α))) - 1 / zz α)]
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  -- (iii) continuity
  have hStc : Continuous St := by
    have : St = fun α => ∑' n : ℕ, ((Λ n * Real.exp (-n / N) : ℝ) : ℂ) * eL (n * α) := by
      ext α; simp [hStd, LeanLab.LZCesaroShort.St]
    rw [this]
    refine continuous_tsum (fun n => continuous_const.mul (continuous_e_mul _)) hus fun n α => ?_
    rw [norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      neg_div, hpow, abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (pow_nonneg hq0.le n))]
    have h2 : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have h3 : Real.log n ≤ n := Real.log_le_self (Nat.cast_nonneg n)
    exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hq0.le n)
  have hzzc : Continuous zz := by
    show Continuous (fun α => LeanLab.LZCesaroShort.zz N α)
    unfold LeanLab.LZCesaroShort.zz; fun_prop
  have hzz0 : ∀ α, zz α ≠ 0 := by
    intro α h
    have := congrArg Complex.re h
    simp [hzzd, LeanLab.LZCesaroShort.zz] at this
    exact absurd this (by positivity)
  have hden0 : ∀ α, 1 - Complex.exp (-(zz α)) ≠ 0 := by
    intro α h
    have h1 : Complex.exp (-(zz α)) = 1 := by linear_combination -h
    have h2 := congrArg norm h1
    rw [cexp_neg_zz, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one] at h2
    linarith
  have hDc : Continuous D := by
    simp only [hD]
    exact hStc.sub (continuous_const.div (continuous_const.sub (hzzc.neg.cexp)) hden0)
  have hLc : Continuous (fun α => ‖St α - 1 / zz α‖ ^ 2) :=
    ((hStc.sub (continuous_const.div hzzc hzz0)).norm).pow 2
  have hRc : Continuous (fun α => 2 * ‖D α‖ ^ 2 + 128) :=
    (continuous_const.mul (hDc.norm.pow 2)).add continuous_const
  -- (iv) assembly
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hξle
    (hLc.intervalIntegrable (μ := volume) _ _)
    (hRc.intervalIntegrable (μ := volume) _ _)
    (fun α hα => hpt α (by rw [Set.uIcc_of_le hξle]; exact hα))
  have hDi : IntervalIntegrable (fun α => 2 * ‖D α‖ ^ 2) volume (-ξ) ξ :=
    (continuous_const.mul (hDc.norm.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hDi intervalIntegrable_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    smul_eq_mul] at hmono
  have hlen : ξ - -ξ = 1 / L := by rw [hξ]; field_simp; ring
  rw [hlen] at hmono
  have hW1 : 1 / (L : ℝ) ≤ W := by
    have hp : 1 ≤ (N : ℝ) ^ (2 * theta) := Real.one_le_rpow hN1 (by linarith)
    have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
    have hf : 1 ≤ (1 + Real.log N) ^ 4 := one_le_pow₀ (by linarith)
    have hprod : 1 ≤ (N : ℝ) ^ (2 * theta) * (1 + Real.log N) ^ 4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hf)]
    exact div_le_div_of_nonneg_right hprod hL0.le
  calc ∫ α in (-ξ)..ξ, ‖St α - 1 / zz α‖ ^ 2
      ≤ 2 * (∫ α in (-ξ)..ξ, ‖D α‖ ^ 2) + 1 / L * 128 := hmono
    _ ≤ 2 * (Cw * W) + 128 * W := by linarith
    _ = (2 * Cw + 128) * W := by ring
    _ = (2 * Cw + 128) * (N : ℝ) ^ (2 * theta) * (1 + Real.log N) ^ 4 / L := by dsimp [W]; ring

/-- Passing from reciprocal integer windows to every xi in the layer range. -/
theorem theta_lemma1_of_weighted_variance (theta : ℝ) (htheta0 : 0 ≤ theta)
    (hv : ThetaWeightedVariance theta) : ThetaLemma1 theta := by
  obtain ⟨C, hC, hb⟩ := theta_lemma1_range theta htheta0 hv
  refine ⟨4 * C, by positivity, fun N hN ξ hξlo hξhi => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hξ0 : 0 < ξ := lt_of_lt_of_le (by positivity) hξlo
  set y := 1 / (2 * ξ) with hy
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ (by positivity)]; linarith
  have hyN : y ≤ N := by
    rw [hy, div_le_iff₀ (by positivity)]
    have h := (div_le_iff₀ hN0).mp hξlo
    linarith
  set L := ⌊y⌋₊ with hL
  have hL1 : 1 ≤ L := (Nat.one_le_floor_iff y).mpr hy1
  have hLN : L ≤ N := Nat.floor_le_of_le hyN
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hLy : (L : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyL : y < (L : ℝ) + 1 := Nat.lt_floor_add_one y
  have hy2L : y < 2 * L := by
    have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    linarith
  have hξL : ξ ≤ 1 / (2 * L) := by
    rw [hy, le_div_iff₀ (by positivity)] at hLy
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hLξ : 1 / (L : ℝ) ≤ 4 * ξ := by
    rw [hy, div_lt_iff₀ (by positivity)] at hy2L
    rw [div_le_iff₀ hL0]
    linarith
  have hmono := intervalIntegral.integral_mono_interval (μ := volume)
    (show -(1 / (2 * (L : ℝ))) ≤ -ξ by linarith)
    (show -ξ ≤ ξ by linarith) hξL
    (Filter.Eventually.of_forall fun α => sq_nonneg ‖St N α - 1 / zz N α‖)
    ((continuous_St_sub (by omega : 1 ≤ N)).intervalIntegrable (μ := volume) _ _)
  refine hmono.trans ((hb N L hN hL1 hLN).trans ?_)
  have hp : 0 ≤ C * (N : ℝ) ^ (2 * theta) * (1 + Real.log N) ^ 4 := by positivity
  calc C * (N : ℝ) ^ (2 * theta) * (1 + Real.log N) ^ 4 / L
      = (C * (N : ℝ) ^ (2 * theta) * (1 + Real.log N) ^ 4) * (1 / L) := by ring
    _ ≤ (C * (N : ℝ) ^ (2 * theta) * (1 + Real.log N) ^ 4) * (4 * ξ) :=
      mul_le_mul_of_nonneg_left hLξ hp
    _ = _ := by ring

/-- BHMS error estimate, CONDITIONAL ON the weighted short interval variance alone. -/
theorem bhms_of_weighted_variance (hv : ThetaWeightedVariance Theta) :
    GSCor2.BHMSTheorem6E := by
  intro hlo hhi
  exact bhms_theorem6E_proved
    (theta_lemma1_of_weighted_variance Theta (by linarith) hv) hlo hhi

end LeanLab.GoldbachAverage.ThetaLayers
