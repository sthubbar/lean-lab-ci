/-
P0022, Kaniecki 1995, inequality (22), p. 370, the bound for `I₃`, reduced to the kernel
integral (9) at `A = 0`, p. 365, and the numerical constant `4.51`, p. 370.
CLOUD 20261020T2317Z-cloud53, unit U-6765, T1.

Proof as on p. 370: pointwise `|C(σ + it)| ≤ Σ_p log p/(p^σ (p^{2σ} - 1)) ≤ Σ_p log p/(√p (p - 1))`
for `σ ≥ 1/2`; so `I₃ ≤ K² ∫_0^∞ k(t) dt`; by (9) at `A = 0` the kernel integral is
`π ((1 + 1/T)^{2σ} - 1)/(2σ)`; this is at most `π/(T (1 - σ/T))`, PROVED here by Bernoulli's
inequality where the paper uses (10); and `K² < 4.51`.
Named inputs: `Kernel9`, `Const451`. Then `lemma5_of'` gives Lemma 5 CONDITIONAL ON Lemma 4,
`Parseval1920`, `Bound21`, `Kernel9`, `Const451`.
AI wrote this Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Kaniecki1995.Lemma5Red

namespace LeanLab.Kaniecki1995.L5

open LeanLab.Kaniecki1995 Real Complex MeasureTheory
open scoped ENNReal

/-- `K = Σ_p log p/(√p (p - 1))`, written as `Σ_n |primeTerm (1/2) n|`, see `norm_primeTerm_half`. -/
noncomputable def K451 : ℝ := ∑' n : ℕ, ‖primeTerm (1 / 2 : ℂ) n‖

/-- p. 370: `(Σ_p log p/(√p (p-1)))² < 4.51`. CITED numerical input; mpmath gives about 2.9635,
see Kaniecki1995/STATEMENTS.md. Stated with `≤`. -/
def Const451 : Prop := K451 ^ 2 ≤ 4.51

/-- (9) at `A = 0`, p. 365: `∫_0^∞ |(e^{δ(σ+it)} - 1)/(σ+it)|² dt = π (e^{2σδ} - 1)/(2σ)`,
`e^δ = 1 + 1/T`. CITED classical integral; only `≤` is used. -/
def Kernel9 : Prop :=
  ∀ T σ : ℝ, 0 < T → 0 < σ →
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (kern T σ t) ≤
      ENNReal.ofReal (π / (2 * σ) * ((1 + 1 / T) ^ (2 * σ) - 1))

/-- `|primeTerm (1/2) p| = log p/(√p (p - 1))` for a prime `p`, so `K451` is the paper's sum. -/
theorem norm_primeTerm_half {n : ℕ} (hn : n.Prime) :
    ‖primeTerm (1 / 2 : ℂ) n‖ = Real.log n / (√(n : ℝ) * ((n : ℝ) - 1)) := by
  have hx2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  unfold primeTerm
  rw [if_pos hn, norm_div, norm_mul, norm_natCast_cpow_of_pos hn.pos, Complex.norm_real,
    Real.norm_of_nonneg hlog0, show (2 : ℂ) * (1 / 2) = 1 by norm_num, Complex.cpow_one]
  have : ‖(n : ℂ) - 1‖ = (n : ℝ) - 1 := by
    rw [show (n : ℂ) - 1 = (((n : ℝ) - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [this, Real.sqrt_eq_rpow]
  norm_num

theorem sub_one_le_norm_den {s : ℂ} (hs : 1 / 2 ≤ s.re) {n : ℕ} (hn : n.Prime) :
    (n : ℝ) - 1 ≤ ‖(n : ℂ) ^ (2 * s) - 1‖ := by
  have hx2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
  have h2 : ‖(n : ℂ) ^ (2 * s)‖ = (n : ℝ) ^ (2 * s.re) := by
    rw [norm_natCast_cpow_of_pos hn.pos]; simp
  have hB : (n : ℝ) ≤ (n : ℝ) ^ (2 * s.re) := by
    conv_lhs => rw [← Real.rpow_one (n : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have := norm_sub_norm_le ((n : ℂ) ^ (2 * s)) 1
  rw [h2, norm_one] at this
  linarith

theorem norm_primeTerm_le_half {s : ℂ} (hs : 1 / 2 ≤ s.re) (n : ℕ) :
    ‖primeTerm s n‖ ≤ ‖primeTerm (1 / 2 : ℂ) n‖ := by
  by_cases hn : n.Prime
  · rw [norm_primeTerm_half hn]
    have hx2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    unfold primeTerm
    rw [if_pos hn, norm_div, norm_mul, norm_natCast_cpow_of_pos hn.pos, Complex.norm_real,
      Real.norm_of_nonneg hlog0]
    have hA : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hs
    rw [Real.sqrt_eq_rpow]
    have hp : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    apply div_le_div_of_nonneg_left hlog0 (mul_pos hp (by linarith))
    exact mul_le_mul hA (sub_one_le_norm_den hs hn) (by linarith) (hp.le.trans hA)
  · simp [primeTerm, hn]

theorem summable_norm_primeTerm {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    Summable fun n => ‖primeTerm s n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_primeTerm_le hs) summable_uC

theorem norm_primeC_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (t : ℝ) : ‖primeC σ t‖ ≤ K451 := by
  have hs : 1 / 2 ≤ (sAt σ t).re := by rw [sAt_re]; exact hσ
  have hs' : 1 / 2 ≤ (1 / 2 : ℂ).re := by norm_num
  unfold primeC K451
  exact (norm_tsum_le_tsum_norm (summable_norm_primeTerm hs)).trans
    ((summable_norm_primeTerm hs).tsum_le_tsum (norm_primeTerm_le_half hs)
      (summable_norm_primeTerm hs'))

/-- `π ((1 + 1/T)^{2σ} - 1)/(2σ) ≤ π/(T (1 - σ/T))` for `T > 0`, `1/2 ≤ σ ≤ 1`, Bernoulli. -/
theorem kernel_real_le {T σ : ℝ} (hT : 0 < T) (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1) (hσT : σ < T) :
    π / (2 * σ) * ((1 + 1 / T) ^ (2 * σ) - 1) ≤ π / (T * (1 - σ / T)) := by
  set u := 1 / T with hu
  have hu0 : 0 < u := by positivity
  have hsplit : (1 + u) ^ (2 * σ) = (1 + u) * (1 + u) ^ (2 * σ - 1) := by
    rw [← Real.rpow_one_add' (by positivity) (by linarith)]
    congr 1; ring
  have hB : (1 + u) ^ (2 * σ - 1) ≤ 1 + (2 * σ - 1) * u :=
    _root_.rpow_one_add_le_one_add_mul_self (by linarith) (by linarith) (by linarith)
  have hle : (1 + u) ^ (2 * σ) - 1 ≤ 2 * σ * u + (2 * σ - 1) * u ^ 2 := by
    rw [hsplit]; nlinarith
  have hTs : T * (1 - σ / T) = T - σ := by field_simp
  rw [hTs]
  have hσ0 : 0 < σ := by linarith
  have hTσ : 0 < T - σ := by linarith
  calc π / (2 * σ) * ((1 + u) ^ (2 * σ) - 1)
      ≤ π / (2 * σ) * (2 * σ * u + (2 * σ - 1) * u ^ 2) := by gcongr
    _ ≤ π / (T - σ) := by
      rw [hu, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hTσ]
      have hπ : 0 < π := Real.pi_pos
      have key : (2 * σ * (1 / T) + (2 * σ - 1) * (1 / T) ^ 2) * (T - σ) ≤ 2 * σ := by
        have h1 : (2 * σ - 1) * (T - σ) ≤ 2 * σ ^ 2 * T := by
          nlinarith [mul_pos hσ0 hT, sq_nonneg (σ - 1 / 2), mul_nonneg (by linarith : (0:ℝ) ≤ 2 * σ - 1) hσ0.le]
        have e : (2 * σ * (1 / T) + (2 * σ - 1) * (1 / T) ^ 2) * (T - σ) =
            2 * σ - (2 * σ ^ 2 * T - (2 * σ - 1) * (T - σ)) / T ^ 2 := by
          field_simp; ring
        rw [e]
        have : 0 ≤ (2 * σ ^ 2 * T - (2 * σ - 1) * (T - σ)) / T ^ 2 :=
          div_nonneg (by linarith) (by positivity)
        linarith
      nlinarith [mul_le_mul_of_nonneg_left key hπ.le]

/-- **(22), p. 370**, CONDITIONAL ON `Kernel9` and `Const451`. -/
theorem bound22_of (hK : Kernel9) (hC : Const451) : Bound22 := by
  intro T σ hT hσ1 hs
  have hT0 : 0 < T := by linarith
  have hσ0 : 0 < σ := by linarith
  have hK0 : 0 ≤ K451 := tsum_nonneg fun _ => norm_nonneg _
  have hkern0 : ∀ t, 0 ≤ kern T σ t := fun t => by unfold kern; positivity
  calc wInt T σ (primeC σ)
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (K451 ^ 2) * ENNReal.ofReal (kern T σ t) := by
        refine lintegral_mono fun t => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have h := norm_primeC_le hσ1.le t
        have : ‖primeC σ t‖ ^ 2 ≤ K451 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
        nlinarith [hkern0 t]
    _ = ENNReal.ofReal (K451 ^ 2) * ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (kern T σ t) :=
        lintegral_const_mul _ (measurable_kern T σ).ennreal_ofReal
    _ ≤ ENNReal.ofReal 4.51 * ENNReal.ofReal (π / (T * (1 - σ / T))) := by
        gcongr
        · exact hC
        · exact (hK T σ hT0 hσ0).trans
            (ENNReal.ofReal_le_ofReal (kernel_real_le hT0 hσ1.le (by linarith) (by linarith)))
    _ = ENNReal.ofReal (4.51 * π / (T * (1 - σ / T))) := by
        rw [← ENNReal.ofReal_mul (by norm_num), mul_div_assoc]

/-- **Kaniecki 1995, Lemma 5**, CONDITIONAL ON Lemma 4, `Parseval1920` under RH, `Bound21`,
`Kernel9` and `Const451`. -/
theorem lemma5_of' (h4 : Lemma4) (hP : Parseval1920) (h21 : Bound21) (hK : Kernel9)
    (hC : Const451) : Lemma5 :=
  lemma5_of h4 hP h21 (bound22_of hK hC)

end LeanLab.Kaniecki1995.L5

#print axioms LeanLab.Kaniecki1995.L5.norm_primeTerm_half
#print axioms LeanLab.Kaniecki1995.L5.norm_primeC_le
#print axioms LeanLab.Kaniecki1995.L5.kernel_real_le
#print axioms LeanLab.Kaniecki1995.L5.bound22_of
#print axioms LeanLab.Kaniecki1995.L5.lemma5_of'

