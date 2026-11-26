/-
AI wrote this Lean code, cloud session S146 burst-20261122 feed1122 Decomp243b p3, prover w2.
Binary Goldbach is open.

# Eventual prime counting bounds from the strong prime number theorem

`pi_upper_nat`: eventually `π N ≤ N / log N + 2 N / log² N`, the eventual form of
Rosser and Schoenfeld 1962 Theorem 1 display 3.2.
`pi_lower_nat`: eventually `N / log N ≤ π N`, the eventual form of Rosser and Schoenfeld 1962
Corollary 1 display 3.5.

Route: Mathlib's Abel summation `Chebyshev.primeCounting_eq_theta_div_log_add_integral`,
`π ⌊x⌋ = θ x / log x + ∫₂ˣ θ t / (t log² t) dt`. Upper bound: `θ ≤ ψ ≤ x + x / (10 log² x)`
from the lab's strong PNT `LeanLab.PNTPort.psi_explicit_strong`, and inside the integral
Chebyshev's `θ t ≤ log 4 · t` with the integral of `1 / log² t` split at `x ^ (9/10)`, giving
the coefficient `log 4 / 0.81 < 1.72` in front of `x / log² x`. Lower bound: `θ ≥ ψ - 2√x log x`
and the integral restricted to `[x/2, x]`, where `θ(t) ≥ θ(x/2) ≥ x/8`.
The theorems `*_real` and `*_eventually` take the strong PNT as a hypothesis `hP`; the final
`*_nat` theorems discharge it with `psi_explicit_strong`.
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import LeanLab.PNTPort.StrongPNT.Bridge

open Real Filter Chebyshev Topology Asymptotics MeasureTheory

noncomputable section

namespace LeanLab.AlmostPrimeSums.S146PiBounds

theorem psi_err_eventually (hP : ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    |ψ x - x| ≤ K * x * exp (-c * sqrt (log x))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, |ψ x - x| ≤ ε * x / log x ^ 2 := by
  obtain ⟨c, hc, K, hK⟩ := hP
  have hv : Tendsto (fun x : ℝ => c * sqrt (log x)) atTop atTop :=
    (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc
  have h0 := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hv).const_mul
    ((|K| + 1) / (ε * c ^ 4))
  rw [mul_zero] at h0
  filter_upwards [h0.eventually (gt_mem_nhds one_pos), eventually_ge_atTop (3 : ℝ)] with x hx hx3
  have hL : 0 < log x := log_pos (by linarith)
  have hsq : sqrt (log x) ^ 2 = log x := sq_sqrt hL.le
  have hx0 : 0 < x := by linarith
  simp only [Function.comp] at hx
  have h4 : (c * sqrt (log x)) ^ 4 = c ^ 4 * log x ^ 2 := by
    rw [mul_pow, show (4:ℕ) = 2 * 2 from rfl, pow_mul (sqrt _), hsq]
  rw [h4] at hx
  set e := exp (-(c * sqrt (log x))) with he
  have he0 : 0 < e := exp_pos _
  have hc4 : 0 < c ^ 4 := by positivity
  have hKe : (|K| + 1) * e * log x ^ 2 < ε := by
    have : (|K| + 1) / (ε * c ^ 4) * (c ^ 4 * log x ^ 2 * e)
        = (|K| + 1) * e * log x ^ 2 / ε := by
      field_simp
    rw [this, div_lt_one hε] at hx
    exact hx
  have hb := hK x (by linarith)
  rw [neg_mul] at hb
  have hL2 : 0 < log x ^ 2 := by positivity
  calc |ψ x - x| ≤ K * x * e := hb
    _ = K * (e * x) := by ring
    _ ≤ (|K| + 1) * (e * x) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (by positivity)
    _ = (|K| + 1) * e * x := by ring
    _ ≤ ε * x / log x ^ 2 := by
      rw [le_div_iff₀ hL2]
      nlinarith [mul_lt_mul_of_pos_right hKe hx0]

theorem log_sq_mul_rpow_le {s : ℝ} (hs : 0 < s) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, log x ^ 2 * x ^ (1 - s) ≤ δ * x := by
  have h := (isLittleO_log_rpow_rpow_atTop 2 hs).bound hδ
  filter_upwards [h, eventually_ge_atTop (1:ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ log x := log_nonneg hx1
  rw [Real.rpow_two, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)] at hx
  calc log x ^ 2 * x ^ (1 - s) ≤ δ * x ^ s * x ^ (1 - s) := by gcongr
    _ = δ * x := by rw [mul_assoc, ← rpow_add hx0]; simp

theorem integral_one_div_log_sq_le_mono {a b : ℝ} (hab : a ≤ b) (one_lt : 1 < a) :
    ∫ x in a..b, 1 / log x ^ 2 ≤ (b - a) / log a ^ 2 := by
  calc
  _ ≤ ∫ x in a..b, 1 / log a ^ 2 := by
      refine intervalIntegral.integral_mono_on hab ?_ (by simp) fun x ⟨_, _⟩ ↦ by
        gcongr <;> bound
      apply intervalIntegrable_one_div_log_sq <;> linarith
  _ ≤ _ := by simp [field]

theorem integral_one_div_log_sq_split {y x : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    ∫ t in 2..x, 1 / log t ^ 2 ≤ (y - 2) / log 2 ^ 2 + (x - y) / log y ^ 2 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := y)]
  · exact add_le_add (integral_one_div_log_sq_le_mono hy (by norm_num))
      (integral_one_div_log_sq_le_mono hyx (by linarith))
  all_goals apply intervalIntegrable_one_div_log_sq <;> linarith

theorem integral_theta_le_log4 {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, θ t / (t * log t ^ 2) ≤ log 4 * ∫ t in 2..x, 1 / log t ^ 2 := by
  calc ∫ t in 2..x, θ t / (t * log t ^ 2)
      ≤ ∫ t in 2..x, log 4 * (1 / log t ^ 2) := by
        refine intervalIntegral.integral_mono_on hx ?_ ?_ fun t ⟨ht, _⟩ ↦ ?_
        · rw [intervalIntegrable_iff, Set.uIoc_of_le hx,
            ← integrableOn_Icc_iff_integrableOn_Ioc]
          exact integrableOn_theta_div_id_mul_log_sq x
        · refine (intervalIntegrable_one_div_log_sq ?_ ?_).const_mul _ <;> linarith
        · have ht0 : 0 < t := by linarith
          have hl : 0 < log t := log_pos (by linarith)
          calc θ t / (t * log t ^ 2) ≤ log 4 * t / (t * log t ^ 2) := by
                gcongr; exact theta_le_log4_mul_x ht0.le
            _ = log 4 * (1 / log t ^ 2) := by field_simp
    _ = log 4 * ∫ t in 2..x, 1 / log t ^ 2 := intervalIntegral.integral_const_mul _ _

theorem pi_upper_real (hP : ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    |ψ x - x| ≤ K * x * exp (-c * sqrt (log x))) :
    ∀ᶠ x : ℝ in atTop, ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) ≤ x / log x + 2 * x / log x ^ 2 := by
  filter_upwards [psi_err_eventually hP (ε := 1/10) (by norm_num),
    log_sq_mul_rpow_le (s := 1/10) (by norm_num) (δ := 1/20) (by norm_num),
    (tendsto_rpow_atTop (show (0:ℝ) < 1 - 1/10 by norm_num)).eventually_ge_atTop 2,
    eventually_ge_atTop (3 : ℝ), eventually_ge_atTop (exp 1)] with x hpsi hy hy2 hx3 hxe
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ log x := by rw [le_log_iff_exp_le hx0]; exact hxe
  have hyx : x ^ (1 - 1/10 : ℝ) ≤ x := by
    calc x ^ (1 - 1/10 : ℝ) ≤ x ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = x := rpow_one x
  have hlogy : log (x ^ (1 - 1/10 : ℝ)) = (1 - 1/10) * log x := Real.log_rpow hx0 _
  have hpi := primeCounting_eq_theta_div_log_add_integral (show 2 ≤ x by linarith)
  have hI := (integral_theta_le_log4 (show 2 ≤ x by linarith)).trans
    (mul_le_mul_of_nonneg_left (integral_one_div_log_sq_split hy2 hyx)
      (log_nonneg (by norm_num)))
  rw [hlogy] at hI
  have hθ : θ x ≤ x + 1/10 * x / log x ^ 2 := by
    have := theta_le_psi x
    have := (abs_le.mp hpsi).2
    linarith
  set L := log x with hLdef
  set y := x ^ (1 - 1/10 : ℝ) with hydef
  have hL0 : 0 < L := by linarith
  set a := x / L ^ 2 with ha
  have ha0 : 0 < a := by positivity
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlog4 : log (4:ℝ) = 2 * log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  -- main term
  have h1 : θ x / L ≤ x / L + a / 10 := by
    rw [div_le_iff₀ hL0]
    have : a / 10 * L ≥ 1/10 * x / L ^ 2 := by
      have e1 : 1/10 * x / L ^ 2 = a / 10 := by rw [ha]; ring
      rw [e1]
      nlinarith [mul_le_mul_of_nonneg_left hL1 ha0.le]
    have : x / L * L = x := by field_simp
    linarith
  have hya : y ≤ a / 20 := by
    rw [ha, div_div, le_div_iff₀ (by positivity)]
    nlinarith [hy]
  have hP1 : (y - 2) / log 2 ^ 2 ≤ a / 20 / 0.48 := by
    have : (0.48:ℝ) ≤ log 2 ^ 2 := by nlinarith
    calc (y - 2) / log 2 ^ 2 ≤ y / log 2 ^ 2 := by gcongr; linarith
      _ ≤ y / 0.48 := by gcongr
      _ ≤ a / 20 / 0.48 := by gcongr
  have hP2 : (x - y) / ((1 - 1/10) * L) ^ 2 ≤ a / 0.81 := by
    calc (x - y) / ((1 - 1/10) * L) ^ 2 ≤ x / ((1 - 1/10) * L) ^ 2 := by
          gcongr; linarith
      _ = a / 0.81 := by rw [ha]; field_simp; ring
  have hP : log 4 * ((y - 2) / log 2 ^ 2 + (x - y) / ((1 - 1/10) * L) ^ 2)
      ≤ 1.3864 * (a / 20 / 0.48 + a / 0.81) := by
    apply mul_le_mul (by linarith) (by linarith) _ (by norm_num)
    have : 0 ≤ (y - 2) / log 2 ^ 2 := div_nonneg (by linarith) (by positivity)
    have : 0 ≤ (x - y) / ((1 - 1/10) * L) ^ 2 := div_nonneg (by linarith) (by positivity)
    linarith
  have h2a : 2 * x / L ^ 2 = 2 * a := by rw [ha]; ring
  rw [hpi, h2a]
  have hfin : (1.3864:ℝ) * (a / 20 / 0.48 + a / 0.81) ≤ 1.9 * a := by
    norm_num; linarith
  linarith [h1, hI, hP, hfin]

theorem theta_ge_quarter (hP : ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    |ψ x - x| ≤ K * x * exp (-c * sqrt (log x))) :
    ∀ᶠ y : ℝ in atTop, y / 4 ≤ θ y := by
  have h := (isLittleO_log_rpow_rpow_atTop 1 (show (0:ℝ) < 1/2 by norm_num)).bound
    (show (0:ℝ) < 1/8 by norm_num)
  filter_upwards [psi_err_eventually hP (ε := 1/10) (by norm_num), h,
    eventually_ge_atTop (exp 1)] with y hpsi hl hye
  have hy0 : 0 < y := lt_of_lt_of_le (exp_pos 1) hye
  have hL1 : 1 ≤ log y := by rw [le_log_iff_exp_le hy0]; exact hye
  have hy1 : 1 ≤ y := by
    have := Real.add_one_le_exp 1
    linarith
  rw [Real.rpow_one, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by positivity),
    ← Real.sqrt_eq_rpow] at hl
  have hst := psi_sub_theta_le hy1
  have hps := (abs_le.mp hpsi).1
  have hs0 : 0 ≤ √y := sqrt_nonneg y
  have hss : √y * √y = y := mul_self_sqrt hy0.le
  have h1 : 2 * √y * log y ≤ y / 4 := by nlinarith [mul_le_mul_of_nonneg_left hl hs0]
  have h2 : 1/10 * y / log y ^ 2 ≤ y / 10 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [one_le_pow₀ (n := 2) hL1]
  linarith

theorem pi_lower_real (hP : ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    |ψ x - x| ≤ K * x * exp (-c * sqrt (log x))) :
    ∀ᶠ x : ℝ in atTop, x / log x ≤ ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) := by
  have hhalf := (tendsto_id.atTop_div_const (show (0:ℝ) < 2 by norm_num)).eventually
    (theta_ge_quarter hP)
  filter_upwards [psi_err_eventually hP (ε := 1/100) (by norm_num),
    log_sq_mul_rpow_le (s := 1/2) (by norm_num) (δ := 1/64) (by norm_num), hhalf,
    eventually_ge_atTop (4 : ℝ), eventually_ge_atTop (exp 1)] with x hpsi hy hhx hx4 hxe
  simp only [id] at hhx
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ log x := by rw [le_log_iff_exp_le hx0]; exact hxe
  have hpi := primeCounting_eq_theta_div_log_add_integral (show 2 ≤ x by linarith)
  set f : ℝ → ℝ := fun t => θ t / (t * log t ^ 2) with hf
  have hint : ∀ a b : ℝ, 2 ≤ a → a ≤ b → IntervalIntegrable f volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
    exact (integrableOn_theta_div_id_mul_log_sq b).mono_set
      (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
  have hsplit : ∫ t in 2..x, f t = (∫ t in 2..x/2, f t) + ∫ t in x/2..x, f t :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 2 (x/2) (by linarith) (by linarith))
      (hint (x/2) x (by linarith) (by linarith))).symm
  have hnn : 0 ≤ ∫ t in 2..x/2, f t := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact div_nonneg (theta_nonneg t) (by have := ht.1; positivity)
  set L := log x with hLdef
  have hL0 : 0 < L := by linarith
  set cst := θ (x/2) / (x * L ^ 2) with hcst
  have hlow : (x - x/2) * cst ≤ ∫ t in x/2..x, f t := by
    have := intervalIntegral.integral_mono_on (show x/2 ≤ x by linarith)
      (intervalIntegrable_const (c := cst)) (hint (x/2) x (by linarith) (by linarith))
      (fun t ht => by
        have ht0 : 0 < t := by linarith [ht.1]
        have hlt : 0 < log t := log_pos (by linarith [ht.1])
        have hlx : log t ≤ L := log_le_log ht0 ht.2
        simp only [hf, hcst]
        apply div_le_div₀ (theta_nonneg t) (theta_mono ht.1) (by positivity)
        gcongr
        exact ht.2)
    simpa using this
  set a := x / L ^ 2 with ha
  have ha0 : 0 < a := by positivity
  have hθ : x - 1/100 * x / L ^ 2 - 2 * √x * L ≤ θ x := by
    have := psi_sub_theta_le (show 1 ≤ x by linarith)
    have := (abs_le.mp hpsi).1
    linarith
  have hsq : √x = x ^ (1 - 1/2 : ℝ) := by rw [Real.sqrt_eq_rpow]; norm_num
  rw [← hsq] at hy
  have hs0 : 0 ≤ √x := sqrt_nonneg x
  have hsa : 2 * √x ≤ a / 32 := by
    rw [ha, div_div, le_div_iff₀ (by positivity)]
    nlinarith [hy]
  have hm1 : θ x / L ≥ x / L - a / 100 - 2 * √x := by
    rw [ge_iff_le, le_div_iff₀ hL0]
    have e1 : (x / L - a / 100 - 2 * √x) * L = x - 1/100 * x / L ^ 2 * L - 2 * √x * L := by
      rw [ha]; field_simp
    rw [e1]
    have : 1/100 * x / L ^ 2 ≤ 1/100 * x / L ^ 2 * L := by
      have : 0 ≤ 1/100 * x / L ^ 2 := by positivity
      nlinarith
    linarith
  have hm2 : (x - x/2) * cst ≥ a / 16 := by
    have e2 : (x - x/2) * cst = θ (x/2) / (2 * L ^ 2) := by rw [hcst]; field_simp; ring
    rw [e2, ge_iff_le, ha, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hhx, pow_pos hL0 2]
  have hx1 : x / L ≤ x / L := le_rfl
  rw [hpi, hsplit]
  linarith

/-- Eventual upper bound, Rosser Schoenfeld 1962 Theorem 1 display 3.2 in eventual form:
`π N ≤ N / log N + 2 N / log² N` for all large `N`. -/
theorem pi_upper_nat : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (Nat.primeCounting N : ℝ) ≤ N / log N + 2 * N / log N ^ 2 := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp (pi_upper_real LeanLab.PNTPort.psi_explicit_strong)
  refine ⟨⌈X⌉₊, fun N hN => ?_⟩
  have := hX N (Nat.ceil_le.mp hN)
  simpa [Nat.floor_natCast] using this

/-- Eventual lower bound, Rosser Schoenfeld 1962 Corollary 1 display 3.5 in eventual form:
`N / log N ≤ π N` for all large `N`. -/
theorem pi_lower_nat : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (N : ℝ) / log N ≤ (Nat.primeCounting N : ℝ) := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp (pi_lower_real LeanLab.PNTPort.psi_explicit_strong)
  refine ⟨⌈X⌉₊, fun N hN => ?_⟩
  have := hX N (Nat.ceil_le.mp hN)
  simpa [Nat.floor_natCast] using this

/-- `Decomp243bFeed1122Summed.leaf_pi_upper_sharp` with its exact statement. -/
theorem leaf_pi_upper_sharp_s146 : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (Nat.primeCounting N : ℝ) ≤ N / log N + 2 * N / log N ^ 2 :=
  pi_upper_nat

end LeanLab.AlmostPrimeSums.S146PiBounds
