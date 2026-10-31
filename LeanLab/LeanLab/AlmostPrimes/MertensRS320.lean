/-
AI-written Lean code, Claude, 2026-10-21, cloud session 20261021T0217Z-cloud56, unit U-6819.
P0048 Dudek-Dunn shared input `RSRecipRed.RS320`, Rosser-Schoenfeld 1962 (3.18) in the lab's
form `Σ_{p ≤ x} 1/p < log log x + 0.26150 + 1/(2 log² x)` for `x ≥ 10^10`.

Explicit Mertens second theorem by Abel summation from Chebyshev θ.
* `abel_identity`, PROVED, no input: for real `1 < a ≤ b`, with `R t = θ t - t` and
  `g t = (1 + log t)/(t² log² t)`,
  `S b - S a = log log b - log log a + R b/(b log b) - R a/(a log a) + ∫_a^b g t R t dt`,
  the finite form of `Σ_{p ≤ x} 1/p = log log x + B + R x/(x log x) - ∫_x^∞ R g`.
* `F_diff`, CONDITIONAL ON `DusartThm52k2`: `|F b - F a| ≤ 0.01/log² a` for `10^10 ≤ a ≤ b`,
  with `F x = S x - log log x`.
* `tendsto_F`, CONDITIONAL ON `DusartThm52k2`: `F x` converges; `B` is defined as its limit.
* `mertens_explicit`, CONDITIONAL ON `DusartThm52k2`: `|S x - log log x - B| ≤ 0.01/log² x`.
* `RS320_of_dusart`, CONDITIONAL ON `DusartThm52k2` and `BLe`, the numeric input
  `B ≤ 0.26150`, where `B ≈ 0.2614972128` is the Meissel-Mertens constant.
KNOWN mathematics, Mertens 1874 and Rosser-Schoenfeld 1962. Goldbach is open.
-/
import Mathlib
import LeanLab.Common.ThetaWindowDusart

open Real Finset Filter Topology MeasureTheory

noncomputable section
namespace LeanLab.AlmostPrimes.MertensRS320

/-- `S x = Σ_{p ≤ x} 1/p`, the same sum as in `RSRecipRed.RS320`. -/
def S (x : ℝ) : ℝ := ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / p

/-- `R t = θ t - t`. -/
def R (t : ℝ) : ℝ := Chebyshev.theta t - t

/-- `F x = S x - log log x`. -/
def F (x : ℝ) : ℝ := S x - log (log x)

/-- The Meissel-Mertens constant, defined as the limit of `F` at infinity. -/
def B : ℝ := limUnder atTop F

/-- The weight `g t = (1 + log t)/(t² log² t) = -d/dt (1/(t log t))`. -/
def g (t : ℝ) : ℝ := (1 + log t) / (t ^ 2 * log t ^ 2)

/-- Numeric input: `B ≤ 0.26150`. The true value is `0.26149 72128...`. -/
def BLe : Prop := B ≤ 0.26150

/-- Abel weight `c k = log k` on primes. -/
def c (k : ℕ) : ℝ := if k.Prime then log k else 0

/-- `fA t = 1/(t log t)`. -/
def fA (t : ℝ) : ℝ := (t * log t)⁻¹

theorem sum_c (t : ℝ) : ∑ k ∈ Icc 0 ⌊t⌋₊, c k = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, sum_filter]; rfl

theorem S_sub {a b : ℝ} (hab : a ≤ b) :
    S b - S a = ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, fA k * c k := by
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  have hterm : ∀ k : ℕ, fA k * c k = if k.Prime then (1 : ℝ) / k else 0 := by
    intro k
    unfold fA c
    split_ifs with hk
    · have h1 : (1 : ℝ) < k := by exact_mod_cast hk.one_lt
      have hl : log (k : ℝ) ≠ 0 := (Real.log_pos h1).ne'
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      field_simp
    · simp
  simp_rw [hterm]
  unfold S
  rw [sum_filter, sum_filter, range_eq_Ico, range_eq_Ico, ← Ico_add_one_add_one_eq_Ioc]
  rw [← sum_Ico_consecutive _ (Nat.zero_le (⌊a⌋₊ + 1)) (by omega : ⌊a⌋₊ + 1 ≤ ⌊b⌋₊ + 1)]
  ring

theorem g_cont {a b : ℝ} (ha : 1 < a) : ContinuousOn g (Set.Icc a b) := by
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
  have : t ^ 2 * log t ^ 2 ≠ 0 := by positivity
  apply ContinuousAt.continuousWithinAt
  unfold g
  fun_prop (disch := assumption)

theorem hasDerivAt_fA {t : ℝ} (ht : 1 < t) : HasDerivAt fA (-g t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : log t ≠ 0 := (Real.log_pos ht).ne'
  have h1 : HasDerivAt (fun t => t * log t) (1 * log t + t * t⁻¹) t :=
    (hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)
  have h2 := h1.inv (mul_ne_zero ht0 hl)
  unfold fA
  convert h2 using 1
  unfold g
  field_simp
  ring

theorem deriv_fA {t : ℝ} (ht : 1 < t) : deriv fA t = -g t := (hasDerivAt_fA ht).deriv

theorem g_theta_int {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => g t * Chebyshev.theta t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have := integrableOn_mul_sum_Icc c (m := 0) (by linarith : (0 : ℝ) ≤ a)
    ((g_cont ha).integrableOn_Icc (b := b))
  simpa only [sum_c] using this

theorem g_id_int {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => g t * t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact (g_cont ha).mul continuousOn_id

theorem gR_int {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => g t * R t) volume a b := by
  have := (g_theta_int ha hab).sub (g_id_int ha hab)
  refine this.congr ?_
  intro t _
  simp only [R]; ring

/-- `∫_a^b g t · t dt = (log log b - 1/log b) - (log log a - 1/log a)`. -/
theorem integral_g_id {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, g t * t =
      (log (log b) - (log b)⁻¹) - (log (log a) - (log a)⁻¹) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => log (log t) - (log t)⁻¹)
  · intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : t ≠ 0 := by linarith
    have hl : log t ≠ 0 := (Real.log_pos ht1).ne'
    have hL := Real.hasDerivAt_log ht0
    have h := (hL.log hl).sub (hL.inv hl)
    convert h using 1
    unfold g
    field_simp
    ring
  · exact g_id_int ha hab

/-- **Abel summation identity for `Σ 1/p`**, PROVED, no cited input. -/
theorem abel_identity {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    S b - S a = log (log b) - log (log a) + R b / (b * log b) - R a / (a * log a)
      + ∫ t in a..b, g t * R t := by
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ fA t :=
    fun t ht => (hasDerivAt_fA (by linarith [ht.1])).differentiableAt
  have hint : IntegrableOn (deriv fA) (Set.Icc a b) := by
    have h1 : IntegrableOn (fun t => -g t) (Set.Icc a b) :=
      ((g_cont ha).neg).integrableOn_Icc
    exact h1.congr_fun (fun t ht => (deriv_fA (by linarith [ht.1])).symm) measurableSet_Icc
  have hA := sum_mul_eq_sub_sub_integral_mul c ha0 hab hdiff hint
  rw [sum_c, sum_c] at hA
  have hI : ∫ t in Set.Ioc a b, deriv fA t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k =
      -∫ t in a..b, g t * Chebyshev.theta t := by
    rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    simp only [sum_c, deriv_fA (by linarith [ht.1] : 1 < t)]
    ring
  rw [hI] at hA
  have hsplit : ∫ t in a..b, g t * Chebyshev.theta t =
      (∫ t in a..b, g t * t) + ∫ t in a..b, g t * R t := by
    rw [← intervalIntegral.integral_add (g_id_int ha hab) (gR_int ha hab)]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [R]; ring
  rw [hsplit, integral_g_id ha hab] at hA
  rw [S_sub hab, hA]
  have hb1 : 1 < b := by linarith
  have hla : log a ≠ 0 := (Real.log_pos ha).ne'
  have hlb : log b ≠ 0 := (Real.log_pos hb1).ne'
  have ha0' : a ≠ 0 := by linarith
  have hb0' : b ≠ 0 := by linarith
  have eb : fA b * Chebyshev.theta b = (log b)⁻¹ + R b / (b * log b) := by
    unfold fA R; field_simp; ring
  have ea : fA a * Chebyshev.theta a = (log a)⁻¹ + R a / (a * log a) := by
    unfold fA R; field_simp; ring
  rw [eb, ea]
  ring

open LeanLab.Common.ThetaWindow

/-- `log z ≥ 17` for `z ≥ 10^10`. -/
theorem seventeen_le_log {z : ℝ} (hz : 10 ^ 10 ≤ z) : 17 ≤ log z := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h : Real.exp 1 ^ 17 ≤ (2.7182818286 : ℝ) ^ 17 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 17
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  have h2 : (2.7182818286 : ℝ) ^ 17 ≤ 10 ^ 10 := by norm_num
  linarith

/-- Boundary term: `|R t/(t log t)| ≤ 0.01/log³ t`, CONDITIONAL ON `DusartThm52k2`. -/
theorem boundary_le (hD : DusartThm52k2) {t : ℝ} (ht : 7713133853 ≤ t) :
    |R t / (t * log t)| ≤ 0.01 / log t ^ 3 := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < log t := Real.log_pos (by linarith)
  have hR := hD t ht
  rw [abs_div, abs_of_pos (by positivity : 0 < t * log t), div_le_iff₀ (by positivity)]
  have : 0.01 / log t ^ 3 * (t * log t) = 0.01 * t / log t ^ 2 := by
    field_simp
  rw [this]
  exact hR

/-- The antiderivative step `∫_a^b 0.01 (1 + log t)/(t log⁴ t) dt`. -/
theorem integral_h {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 0.01 * (1 + log t) / (t * log t ^ 4) =
      (0.01 / 3 * (log a ^ 3)⁻¹ + 0.01 / 2 * (log a ^ 2)⁻¹)
        - (0.01 / 3 * (log b ^ 3)⁻¹ + 0.01 / 2 * (log b ^ 2)⁻¹) := by
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => -(0.01 / 3 * (log t ^ 3)⁻¹ + 0.01 / 2 * (log t ^ 2)⁻¹))
    (f' := fun t => 0.01 * (1 + log t) / (t * log t ^ 4)) (a := a) (b := b) ?_ ?_
  · rw [key]; ring
  · intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : t ≠ 0 := by linarith
    have hl : log t ≠ 0 := (Real.log_pos ht1).ne'
    have hL := Real.hasDerivAt_log ht0
    have h3 := ((hL.pow 3).inv (pow_ne_zero 3 hl)).const_mul (0.01 / 3 : ℝ)
    have h2 := ((hL.pow 2).inv (pow_ne_zero 2 hl)).const_mul (0.01 / 2 : ℝ)
    have h := (h3.add h2).neg
    convert h using 1
    norm_num
    field_simp
    ring
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have : t * log t ^ 4 ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)

/-- Integral term: `|∫_a^b g R| ≤ 0.01 (1/(3 log³ a) + 1/(2 log² a))`,
CONDITIONAL ON `DusartThm52k2`. -/
theorem integral_le (hD : DusartThm52k2) {a b : ℝ} (ha : 7713133853 ≤ a) (hab : a ≤ b) :
    |∫ t in a..b, g t * R t| ≤ 0.01 / 3 * (log a ^ 3)⁻¹ + 0.01 / 2 * (log a ^ 2)⁻¹ := by
  have ha1 : (1 : ℝ) < a := by linarith
  have hb1 : (1 : ℝ) < b := by linarith
  have hint := gR_int ha1 hab
  have hcont : IntervalIntegrable (fun t => 0.01 * (1 + log t) / (t * log t ^ 4)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have : t * log t ^ 4 ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  have h1 := intervalIntegral.abs_integral_le_integral_abs (f := fun t => g t * R t)
    (μ := volume) hab
  have h2 : ∫ t in a..b, |g t * R t| ≤ ∫ t in a..b, 0.01 * (1 + log t) / (t * log t ^ 4) := by
    apply intervalIntegral.integral_mono_on hab hint.abs hcont
    intro t ht
    have ht' : 7713133853 ≤ t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    have hl : 0 < log t := Real.log_pos (by linarith)
    have hR := hD t ht'
    have hg : 0 ≤ g t := by unfold g; positivity
    rw [abs_mul, abs_of_nonneg hg]
    calc g t * |R t| ≤ g t * (0.01 * t / log t ^ 2) :=
          mul_le_mul_of_nonneg_left (by simpa [R] using hR) hg
      _ = 0.01 * (1 + log t) / (t * log t ^ 4) := by
          unfold g; field_simp
  have h3 := integral_h ha1 hab
  have hb3 : 0 ≤ 0.01 / 3 * (log b ^ 3)⁻¹ + 0.01 / 2 * (log b ^ 2)⁻¹ := by
    have := Real.log_pos hb1; positivity
  linarith

/-- **Tail bound**: `|F b - F a| ≤ 0.01/log² a` for `10^10 ≤ a ≤ b`.
CONDITIONAL ON `DusartThm52k2`. -/
theorem F_diff (hD : DusartThm52k2) {a b : ℝ} (ha : 10 ^ 10 ≤ a) (hab : a ≤ b) :
    |F b - F a| ≤ 0.01 / log a ^ 2 := by
  have ha' : (7713133853 : ℝ) ≤ a := by linarith
  have hb' : (7713133853 : ℝ) ≤ b := by linarith
  have hid := abel_identity (by linarith : (1 : ℝ) < a) hab
  have hFe : F b - F a = R b / (b * log b) - R a / (a * log a) + ∫ t in a..b, g t * R t := by
    unfold F; linarith
  have e1 := boundary_le hD hb'
  have e2 := boundary_le hD ha'
  have e3 := integral_le hD ha' hab
  have hL := seventeen_le_log ha
  have hLb : log a ≤ log b := Real.log_le_log (by linarith) hab
  have hlb3 : 0.01 / log b ^ 3 ≤ 0.01 / log a ^ 3 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_left₀ (by linarith) hLb 3
  have hsum : |F b - F a| ≤ 0.01 / log a ^ 3 + 0.01 / log a ^ 3 +
      (0.01 / 3 * (log a ^ 3)⁻¹ + 0.01 / 2 * (log a ^ 2)⁻¹) := by
    rw [hFe]
    calc |R b / (b * log b) - R a / (a * log a) + ∫ t in a..b, g t * R t|
        ≤ |R b / (b * log b)| + |R a / (a * log a)| + |∫ t in a..b, g t * R t| := by
          have := abs_add_le (R b / (b * log b) - R a / (a * log a)) (∫ t in a..b, g t * R t)
          have := abs_sub (R b / (b * log b)) (R a / (a * log a))
          linarith
      _ ≤ _ := by linarith
  have hfin : 0.01 / log a ^ 3 + 0.01 / log a ^ 3 +
      (0.01 / 3 * (log a ^ 3)⁻¹ + 0.01 / 2 * (log a ^ 2)⁻¹) ≤ 0.01 / log a ^ 2 := by
    set L := log a with hLdef
    have hL0 : 0 < L := by linarith
    have hu : 0 < (L ^ 2)⁻¹ := by positivity
    have hv : L⁻¹ ≤ (17 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hL
    have e3 : (L ^ 3)⁻¹ = (L ^ 2)⁻¹ * L⁻¹ := by rw [← mul_inv, ← pow_succ]
    simp only [div_eq_mul_inv, e3]
    nlinarith [mul_le_mul_of_nonneg_left hv hu.le]
  linarith

/-- `F x` converges as `x → ∞`, CONDITIONAL ON `DusartThm52k2`. -/
theorem F_cauchy (hD : DusartThm52k2) : CauchySeq F := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  refine ⟨max (10 ^ 10) (Real.exp (1 / ε)), fun n hn => ?_⟩
  set N := max (10 ^ 10) (Real.exp (1 / ε)) with hNdef
  have hN : (10 : ℝ) ^ 10 ≤ N := le_max_left _ _
  have hNe : Real.exp (1 / ε) ≤ N := le_max_right _ _
  have hd := F_diff hD hN hn
  rw [Real.dist_eq]
  have hL := seventeen_le_log hN
  have hLe : 1 / ε ≤ log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hNe
  have h1 : 0.01 / log N ^ 2 ≤ 0.01 / log N := by
    apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
    nlinarith
  have h2 : 0.01 / log N < ε := by
    rw [div_lt_iff₀ (by linarith)]
    have : 1 ≤ ε * log N := by
      have := mul_le_mul_of_nonneg_left hLe hε.le
      rwa [mul_one_div_cancel hε.ne'] at this
    linarith
  linarith

/-- `F x → B`, CONDITIONAL ON `DusartThm52k2`. -/
theorem tendsto_F (hD : DusartThm52k2) : Tendsto F atTop (𝓝 B) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (F_cauchy hD)
  unfold B
  rwa [hL.limUnder_eq]

/-- **Explicit Mertens second theorem**: `|Σ_{p ≤ x} 1/p - log log x - B| ≤ 0.01/log² x` for
`x ≥ 10^10`, with `B` the limit. CONDITIONAL ON `DusartThm52k2`. -/
theorem mertens_explicit (hD : DusartThm52k2) {x : ℝ} (hx : 10 ^ 10 ≤ x) :
    |S x - log (log x) - B| ≤ 0.01 / log x ^ 2 := by
  have hT := tendsto_F hD
  have hev : ∀ᶠ y in atTop, F y ∈ Set.Icc (F x - 0.01 / log x ^ 2) (F x + 0.01 / log x ^ 2) := by
    filter_upwards [eventually_ge_atTop x] with y hy
    have := F_diff hD hx hy
    rw [abs_le] at this
    constructor <;> linarith
  have hB := isClosed_Icc.mem_of_tendsto hT hev
  rw [abs_le]
  unfold F at hB
  constructor <;> linarith [hB.1, hB.2]

/-- **The lab's `RS320` form**, `Σ_{p ≤ x} 1/p < log log x + 0.26150 + 1/(2 log² x)` for
`x ≥ 10^10`. CONDITIONAL ON `DusartThm52k2` and `BLe`. -/
theorem RS320_form (hD : DusartThm52k2) (hB : BLe) :
    ∀ x : ℝ, 10 ^ 10 ≤ x →
      ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / p <
        log (log x) + 0.26150 + 1 / (2 * log x ^ 2) := by
  intro x hx
  have hm := mertens_explicit hD hx
  rw [abs_le] at hm
  have hL := seventeen_le_log hx
  have hpos : 0 < log x ^ 2 := by positivity
  have : 0.01 / log x ^ 2 < 1 / (2 * log x ^ 2) := by
    rw [div_lt_div_iff₀ hpos (by positivity)]; nlinarith
  unfold BLe at hB
  show S x < _
  linarith [hm.2]

/-! ### Vacuity -/

/-- `S 3 - S 2 = 1/3`: the identity's hypotheses hold at `a = 2`, `b = 3` and its left side
is not zero. -/
theorem S_three_sub_two : S 3 - S 2 = 1 / 3 := by
  have h3 : ⌊(3 : ℝ)⌋₊ = 3 := by simp
  have h2 : ⌊(2 : ℝ)⌋₊ = 2 := by simp
  have s3 : (range (3 + 1)).filter Nat.Prime = {2, 3} := by decide
  have s2 : (range (2 + 1)).filter Nat.Prime = {2} := by decide
  unfold S
  rw [h3, h2, s3, s2]
  norm_num

end LeanLab.AlmostPrimes.MertensRS320

end

#print axioms LeanLab.AlmostPrimes.MertensRS320.abel_identity
#print axioms LeanLab.AlmostPrimes.MertensRS320.F_diff
#print axioms LeanLab.AlmostPrimes.MertensRS320.F_cauchy
#print axioms LeanLab.AlmostPrimes.MertensRS320.tendsto_F
#print axioms LeanLab.AlmostPrimes.MertensRS320.mertens_explicit
#print axioms LeanLab.AlmostPrimes.MertensRS320.RS320_form
#print axioms LeanLab.AlmostPrimes.MertensRS320.S_three_sub_two
