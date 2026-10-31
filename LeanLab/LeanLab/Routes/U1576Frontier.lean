import Mathlib

/-!
# T2 FRONTIER, I-0136: the exceptional set exponent in Li-Liu's Linnik-Goldbach argument

Unit U-1576, PC run 20261027T0807Z-9485. AI wrote this Lean code, Claude, checked only by the
Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

Source. Li and Liu, "6 powers of 2 in the Linnik-Goldbach problem", arXiv 2610.15784 v1,
Proposition 5.2 with displays (49) to (55), read by WebFetch of arxiv.org/html/2610.15784 on
2026-10-27. With `G(α) = Σ_{ν ≤ L} e(2^ν α)` and `z_L = G / L`, the exceptional set is
`E_λ(L) = {α ∈ [0,1] : z_L(α) ∉ D_λ}`, display (51):
`D_λ = {x + iy : x ≤ β_λ, x² + y² ≤ r_λ / (1 + r_λ - x)}`, `r_λ = λ²/2`, display (50).
Display (53): `meas E_λ(L) ≪ e^{-ρ L}` for `ρ < I(λ)`, with `I` the Rademacher rate (49); the
authors say they do not claim `I` is best possible. Display (55): the minor arc contribution
on `E_λ` is `o(N)` when `ρ > (2σ - 1) log 2`, where `N^σ` bounds the prime sum off the major arcs.

Question. Unconditionally, Maynard-Pandey-Radziwiłł give `σ = 19/24`, so (55) needs
`ρ > (7/12) log 2 = 0.40434`. I-0083 found that K = 5 closes at C₁ = 6.7814 only for
`λ ≤ λ* = 0.78312`, where `I(λ*) = 0.34990`. Can a sharper measure exponent close the gap?

Answer, numerics notes/U-1576/pressure_M32.out. `G` is a Birkhoff sum of `e(α)` under the
doubling map, so the exact exponent is the Legendre transform of the pressure of the transfer
operator. Its infimum over the boundary of `D_{λ*}` is `0.35437`, only 1.3 percent above
`I(λ*)`, far below `0.40434`. Li-Liu's exponent is nearly sharp: no proof of (53) at `λ*` can
reach the MPR exponent. Even replacing `D_λ` by the exact sublevel set of the true rate at
`(7/12) log 2` leaves the K = 5 margin at `-0.363`, notes/U-1576/levers.out.

What is in Lean.
* `rate_le_log_two`, PROVED unconditional: for every `β < 49/50`, every admissible exponent in
  (53) is at most `log 2`, from the explicit interval `[0, 2^{-(L+5)}]` inside `E`. This is the
  trivial barrier and the vacuity instance for the named input `RateAtMost`.
* `sigma_lt_of_rate`, PROVED: if every admissible exponent is at most `ρ₀`, then (55) forces
  `σ < (1 + ρ₀ / log 2) / 2`.
* `no_mpr_route`, CONDITIONAL ON `RateAtMost β r 0.3545`, the computed pressure bound: no
  admissible exponent meets (55) at `σ = 19/24`.
* `sigma_bound_3545`, CONDITIONAL ON the same input: (55) forces `σ < 0.7558`.
-/

open Real MeasureTheory

namespace LeanLab.Routes.U1576

/-- Plain math: `G_L(α) = Σ_{ν=1}^{L} e(2^ν α)`, Li-Liu Section 5. -/
noncomputable def G (L : ℕ) (α : ℝ) : ℂ :=
  ∑ ν ∈ Finset.range L, Complex.exp (((2 * π * 2 ^ (ν + 1) * α : ℝ) : ℂ) * Complex.I)

/-- Plain math: `z_L(α) = G_L(α) / L`. -/
noncomputable def zL (L : ℕ) (α : ℝ) : ℂ := G L α / (L : ℂ)

/-- Plain math: Li-Liu display (51), `D = {z : Re z ≤ β, |z|² (1 + r - Re z) ≤ r}`, with the
paper's `β = β_λ` and `r = λ²/2` left as parameters. -/
def Dreg (β r : ℝ) : Set ℂ := {z | z.re ≤ β ∧ Complex.normSq z * (1 + r - z.re) ≤ r}

/-- Plain math: the exceptional set `E(L) = {α ∈ [0,1] : z_L(α) ∉ D}`, Prop. 5.2. -/
def Eset (β r : ℝ) (L : ℕ) : Set ℝ := {α | α ∈ Set.Icc (0 : ℝ) 1 ∧ zL L α ∉ Dreg β r}

/-- Plain math: `ρ` is an admissible exponent in display (53): `meas E(L) ≤ C e^{-ρ L}`. -/
def Admissible (β r ρ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ L : ℕ, 1 ≤ L → (volume (Eset β r L)).toReal ≤ C * exp (-ρ * L)

/-- Plain math: display (55), `ρ > (2σ - 1) log 2`. -/
def Cond55 (σ ρ : ℝ) : Prop := (2 * σ - 1) * log 2 < ρ

/-- CONDITIONAL input shape: every admissible exponent is at most `ρ₀`. The value
`ρ₀ = 0.3545` at `λ* = 0.78312` is the lab's pressure computation, not a proof. -/
def RateAtMost (β r ρ₀ : ℝ) : Prop := ∀ ρ, Admissible β r ρ → ρ ≤ ρ₀

/-- Vacuity: `ρ = 0` is admissible with `C = 1` for every region. -/
theorem admissible_zero (β r : ℝ) : Admissible β r 0 := by
  refine ⟨1, fun L _ => ?_⟩
  have hsub : Eset β r L ⊆ Set.Icc (0 : ℝ) 1 := fun a h => h.1
  have hle : volume (Eset β r L) ≤ 1 := by
    calc volume (Eset β r L) ≤ volume (Set.Icc (0 : ℝ) 1) := measure_mono hsub
      _ = 1 := by simp
  have : (volume (Eset β r L)).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle)
  simpa using this

/-- Plain math: for `0 ≤ α ≤ 2^{-(L+5)}` each term has real part at least `49/50`. -/
theorem re_term_ge (L : ℕ) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ (2 : ℝ)⁻¹ ^ (L + 5))
    (ν : ℕ) (hν : ν < L) :
    (49 / 50 : ℝ) ≤ (Complex.exp (((2 * π * 2 ^ (ν + 1) * α : ℝ) : ℂ) * Complex.I)).re := by
  rw [Complex.exp_ofReal_mul_I_re]
  set t := 2 * π * 2 ^ (ν + 1) * α with ht
  have hpow : (2 : ℝ) ^ (ν + 1) * (2 : ℝ)⁻¹ ^ (L + 5) ≤ 1 / 32 := by
    have h2 : (2 : ℝ) ^ (ν + 1) ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hν
    have : (2 : ℝ)⁻¹ ^ (L + 5) = (2 ^ L)⁻¹ * (1 / 32) := by
      rw [inv_pow, pow_add]; norm_num; ring
    rw [this]
    have hL : (0 : ℝ) < 2 ^ L := by positivity
    calc (2 : ℝ) ^ (ν + 1) * ((2 ^ L)⁻¹ * (1 / 32)) ≤ 2 ^ L * ((2 ^ L)⁻¹ * (1 / 32)) := by
          gcongr
      _ = 1 / 32 := by field_simp
  have hpos : (0 : ℝ) ≤ 2 ^ (ν + 1) := by positivity
  have hb : 2 ^ (ν + 1) * α ≤ 1 / 32 :=
    le_trans (mul_le_mul_of_nonneg_left h1 hpos) hpow
  have ht0 : 0 ≤ t := by rw [ht]; have := pi_pos; positivity
  have ht1 : t ≤ 1 / 5 := by
    have := pi_lt_d2
    rw [ht]
    have hm : 0 ≤ 2 ^ (ν + 1) * α := mul_nonneg hpos h0
    nlinarith
  nlinarith [one_sub_sq_div_two_le_cos (x := t)]

/-- Plain math: for `0 ≤ α ≤ 2^{-(L+5)}` and `L ≥ 1`, `Re z_L(α) ≥ 49/50`. -/
theorem re_zL_ge (L : ℕ) (hL : 1 ≤ L) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ (2 : ℝ)⁻¹ ^ (L + 5)) :
    (49 / 50 : ℝ) ≤ (zL L α).re := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hG : (L : ℝ) * (49 / 50) ≤ (G L α).re := by
    unfold G
    rw [Complex.re_sum]
    have := Finset.card_nsmul_le_sum (Finset.range L)
      (fun ν => (Complex.exp (((2 * π * 2 ^ (ν + 1) * α : ℝ) : ℂ) * Complex.I)).re) (49 / 50)
      (fun ν hν => re_term_ge L α h0 h1 ν (Finset.mem_range.1 hν))
    simpa [nsmul_eq_mul] using this
  have : (zL L α).re = (G L α).re / L := by
    unfold zL
    exact Complex.div_natCast_re _ _
  rw [this, le_div_iff₀ hLpos]
  linarith

/-- Plain math: `[0, 2^{-(L+5)}] ⊆ E(L)` when `β < 49/50` and `L ≥ 1`. -/
theorem interval_sub_E (β r : ℝ) (hβ : β < 49 / 50) (L : ℕ) (hL : 1 ≤ L) :
    Set.Icc (0 : ℝ) ((2 : ℝ)⁻¹ ^ (L + 5)) ⊆ Eset β r L := by
  intro α hα
  have hsmall : (2 : ℝ)⁻¹ ^ (L + 5) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  refine ⟨⟨hα.1, le_trans hα.2 hsmall⟩, ?_⟩
  intro hD
  have := re_zL_ge L hL α hα.1 hα.2
  have := hD.1
  linarith

/-- PROVED unconditional, the trivial barrier and vacuity instance of `RateAtMost`:
for `β < 49/50` every admissible exponent in display (53) is at most `log 2`. -/
theorem rate_le_log_two (β r : ℝ) (hβ : β < 49 / 50) : RateAtMost β r (log 2) := by
  intro ρ ⟨C, hC⟩
  by_contra hρ
  push Not at hρ
  set d := ρ - log 2 with hd
  have hdpos : 0 < d := by linarith
  -- lower bound: 2^{-(L+5)} ≤ C e^{-ρ L}
  have key : ∀ L : ℕ, 1 ≤ L → (2 : ℝ)⁻¹ ^ (L + 5) ≤ C * exp (-ρ * L) := by
    intro L hL
    have hsub := interval_sub_E β r hβ L hL
    have hfin : volume (Eset β r L) ≠ ⊤ := by
      apply ne_top_of_le_ne_top (b := volume (Set.Icc (0 : ℝ) 1)) (by simp)
      exact measure_mono (fun a h => h.1)
    have h1 : (volume (Set.Icc (0 : ℝ) ((2 : ℝ)⁻¹ ^ (L + 5)))).toReal ≤
        (volume (Eset β r L)).toReal := ENNReal.toReal_mono hfin (measure_mono hsub)
    rw [Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal (by positivity)] at h1
    exact le_trans h1 (hC L hL)
  -- choose L large
  obtain ⟨L, hL⟩ := exists_nat_gt (32 * |C| / d)
  have hL1 : 1 ≤ L + 1 := by omega
  have k := key (L + 1) hL1
  have e1 : (2 : ℝ)⁻¹ ^ (L + 1 + 5) = exp (-(log 2) * ((L + 1 : ℕ) : ℝ)) / 32 := by
    rw [neg_mul, exp_neg, mul_comm, exp_nat_mul, exp_log (by norm_num), inv_pow, pow_add]
    norm_num
    ring
  rw [e1] at k
  have hx : exp (-ρ * ((L + 1 : ℕ) : ℝ)) = exp (-(log 2) * ((L + 1 : ℕ) : ℝ)) *
      exp (-d * ((L + 1 : ℕ) : ℝ)) := by
    rw [← exp_add]; congr 1; rw [hd]; ring
  rw [hx] at k
  have hE : 0 < exp (-(log 2) * ((L + 1 : ℕ) : ℝ)) := exp_pos _
  have k2 : 1 ≤ 32 * C * exp (-d * ((L + 1 : ℕ) : ℝ)) := by
    have := (div_le_iff₀ (by norm_num : (0:ℝ) < 32)).1 k
    have h3 : exp (-(log 2) * ((L + 1 : ℕ) : ℝ)) * 1 ≤
        exp (-(log 2) * ((L + 1 : ℕ) : ℝ)) * (32 * C * exp (-d * ((L + 1 : ℕ) : ℝ))) := by
      nlinarith
    exact le_of_mul_le_mul_left h3 hE
  have hgrow : 1 + d * ((L + 1 : ℕ) : ℝ) ≤ exp (d * ((L + 1 : ℕ) : ℝ)) := by
    have := add_one_le_exp (d * ((L + 1 : ℕ) : ℝ)); linarith
  have k3 : exp (d * ((L + 1 : ℕ) : ℝ)) ≤ 32 * C := by
    have he : exp (-d * ((L + 1 : ℕ) : ℝ)) * exp (d * ((L + 1 : ℕ) : ℝ)) = 1 := by
      rw [← exp_add]; simp
    have hpos := exp_pos (d * ((L + 1 : ℕ) : ℝ))
    nlinarith
  have hL' : 32 * |C| < d * ((L + 1 : ℕ) : ℝ) := by
    rw [div_lt_iff₀ hdpos] at hL
    push_cast
    nlinarith
  have := le_abs_self C
  linarith

/-- PROVED: if every admissible exponent is at most `ρ₀`, then any `σ` reached through (55)
satisfies `σ < (1 + ρ₀ / log 2) / 2`. -/
theorem sigma_lt_of_rate {β r ρ₀ σ : ℝ} (h : RateAtMost β r ρ₀)
    (hσ : ∃ ρ, Admissible β r ρ ∧ Cond55 σ ρ) : σ < (1 + ρ₀ / log 2) / 2 := by
  obtain ⟨ρ, hA, hC⟩ := hσ
  have h1 := h ρ hA
  have hl : 0 < log 2 := log_pos (by norm_num)
  unfold Cond55 at hC
  have : 2 * σ - 1 < ρ₀ / log 2 := by
    rw [lt_div_iff₀ hl]; linarith
  linarith

/-- PROVED arithmetic: `(2 · 19/24 - 1) log 2 = (7/12) log 2 > 0.4043 > 0.3545`. -/
theorem mpr_threshold : (0.3545 : ℝ) < (2 * (19 / 24) - 1) * log 2 := by
  have := log_two_gt_d9
  nlinarith

/-- CONDITIONAL ON `RateAtMost β r 0.3545`, the lab's pressure computation at `λ* = 0.78312`:
no admissible exponent in (53) satisfies Li-Liu's (55) at the MPR exponent `σ = 19/24`. -/
theorem no_mpr_route {β r : ℝ} (h : RateAtMost β r 0.3545) :
    ¬ ∃ ρ, Admissible β r ρ ∧ Cond55 (19 / 24) ρ := by
  rintro ⟨ρ, hA, hC⟩
  have := h ρ hA
  unfold Cond55 at hC
  linarith [mpr_threshold]

/-- CONDITIONAL ON `RateAtMost β r 0.3545`: (55) then forces `σ < 0.7558`; Li-Liu's own
exponent `I(λ*) = 0.34990` gives `0.7524`, I-0083. -/
theorem sigma_bound_3545 {β r σ : ℝ} (h : RateAtMost β r 0.3545)
    (hσ : ∃ ρ, Admissible β r ρ ∧ Cond55 σ ρ) : σ < 0.7558 := by
  have h1 := sigma_lt_of_rate h hσ
  have hl := log_two_gt_d9
  have hl0 : 0 < log 2 := log_pos (by norm_num)
  have : 0.3545 / log 2 < 0.5116 := by
    rw [div_lt_iff₀ hl0]; nlinarith
  linarith

/-- Vacuity of the CONDITIONAL statements' shape: `RateAtMost` holds at `log 2` for the
paper's region at `λ* = 0.78312`, where `β_{λ*} ≈ 0.7277 < 49/50`; shown here at `β = 3/4`,
`r = 3/10`. -/
theorem rateAtMost_vacuity : RateAtMost (3 / 4) (3 / 10) (log 2) :=
  rate_le_log_two _ _ (by norm_num)

/-- Vacuity: an admissible exponent exists, `ρ = 0`, at the same region. -/
theorem admissible_vacuity : ∃ ρ, Admissible (3 / 4) (3 / 10) ρ := ⟨0, admissible_zero _ _⟩

end LeanLab.Routes.U1576

#print axioms LeanLab.Routes.U1576.admissible_zero
#print axioms LeanLab.Routes.U1576.re_term_ge
#print axioms LeanLab.Routes.U1576.re_zL_ge
#print axioms LeanLab.Routes.U1576.interval_sub_E
#print axioms LeanLab.Routes.U1576.rate_le_log_two
#print axioms LeanLab.Routes.U1576.sigma_lt_of_rate
#print axioms LeanLab.Routes.U1576.mpr_threshold
#print axioms LeanLab.Routes.U1576.no_mpr_route
#print axioms LeanLab.Routes.U1576.sigma_bound_3545
#print axioms LeanLab.Routes.U1576.rateAtMost_vacuity
#print axioms LeanLab.Routes.U1576.admissible_vacuity
