/-
# Pintz and Althöfer 2026: the sup bound (4.11) from Lemma 4 alone

Unit U-1209, T2 FRONTIER, idea I-0080, PC run 20261020T0902Z-22676.

Source: arXiv 2610.15559v1, read on the page in Chrome this run, from the MathML alt text.
Lemma 4: assume H_θ, 1/2 ≤ θ ≤ 2/3; for every η > 0, uniformly when (a, q) = 1,
`1 ≤ q ≤ 2√X`, `|β| ≤ 2/(q√X)`, with `z = X⁻¹ − 2πiβ`,
`F_X(a/q + β) = μ(q)/(φ(q) z) + O_{θ,η}(X^{a(θ)+η})`, (4.5). Section 4.3: off `𝔐`, Dirichlet gives
`q ≤ ⌊√X⌋`, `|α − a/q| ≤ 1/(q⌊√X⌋)`, and either `q > P` or `qX|α − a/q| > P`, so the main term is
`≪ X^{2/3+η}`; with `a(θ) ≥ 3/4` this gives (4.11).

What is here, all PROVED unconditional:
* `mainTerm`, `μ(q)/(φ(q)(X⁻¹ − 2πiβ))`; `norm_lprof_le_x`, `norm_lprof_le_beta`.
* `Vlin_on_arc`: on the arc about `a/q`, the linear model IS the main term, by `arcs_disjoint`.
* `Vlin_off_arcs`: off every arc it is `0`.
* `dirichlet_circle`: every `z ∈ ℝ/ℤ` is `a/q + β` with `1 ≤ q ≤ N`, `a < q`, `(a,q) = 1`,
  `|β| ≤ 1/(q(N + 1))`, from Mathlib's `Real.exists_rat_abs_sub_le_and_den_le`.
* `mainTerm_off_le`: off the arcs at `P = ⌊x^{1/3}⌋` the main term is at most `2x^{3/4}`, by
  `16φ(q)⁴ ≥ q³`, a cruder route than the paper's `X^{2/3+η}` that suffices since `a(θ) ≥ 3/4`.
* `Lemma4Prop θ`, the paper's Lemma 4 for the lab's `F_{x,x²}`, as a Prop, NOT proved.
* `sup_of_lemma4`: `Lemma4Prop θ → SupBound θ` for `1/2 ≤ θ ≤ 2/3`.
* `theorem3_of_lemma4`, `five_eighths_of_lemma4`: Theorem 3 CONDITIONAL ON Lemma 4 only.

KNOWN mathematics, the paper's route. AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.PintzAlthofer2026Sup
import LeanLab.VanDerCorput1939.Totient

namespace LeanLab.ExceptionalSet.PintzAlthofer2026Lemma4

open Finset Real MeasureTheory AddCircle LeanLab.ExceptionalSet.PintzAlthofer2026
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.PintzAlthofer2026Cube LeanLab.ExceptionalSet.PintzAlthofer2026Linear
open LeanLab.ExceptionalSet.PintzAlthofer2026Sup

attribute [local instance] Classical.propDecidable

noncomputable section

local notation "𝕋" => AddCircle (1 : ℝ)

/-- Lemma 4's main term `μ(q)/(φ(q)(X⁻¹ − 2πiβ))`. -/
def mainTerm (X : ℝ) (q : ℕ) (β : ℝ) : ℂ :=
  (((ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) : ℝ) : ℂ) * lprof X β

theorem norm_den_sq (X β : ℝ) :
    ‖(((1 / X : ℝ) : ℂ) - ((2 * π * β : ℝ) : ℂ) * Complex.I)‖ ^ 2 = (1 / X) ^ 2 + (2 * π * β) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

theorem norm_lprof_eq (X β : ℝ) (hX : 0 < X) :
    ‖lprof X β‖ = 1 / Real.sqrt ((1 / X) ^ 2 + (2 * π * β) ^ 2) := by
  unfold lprof
  rw [norm_div, norm_one, ← norm_den_sq X β, Real.sqrt_sq (norm_nonneg _)]

theorem norm_lprof_le_x {X : ℝ} (hX : 0 < X) (β : ℝ) : ‖lprof X β‖ ≤ X := by
  rw [norm_lprof_eq X β hX]
  have h1 : 1 / X ≤ Real.sqrt ((1 / X) ^ 2 + (2 * π * β) ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (2 * π * β)])
  have h0 : 0 < 1 / X := by positivity
  rw [div_le_iff₀ (lt_of_lt_of_le h0 h1)]
  calc (1 : ℝ) = X * (1 / X) := by field_simp
    _ ≤ X * Real.sqrt ((1 / X) ^ 2 + (2 * π * β) ^ 2) := mul_le_mul_of_nonneg_left h1 hX.le

theorem norm_lprof_le_beta {X : ℝ} (hX : 0 < X) {β : ℝ} (hβ : β ≠ 0) :
    ‖lprof X β‖ ≤ 1 / (2 * π * |β|) := by
  rw [norm_lprof_eq X β hX]
  have hb : 0 < 2 * π * |β| := by have := abs_pos.2 hβ; positivity
  have h1 : 2 * π * |β| ≤ Real.sqrt ((1 / X) ^ 2 + (2 * π * β) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    have : (2 * π * |β|) ^ 2 = (2 * π * β) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring
    nlinarith [sq_nonneg (1 / X)]
  exact one_div_le_one_div_of_le hb h1

theorem norm_mainTerm_le (X : ℝ) (q : ℕ) (hq : 1 ≤ q) (β : ℝ) :
    ‖mainTerm X q β‖ ≤ ‖lprof X β‖ / q.totient := by
  unfold mainTerm
  have ht : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos ht]
  have hμ : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right ht]
  nlinarith [norm_nonneg (lprof X β), abs_nonneg (ArithmeticFunction.moebius q : ℝ)]

/-! ### The linear model on and off the arcs -/

theorem coe_add_sub (u β : ℝ) : (((u + β : ℝ)) : 𝕋) - ((u : ℝ) : 𝕋) = ((β : ℝ) : 𝕋) := by
  rw [AddCircle.coe_add]; abel

/-- **`Vlin_on_arc`**: on the arc about `a/q`, `V_X = μ(q)/(φ(q)(X⁻¹ − 2πiβ))`. -/
theorem Vlin_on_arc {X P : ℝ} (hX : 0 < X) (hPX : 2 * P ^ 2 < X) {Q : ℕ} (hQP : (Q : ℝ) ≤ P)
    {q a : ℕ} (hi : (⟨q, a⟩ : Σ _ : ℕ, ℕ) ∈ arcIdx Q) {β : ℝ}
    (hβ : β ∈ Set.Ioc (-(P / (q * X))) (P / (q * X))) (hδ : P / (q * X) ≤ 1 / 2) :
    Vlin X P Q ((((a : ℝ) / q + β : ℝ)) : 𝕋) = mainTerm X q β := by
  set z : 𝕋 := ((((a : ℝ) / q + β : ℝ)) : 𝕋)
  have hz : ((β : ℝ) : 𝕋) = z - (((a : ℝ) / q : ℝ) : 𝕋) := (coe_add_sub _ _).symm
  unfold Vlin
  rw [Finset.sum_eq_single (⟨q, a⟩ : Σ _ : ℕ, ℕ)]
  · unfold linTerm mainTerm
    simp only
    rw [← hz]
    congr 1
    unfold hLin
    have hmem : β ∈ Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
      simp only [Set.mem_Ioc] at hβ ⊢; constructor <;> linarith [hβ.1, hβ.2]
    rw [AddCircle.liftIoc_coe_apply hmem]
    unfold gLin; rw [Set.indicator_of_mem hβ]
  · intro j hj hji
    by_contra hne
    unfold linTerm at hne
    obtain ⟨β', hβ', hβz'⟩ := hLin_support (right_ne_zero_of_mul hne)
    obtain ⟨q', a'⟩ := j
    simp only [arcIdx, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_range] at hi hj
    have hqP : (q : ℝ) ≤ P := le_trans (by exact_mod_cast hi.1.2) hQP
    have hq'P : (q' : ℝ) ≤ P := le_trans (by exact_mod_cast hj.1.2) hQP
    obtain ⟨h1, h2⟩ := arcs_disjoint hX hPX hi.1.1 hj.1.1 hqP hq'P hi.2.1 hj.2.1 hi.2.2 hj.2.2
      hβ hβ' hz hβz'
    subst h1; subst h2
    exact hji rfl
  · intro h; exact absurd hi h

/-- The point `z` lies on some arc of `arcIdx Q`. -/
def OnArc (X P : ℝ) (Q : ℕ) (z : 𝕋) : Prop :=
  ∃ i ∈ arcIdx Q, ∃ β ∈ Set.Ioc (-(P / (i.1 * X))) (P / (i.1 * X)),
    ((β : ℝ) : 𝕋) = z - (((i.2 : ℝ) / i.1 : ℝ) : 𝕋)

/-- **`Vlin_off_arcs`**: off every arc the linear model is `0`. -/
theorem Vlin_off_arcs {X P : ℝ} {Q : ℕ} {z : 𝕋} (h : ¬ OnArc X P Q z) : Vlin X P Q z = 0 := by
  unfold Vlin
  apply Finset.sum_eq_zero
  intro i hi
  by_contra hne
  unfold linTerm at hne
  obtain ⟨β, hβ, hβz⟩ := hLin_support (right_ne_zero_of_mul hne)
  exact h ⟨i, hi, β, hβ, hβz⟩

/-! ### Dirichlet on the circle -/

theorem intCast_circle_zero (m : ℤ) : (((m : ℝ)) : 𝕋) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]; exact ⟨m, by simp⟩

/-- **`dirichlet_circle`**: every `z` is `a/q + β` with `1 ≤ q ≤ N`, `a < q`, `(a, q) = 1` and
`|β| ≤ 1/(q(N + 1))`. -/
theorem dirichlet_circle (N : ℕ) (hN : 0 < N) (z : 𝕋) :
    ∃ q a : ℕ, ∃ β : ℝ, 1 ≤ q ∧ q ≤ N ∧ a < q ∧ Nat.Coprime a q ∧
      |β| ≤ 1 / ((N + 1) * q) ∧ z = (((a : ℝ) / q + β : ℝ) : 𝕋) := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hN
  set q := r.den
  have hq : 0 < q := r.den_pos
  set a : ℕ := (r.num % (q : ℤ)).toNat
  have hmod0 : 0 ≤ r.num % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
  have hmodlt : r.num % (q : ℤ) < q := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
  have ha : (a : ℤ) = r.num % (q : ℤ) := Int.toNat_of_nonneg hmod0
  refine ⟨q, a, α - r, hq, hden, by omega, ?_, ?_, ?_⟩
  · -- coprimality
    have hc : Nat.Coprime r.num.natAbs q := r.reduced
    rw [Nat.coprime_iff_gcd_eq_one, ← Int.gcd_natCast_natCast, ha, Int.gcd_emod,
      Int.gcd_eq_natAbs]
    simpa using hc
  · exact hr
  · -- the point
    have hnum : (r : ℝ) = (a : ℝ) / q + ((r.num / (q : ℤ) : ℤ) : ℝ) := by
      have h1 : (r : ℝ) = (r.num : ℝ) / q := by
        rw [Rat.cast_def]
      have h2 : r.num = (q : ℤ) * (r.num / (q : ℤ)) + r.num % (q : ℤ) := by
        rw [Int.emod_def]; ring
      have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      rw [h1]
      have h3 : (r.num : ℝ) = (q : ℝ) * ((r.num / (q : ℤ) : ℤ) : ℝ) + (a : ℝ) := by
        have := congrArg (fun t : ℤ => (t : ℝ)) h2
        rw [this]; push_cast; rw [← ha]; push_cast; ring
      rw [h3]; field_simp; ring
    show ((α : ℝ) : 𝕋) = (((a : ℝ) / q + (α - r) : ℝ) : 𝕋)
    have : (a : ℝ) / q + (α - r) = α - ((r.num / (q : ℤ) : ℤ) : ℝ) := by rw [hnum]; ring
    rw [this, AddCircle.coe_sub, intCast_circle_zero, sub_zero]

/-! ### The main term off the arcs -/

/-- **`mainTerm_off_le`**: if `t^12 = x`, `t^4/2 ≤ P`, and either `q > P` with `t^4 ≤ q`, or
`q ≤ P` with `|β| ≥ P/(qx)`, then `‖μ(q)/(φ(q) z)‖ ≤ 2 t^9`, that is `2x^{3/4}`. -/
theorem mainTerm_off_le {x t P : ℝ} (ht : 0 < t) (htx : t ^ 12 = x) (hP : t ^ 4 / 2 ≤ P)
    {q : ℕ} (hq : 1 ≤ q) {β : ℝ}
    (hcase : (t ^ 4 ≤ q) ∨ ((q : ℝ) ≤ P ∧ P / (q * x) ≤ |β|)) :
    ‖mainTerm x q β‖ ≤ 2 * t ^ 9 := by
  have hx : 0 < x := by rw [← htx]; positivity
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hφ : (q : ℝ) ^ 3 ≤ 16 * (q.totient : ℝ) ^ 4 := by
    exact_mod_cast LeanLab.VanDerCorput1939.cube_le_totient_pow4 q (by omega)
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  refine (norm_mainTerm_le x q hq β).trans ?_
  rcases hcase with h1 | ⟨h2, h3⟩
  · -- x/φ ≤ 2t^9, by fourth powers: x⁴ = t^48 ≤ t^36 q³ ≤ 16 t^36 φ⁴
    have hl := norm_lprof_le_x hx β
    have hgoal : x ≤ 2 * t ^ 9 * q.totient := by
      have hq3 : (t ^ 4) ^ 3 ≤ (q : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
      have h4 : x ^ 4 ≤ (2 * t ^ 9 * q.totient) ^ 4 := by
        rw [← htx]
        have : (2 * t ^ 9 * (q.totient : ℝ)) ^ 4 = t ^ 36 * (16 * (q.totient : ℝ) ^ 4) := by ring
        rw [this]
        have e : (t ^ 12) ^ 4 = t ^ 36 * (t ^ 4) ^ 3 := by ring
        rw [e]
        apply mul_le_mul_of_nonneg_left (hq3.trans hφ) (by positivity)
      exact (pow_le_pow_iff_left₀ hx.le (by positivity) (by norm_num)).1 h4
    calc ‖lprof x β‖ / q.totient ≤ x / q.totient := div_le_div_of_nonneg_right hl hφ0.le
      _ ≤ 2 * t ^ 9 := by rw [div_le_iff₀ hφ0]; linarith
  · -- q x/(2π φ P) ≤ 2t^9 by fourth powers: (qx/(φP))⁴ ≤ 16 x⁴/P³ ≤ 128 t^36
    have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
    have hb0 : 0 < |β| := lt_of_lt_of_le (by positivity) h3
    have hl := norm_lprof_le_beta hx (abs_pos.1 hb0)
    have hpi : 3 < π := Real.pi_gt_three
    -- ‖lprof‖ ≤ 1/(2π|β|) ≤ qx/(2πP)
    have hl2 : ‖lprof x β‖ ≤ q * x / (2 * π * P) := by
      refine hl.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : P ≤ |β| * (q * x) := by rwa [div_le_iff₀ (by positivity)] at h3
      nlinarith
    have hkey : q * x ≤ 2 * π * P * (2 * t ^ 9) * q.totient := by
      -- fourth powers
      have hP3 : t ^ 12 / 8 ≤ P ^ 3 := by
        have := pow_le_pow_left₀ (by positivity) hP 3
        have e : (t ^ 4 / 2) ^ 3 = t ^ 12 / 8 := by ring
        linarith
      have lhs : ((q : ℝ) * x) ^ 4 = (q : ℝ) ^ 4 * x ^ 4 := by ring
      have hq4 : (q : ℝ) ^ 4 ≤ P * (16 * (q.totient : ℝ) ^ 4) := by
        have : (q : ℝ) ^ 4 = q * q ^ 3 := by ring
        rw [this]
        exact mul_le_mul h2 hφ (by positivity) hP0.le
      have h4 : ((q : ℝ) * x) ^ 4 ≤ (2 * π * P * (2 * t ^ 9) * q.totient) ^ 4 := by
        rw [lhs, ← htx]
        have rhs : (2 * π * P * (2 * t ^ 9) * (q.totient : ℝ)) ^ 4 =
            (4 * π) ^ 4 * P ^ 4 * t ^ 36 * (q.totient : ℝ) ^ 4 := by ring
        rw [rhs]
        have e1 : (q : ℝ) ^ 4 * (t ^ 12) ^ 4 ≤ P * (16 * (q.totient : ℝ) ^ 4) * (t ^ 12) ^ 4 :=
          mul_le_mul_of_nonneg_right hq4 (by positivity)
        have e2 : P * (16 * (q.totient : ℝ) ^ 4) * (t ^ 12) ^ 4 ≤
            (4 * π) ^ 4 * P ^ 4 * t ^ 36 * (q.totient : ℝ) ^ 4 := by
          have hpi4 : (128 : ℝ) ≤ (4 * π) ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hpi.le 4]
          have : P * (16 * (q.totient : ℝ) ^ 4) * (t ^ 12) ^ 4 =
              16 * (q.totient : ℝ) ^ 4 * t ^ 36 * (P * t ^ 12) := by ring
          rw [this]
          have hPt : P * t ^ 12 ≤ 8 * P ^ 4 := by nlinarith
          have : 16 * (q.totient : ℝ) ^ 4 * t ^ 36 * (P * t ^ 12) ≤
              16 * (q.totient : ℝ) ^ 4 * t ^ 36 * (8 * P ^ 4) :=
            mul_le_mul_of_nonneg_left hPt (by positivity)
          have hpos : 0 ≤ P ^ 4 * t ^ 36 * (q.totient : ℝ) ^ 4 := by positivity
          have h128 := mul_le_mul_of_nonneg_right hpi4 hpos
          have hfin : 16 * (q.totient : ℝ) ^ 4 * t ^ 36 * (8 * P ^ 4) ≤
              (4 * π) ^ 4 * P ^ 4 * t ^ 36 * (q.totient : ℝ) ^ 4 := by
            calc 16 * (q.totient : ℝ) ^ 4 * t ^ 36 * (8 * P ^ 4)
                = 128 * (P ^ 4 * t ^ 36 * (q.totient : ℝ) ^ 4) := by ring
              _ ≤ (4 * π) ^ 4 * (P ^ 4 * t ^ 36 * (q.totient : ℝ) ^ 4) := h128
              _ = (4 * π) ^ 4 * P ^ 4 * t ^ 36 * (q.totient : ℝ) ^ 4 := by ring
          linarith
        linarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h4
    calc ‖lprof x β‖ / q.totient ≤ q * x / (2 * π * P) / q.totient :=
          div_le_div_of_nonneg_right hl2 hφ0.le
      _ ≤ 2 * t ^ 9 := by
          rw [div_div, div_le_iff₀ (by positivity)]
          linarith

/-! ### Lemma 4 ⇒ (4.11) -/

/-- **The paper's Lemma 4**, for the lab's `F_{x,x²}`, as a Prop, NOT proved: for every `η > 0`
and large `x`, uniformly for `1 ≤ q ≤ 2√x`, `0 ≤ a < q`, `(a, q) = 1`, `|β| ≤ 2/(q√x)`,
`|F(a/q + β) − μ(q)/(φ(q)(x⁻¹ − 2πiβ))| ≤ K x^{a(θ)+η}`. In the paper it follows from `H_θ`. -/
def Lemma4Prop (θ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ K : ℝ, ∃ X0 : ℕ, ∀ x : ℕ, X0 ≤ x → ∀ q a : ℕ, ∀ β : ℝ,
    1 ≤ q → (q : ℝ) ≤ 2 * Real.sqrt x → a < q → Nat.Coprime a q →
    |β| ≤ 2 / (q * Real.sqrt x) →
    ‖FX x (x ^ 2) ((((a : ℝ) / q + β : ℝ)) : 𝕋) - mainTerm x q β‖ ≤ K * (x : ℝ) ^ (PintzAlthofer2026.a θ + η)

set_option maxHeartbeats 2000000 in
/-- **`sup_of_lemma4`**: the paper's Lemma 4 gives its sup bound (4.11). -/
theorem sup_of_lemma4 {θ : ℝ} (h1 : 1 / 2 ≤ θ) (h2 : θ ≤ 2 / 3) (hL : Lemma4Prop θ) :
    SupBound θ := by
  intro η hη
  obtain ⟨K, X0, hK⟩ := hL η hη
  refine ⟨K + 2, max X0 4096, fun x hx z => ?_⟩
  have hx4096 : 4096 ≤ x := le_trans (le_max_right _ _) hx
  have hxX0 : X0 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  set t := (x : ℝ) ^ ((1 : ℝ) / 12) with ht_def
  have ht0 : 0 < t := by positivity
  have htx : t ^ 12 = (x : ℝ) := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have ht4 : (x : ℝ) ^ ((1 : ℝ) / 3) = t ^ 4 := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have ht9 : t ^ 9 = (x : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hpow : (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (x : ℝ) ^ (PintzAlthofer2026.a θ + η) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [a_ge h1 h2])
  set P : ℕ := P3 x
  have hPge : t ^ 4 / 2 ≤ (P : ℝ) := by rw [← ht4]; exact P3_ge x (by omega)
  have hPle : (P : ℝ) ≤ t ^ 4 := by rw [← ht4]; exact P3_real_le x
  have hPX : 2 * (P : ℝ) ^ 2 < x := two_P3_sq_lt x (by omega)
  have hsqrt : Real.sqrt x = t ^ 6 := by
    rw [← htx, show t ^ 12 = (t ^ 6) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
  have ht2 : 2 ≤ t := LeanLab.ExceptionalSet.PintzAlthofer2026CoefLower.le_of_pow_le (m := 12)
    (by norm_num) ht0.le (by norm_num) htx (by norm_num; exact_mod_cast hx4096)
  have hP2sqrt : (P : ℝ) ≤ 2 * Real.sqrt x := by
    rw [hsqrt]; have : t ^ 4 ≤ t ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  by_cases hon : OnArc x P P z
  · -- on an arc: V is the main term, Lemma 4 applies
    obtain ⟨⟨q, a⟩, hi, β, hβ, hβz⟩ := hon
    have hi' := hi
    simp only [arcIdx, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_range] at hi'
    have hq1 : 1 ≤ q := hi'.1.1
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hqP : (q : ℝ) ≤ P := by exact_mod_cast hi'.1.2
    simp only at hβ hβz
    have hz : z = (((a : ℝ) / q + β : ℝ) : 𝕋) := by
      rw [AddCircle.coe_add, hβz]; abel
    have hδ : (P : ℝ) / (q * x) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    rw [hz, Vlin_on_arc hx0 hPX le_rfl hi hβ hδ]
    have hβabs : |β| ≤ 2 / (q * Real.sqrt x) := by
      have hb : |β| ≤ (P : ℝ) / (q * x) := abs_le.2 ⟨by linarith [hβ.1], hβ.2⟩
      refine hb.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
      have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
      have h1 : (P : ℝ) * Real.sqrt x ≤ 2 * x := by
        have := mul_le_mul_of_nonneg_right hP2sqrt hs0.le
        nlinarith
      calc (P : ℝ) * (q * Real.sqrt x) = q * ((P : ℝ) * Real.sqrt x) := by ring
        _ ≤ q * (2 * x) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * (q * x) := by ring
    have := hK x hxX0 q a β hq1 (hqP.trans hP2sqrt) hi'.2.1 hi'.2.2 hβabs
    have hK0 : 0 ≤ (x : ℝ) ^ (PintzAlthofer2026.a θ + η) := by positivity
    have hexp : (K + 2) * (x : ℝ) ^ (PintzAlthofer2026.a θ + η) =
        K * (x : ℝ) ^ (PintzAlthofer2026.a θ + η) + 2 * (x : ℝ) ^ (PintzAlthofer2026.a θ + η) := by ring
    linarith
  · -- off the arcs: V = 0, F = main term + error, main term ≤ 2x^{3/4}
    rw [Vlin_off_arcs hon, sub_zero]
    set N := Nat.sqrt x
    have hN : 0 < N := Nat.sqrt_pos.2 (by omega)
    obtain ⟨q, a, β, hq1, hqN, haq, hcop, hβ, hz⟩ := dirichlet_circle N hN z
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hNs : (N : ℝ) ≤ Real.sqrt x := Real.nat_sqrt_le_real_sqrt
    have hNs' : Real.sqrt x < N + 1 := Real.real_sqrt_lt_nat_sqrt_succ
    have hq2 : (q : ℝ) ≤ 2 * Real.sqrt x := by
      have : (q : ℝ) ≤ N := by exact_mod_cast hqN
      have : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
      linarith
    have hβ2 : |β| ≤ 2 / (q * Real.sqrt x) := by
      refine hβ.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have herr := hK x hxX0 q a β hq1 hq2 haq hcop hβ2
    -- the case split
    have hcase : (t ^ 4 ≤ q) ∨ ((q : ℝ) ≤ P ∧ (P : ℝ) / (q * x) ≤ |β|) := by
      by_cases hqP : q ≤ P
      · right
        refine ⟨by exact_mod_cast hqP, ?_⟩
        by_contra hlt
        push_neg at hlt
        apply hon
        refine ⟨⟨q, a⟩, ?_, β, ?_, ?_⟩
        · simp only [arcIdx, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter,
            Finset.mem_range]
          exact ⟨⟨hq1, hqP⟩, haq, hcop⟩
        · simp only [Set.mem_Ioc]
          constructor
          · linarith [neg_abs_le β]
          · linarith [le_abs_self β]
        · simp only; rw [hz, coe_add_sub]
      · left
        push_neg at hqP
        have h1 : (P : ℝ) + 1 ≤ q := by exact_mod_cast hqP
        have h2 : t ^ 4 < (P : ℝ) + 1 := by
          rw [← ht4]; exact Nat.lt_floor_add_one _
        linarith
    have hM := mainTerm_off_le ht0 htx hPge hq1 hcase
    rw [hz]
    calc ‖FX x (x ^ 2) ((((a : ℝ) / q + β : ℝ)) : 𝕋)‖
        ≤ ‖FX x (x ^ 2) ((((a : ℝ) / q + β : ℝ)) : 𝕋) - mainTerm x q β‖ + ‖mainTerm x q β‖ := by
          have := norm_add_le (FX x (x ^ 2) ((((a : ℝ) / q + β : ℝ)) : 𝕋) - mainTerm x q β)
            (mainTerm x q β)
          simpa using this
      _ ≤ K * (x : ℝ) ^ (PintzAlthofer2026.a θ + η) + 2 * (x : ℝ) ^ (PintzAlthofer2026.a θ + η) := by
          rw [ht9] at hM; linarith
      _ = (K + 2) * (x : ℝ) ^ (PintzAlthofer2026.a θ + η) := by ring

/-- Theorem 3 of Pintz-Althöfer, CONDITIONAL ON the paper's Lemma 4 only. -/
theorem theorem3_of_lemma4 {θ : ℝ} (h1 : 1 / 2 ≤ θ) (h2 : θ ≤ 2 / 3) (hL : Lemma4Prop θ) :
    ∀ ε : ℝ, 0 < ε → PowerBound (g θ + ε) :=
  theorem3_of_sup h1 h2 (sup_of_lemma4 h1 h2 hL)

/-- θ = 5/8, CONDITIONAL ON `Lemma4Prop (5/8)` only: `E(X) ≪ X^{25/44+ε}`. -/
theorem five_eighths_of_lemma4 (hL : Lemma4Prop (5 / 8)) :
    ∀ ε : ℝ, 0 < ε → PowerBound (25 / 44 + ε) :=
  five_eighths_of_sup (sup_of_lemma4 (by norm_num) (by norm_num) hL)

/-! ### Vacuity -/

/-- Lemma 4's range is not empty: `q = 1`, `a = 0`, `β = 0` fit for every `x ≥ 1`. -/
example (x : ℕ) (hx : 1 ≤ x) : (1 : ℝ) ≤ 2 * Real.sqrt x := by
  have : (1 : ℝ) ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hx)
  linarith

end

end LeanLab.ExceptionalSet.PintzAlthofer2026Lemma4
