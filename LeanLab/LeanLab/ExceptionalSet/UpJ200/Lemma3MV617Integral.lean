import LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Split
import LeanLab.ExceptionalSet.GammaTail465

/-!
# Re split of the LEAF `mv_617_tilde_integral` of `Lemma3MV617Split`

Burst burst-20261122, unit mv617, step mv617tilde_split-integral, run by a Claude cloud session.

Source P0015, Montgomery and Vaughan 1975, read from the page images of `papers/P0015.pdf`,
journal pages 361 to 365. The parent leaf is display (6.1̃7) with `Ĩ(n)` the integral of page 364.
The split follows MV's order of work in the exceptional case.

* DEFINITIONS, each a display of P0015: `tauInd`, the Gauss sum `τ(χ̃χ₀)` of the character mod `q`
  induced by `χ̃`, page 361 and (6.2̃); `ramanujanInd`, the twisted sum `c_{χ̃χ₀}(-n)` of (6.4̃);
  `excWeight` and `crossWeight`, the coefficients of the first two terms of (6.4̃); `arcTt` and
  `arcTTt`, the arc integrals of (6.4̃); `ItildeInt` and `Jtilde`, the integrals `Ĩ(n)`, `J̃(n)` of
  page 364.
* LEAF `mv_64_tilde_remainder`, HARD: (6.1) to (6.9) with (6.2̃), (6.4̃), (6.6̃), (6.7̃): `R₁(n)`
  is the sum over `q ≤ P` of the three main arc terms, up to `n φ(n)⁻¹ (X^{1/2} W + W²)`.
* LEAF `mv_610_tilde_sq` and `mv_610_tilde_cross`, MEDIUM: (6.1̃0), the arc integrals of `T̃²` and
  `T T̃` are `Ĩ(n) + O(qQ)` and `J̃(n) + O(qQ)`.
* PROVED `mv_618_tilde`, formerly LEAF EASY: (6.18), `|Ĩ(n)| ≤ X`, `|J̃(n)| ≤ X`, by orthogonality.
* LEAF `mv_619_weights`, MEDIUM: the termwise bound behind (6.19) and the display after it,
  `|τ(χ̃χ₀)² φ(q)⁻² c_q(-n)| + |μ(q) c_{χ̃χ₀}(-n) τ(χ̃χ₀) φ(q)⁻²| ≪ r̃ φ(q)⁻¹ φ(q/(q,n))⁻¹`.
* LEAF `mv_616_tilde`, MEDIUM: (6.1̃6), the exceptional singular series.
* LEAF `mv_620`, MEDIUM: (6.20), the cross singular series.
* LEAF `mv_615_absorbed`, HARD, carrying a QUESTION: the non exceptional errors (6.13) and (6.14),
  which MV bound by `X^{1+δ} P⁻¹`, absorbed in the envelope of the parent leaf. See the notes file.
* REUSED, PROVED: `Lemma2MVSplit.mv_arc_main_611` for (6.11), `Lemma2MVSplit.mv_singular_series_616`
  for (6.16), `Lemma2MVSplit.norm_sum_sub_tsum_le`, `Supply465.gammaTwo_summable`.
* PROVED from these, no other sorry: `mv_617_tilde_integral_of_steps`, whose type is checked equal
  to `type_of% @Lemma3MV617Split.mv_617_tilde_integral`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral

open Real Finset Filter
open LeanLab.ExceptionalSet.U1539 (R1 eC)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (singSeries)
open LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082 (twistedSing)
open LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected (singularSeries)
open LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit
  (T mainWeight arcIntegral ramanujan mv_arc_main_611 mv_singular_series_616
    norm_sum_sub_tsum_le mainWeight_zero)
open LeanLab.ExceptionalSet.UpJ200.Lemma3MVSplit (Ttilde mvWtilde)

/-! ### Definitions, each a display of P0015 -/

/-- P0015 page 361 and display (6.2̃): the Gauss sum `τ(χ̃χ₀) = Σ_{a mod q} χ̃χ₀(a) e(a/q)` of the
character mod `q` induced by `χ̃` mod `r̃`, defined when `r̃ ∣ q`; zero otherwise, so that the
exceptional terms of (6.2̃) and (6.4̃) are absent when `r̃ ∤ q`. -/
noncomputable def tauInd {r : ℕ} (χ : DirichletCharacter ℂ r) (q : ℕ) : ℂ :=
  if h : r ∣ q ∧ q ≠ 0 then
    haveI : NeZero q := ⟨h.2⟩
    gaussSum (DirichletCharacter.changeLevel h.1 χ) ZMod.stdAddChar
  else 0

/-- P0015 display (6.4̃), second term: `c_{χ̃χ₀}(-n) = Σ_{a mod q} χ̃χ₀(a) e(-an/q)`, defined when
`r̃ ∣ q`. -/
noncomputable def ramanujanInd {r : ℕ} (χ : DirichletCharacter ℂ r) (q n : ℕ) : ℂ :=
  if h : r ∣ q then
    ∑ a ∈ range q, DirichletCharacter.changeLevel h χ (a : ZMod q) * eC (-((a : ℝ) * n / q))
  else 0

/-- P0015 display (6.4̃), first term coefficient: `τ(χ̃χ₀)² φ(q)⁻² c_q(-n)`. -/
noncomputable def excWeight {r : ℕ} (χ : DirichletCharacter ℂ r) (q n : ℕ) : ℂ :=
  tauInd χ q ^ 2 / (q.totient : ℂ) ^ 2 * ramanujan q (-(n : ℤ))

/-- P0015 display (6.4̃), second term coefficient without the factor 2:
`μ(q) c_{χ̃χ₀}(-n) τ(χ̃χ₀) φ(q)⁻²`. -/
noncomputable def crossWeight {r : ℕ} (χ : DirichletCharacter ℂ r) (q n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℤ) : ℂ) * ramanujanInd χ q n * tauInd χ q /
    (q.totient : ℂ) ^ 2

/-- P0015 display (6.4̃), first integral: `∫_{-1/qQ}^{1/qQ} T̃(η)² e(-nη) dη`, `1/qQ = P/(qX)`. -/
noncomputable def arcTt (β P X : ℝ) (q n : ℕ) : ℂ :=
  ∫ η in (-(P / (q * X)))..(P / (q * X)), Ttilde β P X η ^ 2 * eC (-(η * n))

/-- P0015 display (6.4̃), second integral: `∫_{-1/qQ}^{1/qQ} T(η) T̃(η) e(-nη) dη`. -/
noncomputable def arcTTt (β P X : ℝ) (q n : ℕ) : ℂ :=
  ∫ η in (-(P / (q * X)))..(P / (q * X)), T P X η * Ttilde β P X η * eC (-(η * n))

/-- P0015 page 364: `Ĩ(n) = ∫_0^1 T̃(η)² e(-nη) dη`. -/
noncomputable def ItildeInt (β P X : ℝ) (n : ℕ) : ℂ :=
  ∫ η in (0 : ℝ)..1, Ttilde β P X η ^ 2 * eC (-(η * n))

/-- P0015 page 364: `J̃(n) = ∫_0^1 T(η) T̃(η) e(-nη) dη`. -/
noncomputable def Jtilde (β P X : ℝ) (n : ℕ) : ℂ :=
  ∫ η in (0 : ℝ)..1, T P X η * Ttilde β P X η * eC (-(η * n))

/-! ### Elementary facts about the definitions, PROVED -/

lemma tauInd_of_not_dvd {r : ℕ} (χ : DirichletCharacter ℂ r) {q : ℕ} (h : ¬ r ∣ q) :
    tauInd χ q = 0 := dif_neg (fun h' => h h'.1)

lemma tauInd_zero {r : ℕ} (χ : DirichletCharacter ℂ r) : tauInd χ 0 = 0 :=
  dif_neg (fun h' => h'.2 rfl)

lemma excWeight_of_tau {r : ℕ} (χ : DirichletCharacter ℂ r) {q : ℕ} (n : ℕ)
    (h : tauInd χ q = 0) : excWeight χ q n = 0 := by
  simp [excWeight, h]

lemma crossWeight_of_tau {r : ℕ} (χ : DirichletCharacter ℂ r) {q : ℕ} (n : ℕ)
    (h : tauInd χ q = 0) : crossWeight χ q n = 0 := by
  simp [crossWeight, h]

lemma singSeries_natCast (n : ℕ) : singSeries (n : ℤ) = singularSeries n := by
  unfold singSeries singularSeries
  congr 1
  funext p
  simp only [Int.natCast_dvd_natCast]

/-! ### Orthogonality on `[0,1]`, PROVED, used for (6.18) -/

/-- P0015 page 364: `e` is additive. PROVED. -/
theorem eC_add (a b : ℝ) : eC a * eC b = eC (a + b) := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- Continuity of `η ↦ e(ηc)`. PROVED. -/
theorem cont_eC (c : ℝ) : Continuous fun η : ℝ => eC (η * c) := by
  unfold eC; fun_prop

/-- Orthogonality of `e(kη)` on `[0,1]`. PROVED. -/
theorem int01_eC (k : ℤ) :
    ∫ η in (0 : ℝ)..1, eC (η * k) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [eC]
  · have hc : (2 * π * Complex.I * k : ℂ) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [Complex.I_ne_zero, hpi, this]
    have hfun : (fun η : ℝ => eC (η * k)) =
        fun η : ℝ => Complex.exp ((2 * π * Complex.I * k) * η) := by
      funext η; unfold eC; congr 1; push_cast; ring
    rw [hfun, integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * π * Complex.I * k * ((1 : ℝ) : ℂ)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I k
      rw [← this]; congr 1; push_cast; ring
    rw [h1]; simp

/-- P0015 page 364, as in (6.7): orthogonality for a product of two weighted sums. PROVED. -/
theorem int01_prod (S S' : Finset ℕ) (a b : ℕ → ℂ) (n : ℕ) :
    ∫ η in (0 : ℝ)..1, (∑ k ∈ S, a k * eC (η * k)) * (∑ l ∈ S', b l * eC (η * l)) *
        eC (-(η * n)) =
      ∑ k ∈ S, ∑ l ∈ S', a k * b l * (if k + l = n then 1 else 0) := by
  have hexp : ∀ η : ℝ, (∑ k ∈ S, a k * eC (η * k)) * (∑ l ∈ S', b l * eC (η * l)) *
      eC (-(η * n)) = ∑ k ∈ S, ∑ l ∈ S', a k * b l * eC (η * (((k : ℤ) + l - n : ℤ) : ℝ)) := by
    intro η
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    have : eC (η * k) * eC (η * l) * eC (-(η * n)) = eC (η * (((k : ℤ) + l - n : ℤ) : ℝ)) := by
      rw [eC_add, eC_add]; congr 1; push_cast; ring
    rw [← this]; ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum]
  swap
  · intro i _
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ fun j _ => continuous_const.mul (cont_eC _)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_finsetSum]
  swap
  · intro j _
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (cont_eC _)
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [intervalIntegral.integral_const_mul, int01_eC]
  congr 2; apply propext; omega

/-- With coefficients of size at most one, the integral is at most `#S`. PROVED. -/
theorem norm_int01_prod_le (S S' : Finset ℕ) (a b : ℕ → ℂ) (n : ℕ)
    (ha : ∀ k ∈ S, ‖a k‖ ≤ 1) (hb : ∀ l ∈ S', ‖b l‖ ≤ 1) :
    ‖∫ η in (0 : ℝ)..1, (∑ k ∈ S, a k * eC (η * k)) * (∑ l ∈ S', b l * eC (η * l)) *
        eC (-(η * n))‖ ≤ S.card := by
  rw [int01_prod]
  refine (norm_sum_le _ _).trans ?_
  rw [card_eq_sum_ones, Nat.cast_sum]
  refine sum_le_sum fun k hk => ?_
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ l ∈ S', ‖a k * b l * (if k + l = n then (1 : ℂ) else 0)‖ ≤
      if l = n - k ∧ k ≤ n then 1 else 0 := by
    intro l hl
    by_cases h : k + l = n
    · rw [if_pos h, if_pos ⟨by omega, by omega⟩, mul_one, norm_mul]
      calc ‖a k‖ * ‖b l‖ ≤ 1 * 1 :=
            mul_le_mul (ha k hk) (hb l hl) (norm_nonneg _) zero_le_one
        _ = 1 := by ring
    · rw [if_neg h, mul_zero, norm_zero]; split_ifs <;> norm_num
  refine (sum_le_sum h1).trans ?_
  rw [Finset.sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  push_cast
  have : (S'.filter (fun l => l = n - k ∧ k ≤ n)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    simp only [mem_filter] at hx hy
    omega
  exact_mod_cast this

/-- `T̃` as a weighted sum, page 361. PROVED. -/
theorem Ttilde_eq (β P X η : ℝ) : Ttilde β P X η =
    ∑ k ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, (-(((k : ℝ) ^ (β - 1) : ℝ) : ℂ)) * eC (η * k) := by
  simp [Ttilde, neg_mul, sum_neg_distrib]

/-- `T` as a weighted sum, page 361. PROVED. -/
theorem T_eq (P X η : ℝ) : T P X η = ∑ k ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, (1 : ℂ) * eC (η * k) := by
  simp [T]

/-- The coefficients `n^{β̃-1}` lie in `[0,1]` for `β̃ ≤ 1`. PROVED. -/
theorem coef_le (β P X : ℝ) (hβ : β ≤ 1) :
    ∀ k ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, ‖(-(((k : ℝ) ^ (β - 1) : ℝ) : ℂ))‖ ≤ 1 := by
  intro k hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by have := (mem_Ioc.mp hk).1; omega)
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos hk1 (by linarith)

/-- `#(P, X] ≤ X`. PROVED. -/
theorem card_le (P X : ℝ) (hX : 0 ≤ X) : ((Ioc ⌊P⌋₊ ⌊X⌋₊).card : ℝ) ≤ X := by
  rw [Nat.card_Ioc]
  exact le_trans (by exact_mod_cast Nat.sub_le _ _) (Nat.floor_le hX)


/-! ### Leaves -/

/-- LEAF: P0015 displays (6.1) to (6.9) with the exceptional additions (6.2̃), (6.4̃), (6.6̃) and
(6.7̃), pages 361 to 364, class HARD. For `α ∈ 𝔐(q,a)` expand `S(α)` by characters, (6.1), with
`S(χ̃χ₀,η) = T̃(η) + W(χ̃χ₀,η)`, page 361; square and integrate over the arcs of modulus `q`, (6.4)
augmented by (6.4̃). The main terms are `μ(q)² φ(q)⁻² c_q(-n) ∫T²e`, `τ(χ̃χ₀)² φ(q)⁻² c_q(-n) ∫T̃²e`
and `2μ(q) c_{χ̃χ₀}(-n) τ(χ̃χ₀) φ(q)⁻² ∫T T̃ e`; all terms with a factor `W(χ,η)` are bounded by
Cauchy Schwarz with (6.7) and (6.7̃), (6.6) and (6.6̃), and Lemma 5.5, giving (6.8) with the `W`
of the exceptional case, the lab's `mvWtilde`. The integrals over arcs are not yet evaluated. -/
theorem mv_64_tilde_remainder : ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 < C ∧
    ∀ θ : ℝ, 0 < θ → θ < 6 / 100 → ∃ P₀ : ℝ, ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
    ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ → SelectedRealZero a (X ^ θ) r →
    ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
      χ.LFunction β = 0 →
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
        ‖R1 (X ^ θ) X (n : ℤ) - ∑ q ∈ Icc 1 ⌊X ^ θ⌋₊,
            (mainWeight q n * arcIntegral (X ^ θ) X q n +
              excWeight χ q n * arcTt β (X ^ θ) X q n +
              2 * crossWeight χ q n * arcTTt β (X ^ θ) X q n)‖ ≤
          C * ((n : ℝ) / (n.totient : ℝ)) *
            (mvWtilde β (X ^ θ) X χ * Real.sqrt X + mvWtilde β (X ^ θ) X χ ^ 2) := by
  sorry

/-- LEAF: P0015 display (6.1̃0), page 364, first integral, class MEDIUM. By partial summation
`T̃(η) ≪ ‖η‖⁻¹`, since the coefficients `n^{β̃-1}` lie in `(0,1]` and decrease for `β̃ ≤ 1`; so
`∫_{1/qQ}^{1/2} |T̃|² ≪ qQ` and the arc integral of `T̃² e(-nη)` is `Ĩ(n) + O(qQ)`, `qQ = qX/P`. -/
theorem mv_610_tilde_sq : ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ < 6 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ β : ℝ, β ≤ 1 →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ X ^ θ → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
        ‖arcTt β (X ^ θ) X q n - ItildeInt β (X ^ θ) X n‖ ≤ C * q * (X / X ^ θ) := by
  sorry

/-- LEAF: P0015 display (6.1̃0), page 364, second integral, class MEDIUM. With `T(η) ≪ ‖η‖⁻¹` and
`T̃(η) ≪ ‖η‖⁻¹`, `∫_{1/qQ}^{1/2} |T T̃| ≪ qQ`, so the arc integral of `T T̃ e(-nη)` is
`J̃(n) + O(qQ)`. -/
theorem mv_610_tilde_cross : ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ < 6 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ β : ℝ, β ≤ 1 →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ X ^ θ → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
        ‖arcTTt β (X ^ θ) X q n - Jtilde β (X ^ θ) X n‖ ≤ C * q * (X / X ^ θ) := by
  sorry

/-- PROVED, formerly a LEAF of class EASY: P0015 display (6.18), page 364. "As in (6.7)": by
orthogonality `∫_0^1 T̃² e(-nη) = Σ_{k+l=n} k^{β̃-1} l^{β̃-1}` and
`∫_0^1 T T̃ e(-nη) = -Σ_{k+l=n} l^{β̃-1}`, sums over `P < k, l ≤ X`, with at most `X` terms of
size at most one, for `β̃ ≤ 1`. -/
theorem mv_618_tilde : ∀ β P X : ℝ, β ≤ 1 → 0 ≤ X → ∀ n : ℕ,
    ‖ItildeInt β P X n‖ ≤ X ∧ ‖Jtilde β P X n‖ ≤ X := by
  intro β P X hβ hX n
  constructor
  · unfold ItildeInt
    simp_rw [sq, Ttilde_eq]
    exact (norm_int01_prod_le _ _ _ _ n (coef_le β P X hβ) (coef_le β P X hβ)).trans
      (card_le P X hX)
  · unfold Jtilde
    simp_rw [Ttilde_eq, T_eq]
    exact (norm_int01_prod_le _ _ _ _ n (fun k _ => by simp) (coef_le β P X hβ)).trans
      (card_le P X hX)

/-- LEAF: the termwise bound used in P0015 display (6.19) and in the display after it, page 365,
class MEDIUM. For `r̃ ∣ q`: `|τ(χ̃χ₀)|² ≤ r̃` by Lemma 5.2, `|c_q(-n)| ≤ φ(q) φ(q/(q,n))⁻¹` by
(5.2), and for squarefree `q` the same bound times `r̃^{1/2}` for `c_{χ̃χ₀}(-n)`; MV "treat these
as in (6.13)". -/
theorem mv_619_weights : ∃ C : ℝ, 0 < C ∧
    ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r), χ.IsPrimitive → χ ^ 2 = 1 →
      ∀ q n : ℕ, 1 ≤ q → r ∣ q → 1 ≤ n →
        ‖excWeight χ q n‖ + ‖crossWeight χ q n‖ ≤
          C * ((r : ℝ) * (1 / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)))) := by
  sorry

/-- LEAF: P0015 display (6.1̃6), page 365, class MEDIUM, by Lemma 5.1 and (5.2):
`𝔖̃(n) = Σ_{q ≥ 1, r̃ ∣ q} τ(χ̃χ₀)² c_q(-n) φ(q)⁻²
  = χ̃(-1) μ(r̃/(r̃,n)) r̃ φ(r̃)⁻¹ φ(r̃/(r̃,n))⁻¹ ∏_{p∤r̃, p∤n} (1 - (p-1)⁻²) ∏_{p∤r̃, p∣n} (1 + (p-1)⁻¹)`,
the series absolutely convergent; the product is the lab's `twistedSing`, P0082 display (12). -/
theorem mv_616_tilde : ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
    χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → ∀ n : ℕ, 1 ≤ n →
      Summable (fun q : ℕ => ‖excWeight χ q n‖) ∧
        HasSum (fun q : ℕ => excWeight χ q n) ((twistedSing χ (n : ℤ) : ℝ) : ℂ) := by
  sorry

/-- LEAF: P0015 display (6.20), page 365, class MEDIUM:
`Σ_{q ≥ 1, r̃ ∣ q} μ(q) τ(χ̃χ₀) c_{χ̃χ₀}(-n) φ(q)⁻² = μ(r̃) χ̃(n) r̃ φ(r̃)⁻² ∏ ∏
  ≪ χ̃(n)² r̃ φ(r̃)⁻² n φ(n)⁻¹`, the series absolutely convergent. -/
theorem mv_620 : ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
    χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → ∀ n : ℕ, 1 ≤ n →
      Summable (fun q : ℕ => ‖crossWeight χ q n‖) ∧
        ‖∑' q : ℕ, crossWeight χ q n‖ ≤
          C * ‖χ ((n : ℤ) : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 *
            ((n : ℝ) / (n.totient : ℝ)) := by
  sorry

/-- LEAF: the non exceptional errors (6.13) and (6.14) of P0015 page 363, `Q Σ_{q≤P} μ(q)² φ(q)⁻²
|c_q(n)| q` and `n Σ_{q>P} μ(q)² φ(q)⁻² |c_q(n)|`, absorbed in the error envelope of (6.1̃7) as
P0082 page 358 asserts: "avoid divisor estimates producing an `X^ε` (these occur only in (6.19)
and the formula thereafter)". Class HARD. QUESTION: MV bound these two errors only by
`X^{1+δ}P⁻¹`, which P0082 absorbs into its last error term through the lower bound
`1 - β̃ ≫ r̃^{-1/2} (log r̃)^{-2}` of its display (10); the envelope here, kept from the parent leaf,
has `W` in place of that term and no `X^{1+δ}P⁻¹`, so this step may not follow from MV. -/
theorem mv_615_absorbed : ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 < C ∧
    ∀ θ : ℝ, 0 < θ → θ < 6 / 100 → ∃ P₀ : ℝ, ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
    ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ → SelectedRealZero a (X ^ θ) r →
    ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
      χ.LFunction β = 0 →
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X → Even n →
        (X / X ^ θ) * ∑ q ∈ Icc 1 ⌊X ^ θ⌋₊, ‖mainWeight q n‖ * q +
            (n : ℝ) * ∑' q : ℕ, (if X ^ θ < (q : ℝ) then ‖mainWeight q n‖ else 0) ≤
          C * X * divisorError r (X ^ θ) (n : ℤ) +
          C * X * ‖χ ((n : ℤ) : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 *
            ((n : ℝ) / (n.totient : ℝ)) +
          C * ((n : ℝ) / (n.totient : ℝ)) *
            (mvWtilde β (X ^ θ) X χ * Real.sqrt X + mvWtilde β (X ^ θ) X χ ^ 2) := by
  sorry

/-! ### Arithmetic helpers, PROVED -/

/-- The infinite tail of a weight bounded as in `mv_619_weights` is bounded by the second
envelope of `divisorError`, P0015 page 365 the display after (6.19). PROVED. -/
lemma tail_weight_le (f : ℕ → ℂ) (r : ℕ) (P : ℝ) (hP : 0 ≤ P) (n : ℕ) (hn : 1 ≤ n)
    (Cw : ℝ) (hCw : 0 ≤ Cw) (hf0 : f 0 = 0) (hfz : ∀ q, ¬ r ∣ q → f q = 0)
    (hfb : ∀ q, 1 ≤ q → r ∣ q →
      ‖f q‖ ≤ Cw * ((r : ℝ) * (1 / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)))))
    (hs : Summable (fun q => ‖f q‖)) :
    ∑' q : ℕ, (if q ∈ Icc 1 ⌊P⌋₊ then 0 else ‖f q‖) ≤
      Cw * ((r : ℝ) * ∑' q : ℕ, if P < (q : ℝ) ∧ r ∣ q then
        1 / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)) else 0) := by
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hg := LeanLab.ExceptionalSet.Supply465.gammaTwo_summable r P (n : ℤ) hn0
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun q => ?_) ?_ ((hg.mul_left (r : ℝ)).mul_left Cw)
  · have hg0 : 0 ≤ (if P < (q : ℝ) ∧ r ∣ q then
        1 / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)) else 0) := by
      split_ifs <;> positivity
    have hR0 : 0 ≤ Cw * ((r : ℝ) * (if P < (q : ℝ) ∧ r ∣ q then
        1 / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)) else 0)) := by
      positivity
    by_cases hq0 : q = 0
    · subst hq0; simp [hf0]
    by_cases hqs : q ∈ Icc 1 ⌊P⌋₊
    · rw [if_pos hqs]; exact hR0
    rw [if_neg hqs]
    have hPq : P < (q : ℝ) := by
      by_contra h
      push_neg at h
      exact hqs (mem_Icc.mpr ⟨by omega, Nat.le_floor h⟩)
    by_cases hrq : r ∣ q
    · rw [if_pos ⟨hPq, hrq⟩]; exact hfb q (by omega) hrq
    · rw [hfz q hrq, norm_zero]; exact hR0
  · exact hs.of_nonneg_of_le (fun q => by split_ifs <;> simp)
      (fun q => by split_ifs <;> simp)

/-- The finite sum over the arcs of a weight bounded as in `mv_619_weights` is bounded by the
first envelope of `divisorError`, P0015 display (6.19). PROVED. -/
lemma fin_weight_le (f : ℕ → ℝ) (r : ℕ) (P X : ℝ) (hP : 0 ≤ P) (hX : 0 ≤ X) (n : ℕ)
    (Cw : ℝ) (hfz : ∀ q ∈ Icc 1 ⌊P⌋₊, ¬ r ∣ q → f q = 0)
    (hfb : ∀ q ∈ Icc 1 ⌊P⌋₊, r ∣ q →
      f q ≤ Cw * ((r : ℝ) * (1 / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ))))) :
    (X / P) * ∑ q ∈ Icc 1 ⌊P⌋₊, f q * q ≤
      Cw * X * ((r : ℝ) / P * ∑ q ∈ (Icc 1 ⌊P⌋₊).filter (fun q => r ∣ q),
        (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ))) := by
  have h1 : ∑ q ∈ Icc 1 ⌊P⌋₊, f q * q ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, (if r ∣ q then
      Cw * ((r : ℝ) * (1 / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)))) * q
      else 0) := by
    refine sum_le_sum (fun q hq => ?_)
    by_cases hrq : r ∣ q
    · rw [if_pos hrq]
      exact mul_le_mul_of_nonneg_right (hfb q hq hrq) (Nat.cast_nonneg _)
    · rw [if_neg hrq, hfz q hq hrq, zero_mul]
  rw [← sum_filter] at h1
  have h2 : ∑ q ∈ (Icc 1 ⌊P⌋₊).filter (fun q => r ∣ q),
      Cw * ((r : ℝ) * (1 / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)))) * q =
      Cw * (r : ℝ) * ∑ q ∈ (Icc 1 ⌊P⌋₊).filter (fun q => r ∣ q),
        (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)) := by
    rw [mul_sum]; refine sum_congr rfl (fun q _ => by ring)
  rw [h2] at h1
  calc (X / P) * ∑ q ∈ Icc 1 ⌊P⌋₊, f q * q ≤ (X / P) * (Cw * (r : ℝ) *
        ∑ q ∈ (Icc 1 ⌊P⌋₊).filter (fun q => r ∣ q),
          (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hX hP)
    _ = _ := by ring

lemma norm_add7_le {E : Type*} [SeminormedAddCommGroup E] (a b c d e f g : E) :
    ‖a + b + c + d + e + f + g‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ := by
  refine (norm_add_le _ _).trans ?_; gcongr
  refine (norm_add_le _ _).trans ?_; gcongr
  refine (norm_add_le _ _).trans ?_; gcongr
  refine (norm_add_le _ _).trans ?_; gcongr
  refine (norm_add_le _ _).trans ?_; gcongr
  exact norm_add_le _ _

/-! ### Assembly, PROVED -/

/-- Real arithmetic for the assembly: the non exceptional pieces. PROVED. -/
lemma arith_two (C2 a b x y E : ℝ) (hC2 : 0 ≤ C2) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : x ≤ C2 * a) (hy : y ≤ b) (hE : a + b ≤ E) : x + y ≤ (C2 + 1) * E := by
  nlinarith

/-- Real arithmetic for the assembly: the arc errors (6.1̃0) summed by (6.19). PROVED. -/
lemma arith_three (C5 C6 Cw A B U x y : ℝ) (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6)
    (hx : x ≤ C5 * A) (hy : y ≤ 2 * C6 * B) (hA : A ≤ Cw * U) (hB : B ≤ Cw * U) :
    x + y ≤ (C5 + 2 * C6) * Cw * U := by
  nlinarith [mul_le_mul_of_nonneg_left hA hC5, mul_le_mul_of_nonneg_left hB hC6]

/-- Real arithmetic for the assembly: collecting the constants. PROVED. -/
lemma arith_final (C1 C2 Ca C5 C6 Cw C7 u1 u2 v w : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hCa : 0 ≤ Ca) (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6) (hCw : 0 ≤ Cw) (hC7 : 0 ≤ C7)
    (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    C1 * w + (C2 + 1) * (Ca * (u1 + u2) + Ca * v + Ca * w) + (C5 + 2 * C6) * Cw * u1 +
        Cw * u2 + (2 * C7 * v + 2 * Cw * u2) ≤
      (C1 + (C2 + 1) * Ca + (C5 + 2 * C6 + 3) * Cw + 2 * C7) * (u1 + u2) +
        (C1 + (C2 + 1) * Ca + (C5 + 2 * C6 + 3) * Cw + 2 * C7) * v +
        (C1 + (C2 + 1) * Ca + (C5 + 2 * C6 + 3) * Cw + 2 * C7) * w := by
  have k2 : 0 ≤ (C5 + 2 * C6 + 3) * Cw := by positivity
  nlinarith [mul_nonneg hC1 hu1, mul_nonneg hC1 hu2, mul_nonneg hC1 hv,
    mul_nonneg k2 hv, mul_nonneg k2 hw, mul_nonneg hC7 hu1, mul_nonneg hC7 hu2,
    mul_nonneg hC7 hw, mul_nonneg (mul_nonneg hC5 hCw) hu2, mul_nonneg (mul_nonneg hC6 hCw) hu2,
    mul_nonneg hCw hu1]

set_option maxHeartbeats 1000000 in
/-- PROVED from the leaves above and the proved pieces (6.11) and (6.16) of `Lemma2MVSplit`: the
parent LEAF `Lemma3MV617Split.mv_617_tilde_integral`, P0015 display (6.1̃7). -/
theorem mv_617_tilde_integral_of_steps :
    type_of% @Lemma3MV617Split.mv_617_tilde_integral := by
  intro a ha
  obtain ⟨C1, hC1, h1⟩ := mv_64_tilde_remainder a ha
  obtain ⟨Ca, hCa, hA⟩ := mv_615_absorbed a ha
  obtain ⟨C2, hC2, h2⟩ := mv_arc_main_611
  obtain ⟨C5, hC5, h5⟩ := mv_610_tilde_sq
  obtain ⟨C6, hC6, h6⟩ := mv_610_tilde_cross
  obtain ⟨Cw, hCw, hw⟩ := mv_619_weights
  obtain ⟨C7, hC7, h7⟩ := mv_620
  refine ⟨C1 + (C2 + 1) * Ca + (C5 + 2 * C6 + 3) * Cw + 2 * C7, by positivity,
    fun θ hθ hθ1 => ?_⟩
  obtain ⟨PA, hPA⟩ := h1 θ hθ hθ1
  obtain ⟨PB, hPB⟩ := hA θ hθ hθ1
  obtain ⟨X2, hX2⟩ := h2 (θ / 6) (by positivity) (by linarith)
  have h6θ : 6 * (θ / 6) = θ := by ring
  simp only [h6θ] at hX2
  obtain ⟨X5, hX5⟩ := h5 θ hθ hθ1
  obtain ⟨X6, hX6⟩ := h6 θ hθ hθ1
  set Xm := max (max X2 X5) (max X6 1) with hXm
  refine ⟨max (max PA PB) (Xm ^ θ), ?_⟩
  intro X hX hPX r hr1 hr hrP hsel hNZ χ β hprim hsq hne hβ1 hβ2 hL m hm hmX hev
  have hPA' : PA ≤ X ^ θ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hPX
  have hPB' : PB ≤ X ^ θ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hPX
  have hXm1 : 1 ≤ Xm := le_trans (le_max_right _ _) (le_max_right _ _)
  have hXmX : Xm ≤ X :=
    (Real.rpow_le_rpow_iff (by linarith) hX.le hθ).mp (le_trans (le_max_right _ _) hPX)
  have hX2' : X2 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXmX
  have hX5' : X5 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXmX
  have hX6' : X6 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hXmX
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ m)
  have hn : 1 ≤ n := by exact_mod_cast hm
  have hnX : (n : ℝ) ≤ X := by exact_mod_cast hmX
  have hevn : Even n := by exact_mod_cast hev
  have e1 : ((n : ℤ) : ℝ) = (n : ℝ) := Int.cast_natCast n
  have e2 : (n : ℤ).toNat = n := Int.toNat_natCast n
  rw [e2, e1]
  -- notation
  set P := X ^ θ with hPdef
  have hP0 : 0 ≤ P := Real.rpow_nonneg hX.le θ
  set s := Icc 1 ⌊P⌋₊ with hs
  set M := (n : ℝ) / (n.totient : ℝ) with hMdef
  set Wt := mvWtilde β P X χ
  set I := ItildeInt β P X n with hIdef
  set J := Jtilde β P X n with hJdef
  set tS := twistedSing χ (n : ℤ) with htS
  set D1 := (r : ℝ) / P * ∑ q ∈ s.filter (fun q => r ∣ q),
    (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)) with hD1
  set D2 := (r : ℝ) * ∑' q : ℕ, (if P < (q : ℝ) ∧ r ∣ q then
    1 / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)) else 0) with hD2
  have hD : divisorError r P (n : ℤ) = D1 + D2 := rfl
  have hD1n : 0 ≤ D1 := by
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun q _ => by positivity)
  have hD2n : 0 ≤ D2 := by
    apply mul_nonneg (by positivity)
    exact tsum_nonneg (fun q => by split_ifs <;> positivity)
  have hM0 : 0 ≤ M := by positivity
  have hIgoal : (∫ η in (0 : ℝ)..1, Ttilde β P X η ^ 2 * eC (-(η * (n : ℝ)))) = I := rfl
  rw [hIgoal]
  -- the pieces
  have hT1 := hPA X hX hPA' r hr1 hr hrP hsel hNZ χ β hprim hsq hne hβ1 hβ2 hL n hn hnX
  have hAbs := hPB X hX hPB' r hr1 hr hrP hsel hNZ χ β hprim hsq hne hβ1 hβ2 hL n hn hnX hevn
  obtain ⟨h618I, h618J⟩ := mv_618_tilde β P X hβ2.le hX.le n
  obtain ⟨hsE, hhE⟩ := mv_616_tilde r hNZ χ hprim hsq hne n hn
  obtain ⟨hsK, hK7⟩ := h7 r hNZ χ hprim hsq hne n hn
  have hwq := hw r hNZ χ hprim hsq
  have hqP : ∀ q ∈ s, 1 ≤ q ∧ (q : ℝ) ≤ P := fun q hq =>
    ⟨(mem_Icc.mp hq).1, le_trans (by exact_mod_cast (mem_Icc.mp hq).2) (Nat.floor_le hP0)⟩
  have hEz : ∀ q, ¬ r ∣ q → excWeight χ q n = 0 :=
    fun q h => excWeight_of_tau χ n (tauInd_of_not_dvd χ h)
  have hKz : ∀ q, ¬ r ∣ q → crossWeight χ q n = 0 :=
    fun q h => crossWeight_of_tau χ n (tauInd_of_not_dvd χ h)
  have hE0 : excWeight χ 0 n = 0 := excWeight_of_tau χ n (tauInd_zero χ)
  have hK0 : crossWeight χ 0 n = 0 := crossWeight_of_tau χ n (tauInd_zero χ)
  have hEb : ∀ q, 1 ≤ q → r ∣ q → ‖excWeight χ q n‖ ≤
      Cw * ((r : ℝ) * (1 / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)))) :=
    fun q hq hrq => le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hwq q n hq hrq hn)
  have hKb : ∀ q, 1 ≤ q → r ∣ q → ‖crossWeight χ q n‖ ≤
      Cw * ((r : ℝ) * (1 / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)))) :=
    fun q hq hrq => le_trans (le_add_of_nonneg_left (norm_nonneg _)) (hwq q n hq hrq hn)
  -- T2
  have hT2 : ‖∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ))‖ ≤
      C2 * ((X / P) * ∑ q ∈ s, ‖mainWeight q n‖ * q) := by
    calc ‖∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ))‖
        ≤ ∑ q ∈ s, ‖mainWeight q n‖ * (C2 * q * (X / P)) := by
          refine (norm_sum_le _ _).trans (sum_le_sum (fun q hq => ?_))
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (hX2 X hX2' q (hqP q hq).1 (hqP q hq).2 n hn hnX) (norm_nonneg _)
      _ = C2 * ((X / P) * ∑ q ∈ s, ‖mainWeight q n‖ * q) := by
          rw [mul_sum, mul_sum]; refine sum_congr rfl (fun q _ => by ring)
  -- T3
  have hT3 : ‖(n : ℂ) * ((∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ))‖ ≤
      (n : ℝ) * ∑' q : ℕ, (if P < (q : ℝ) then ‖mainWeight q n‖ else 0) := by
    obtain ⟨hsum, hhas⟩ := mv_singular_series_616 n hn
    have ht := norm_sum_sub_tsum_le hsum hhas s
    have hcongr : ∑' q : ℕ, (if q ∈ s then 0 else ‖mainWeight q n‖) =
        ∑' q : ℕ, (if P < (q : ℝ) then ‖mainWeight q n‖ else 0) := by
      refine tsum_congr (fun q => ?_)
      by_cases hq0 : q = 0
      · subst hq0; simp [mainWeight_zero]
      · have hiff : q ∈ s ↔ ¬ P < (q : ℝ) := by
          rw [hs, mem_Icc, not_lt]
          constructor
          · rintro ⟨_, h⟩; exact le_trans (by exact_mod_cast h) (Nat.floor_le hP0)
          · intro h; exact ⟨by omega, Nat.le_floor h⟩
        by_cases hq : q ∈ s
        · simp [hq, hiff.mp hq]
        · have : P < (q : ℝ) := by by_contra h; exact hq (hiff.mpr h)
          simp [hq, this]
    rw [hcongr] at ht
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  -- T4 and T6
  have hT4 : ‖∑ q ∈ s, excWeight χ q n * (arcTt β P X q n - I)‖ ≤
      C5 * ((X / P) * ∑ q ∈ s, ‖excWeight χ q n‖ * q) := by
    calc _ ≤ ∑ q ∈ s, ‖excWeight χ q n‖ * (C5 * q * (X / P)) := by
          refine (norm_sum_le _ _).trans (sum_le_sum (fun q hq => ?_))
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (hX5 X hX5' β hβ2.le q (hqP q hq).1 (hqP q hq).2 n hn hnX) (norm_nonneg _)
      _ = _ := by rw [mul_sum, mul_sum]; refine sum_congr rfl (fun q _ => by ring)
  have hT6 : ‖2 * ∑ q ∈ s, crossWeight χ q n * (arcTTt β P X q n - J)‖ ≤
      2 * C6 * ((X / P) * ∑ q ∈ s, ‖crossWeight χ q n‖ * q) := by
    rw [norm_mul, Complex.norm_ofNat, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc _ ≤ ∑ q ∈ s, ‖crossWeight χ q n‖ * (C6 * q * (X / P)) := by
          refine (norm_sum_le _ _).trans (sum_le_sum (fun q hq => ?_))
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (hX6 X hX6' β hβ2.le q (hqP q hq).1 (hqP q hq).2 n hn hnX) (norm_nonneg _)
      _ = _ := by rw [mul_sum, mul_sum]; refine sum_congr rfl (fun q _ => by ring)
  have hEfin : (X / P) * ∑ q ∈ s, ‖excWeight χ q n‖ * q ≤ Cw * X * D1 :=
    fin_weight_le (fun q => ‖excWeight χ q n‖) r P X hP0 hX.le n Cw
      (fun q _ h => by simp [hEz q h]) (fun q hq h => hEb q (hqP q hq).1 h)
  have hKfin : (X / P) * ∑ q ∈ s, ‖crossWeight χ q n‖ * q ≤ Cw * X * D1 :=
    fin_weight_le (fun q => ‖crossWeight χ q n‖) r P X hP0 hX.le n Cw
      (fun q _ h => by simp [hKz q h]) (fun q hq h => hKb q (hqP q hq).1 h)
  -- T5
  have hT5 : ‖I * ((∑ q ∈ s, excWeight χ q n) - ((tS : ℝ) : ℂ))‖ ≤ X * (Cw * D2) := by
    rw [norm_mul]
    have ht := norm_sum_sub_tsum_le hsE hhE s
    have ht2 := tail_weight_le (fun q => excWeight χ q n) r P hP0 n hn Cw hCw.le hE0 hEz hEb hsE
    exact mul_le_mul h618I (ht.trans ht2) (norm_nonneg _) hX.le
  -- T7
  have hT7 : ‖2 * J * ∑ q ∈ s, crossWeight χ q n‖ ≤
      2 * X * (C7 * ‖χ ((n : ℤ) : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M + Cw * D2) := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have hK := hsK.of_norm.hasSum
    have ht := norm_sum_sub_tsum_le hsK hK s
    have ht2 := tail_weight_le (fun q => crossWeight χ q n) r P hP0 n hn Cw hCw.le hK0 hKz hKb hsK
    have hsplit : ∑ q ∈ s, crossWeight χ q n =
        (∑' q, crossWeight χ q n) + ((∑ q ∈ s, crossWeight χ q n) - ∑' q, crossWeight χ q n) := by
      ring
    have hnorm : ‖∑ q ∈ s, crossWeight χ q n‖ ≤
        C7 * ‖χ ((n : ℤ) : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M + Cw * D2 := by
      rw [hsplit]
      exact (norm_add_le _ _).trans (add_le_add hK7 (ht.trans ht2))
    have hJ := mul_le_mul h618J hnorm (norm_nonneg _) hX.le
    refine le_trans (le_of_eq (mul_assoc _ _ _)) ?_
    refine le_trans (mul_le_mul_of_nonneg_left hJ (by norm_num)) (le_of_eq ?_)
    ring
  -- the identity
  have hS3 : ∑ q ∈ s, (mainWeight q n * arcIntegral P X q n + excWeight χ q n * arcTt β P X q n +
        2 * crossWeight χ q n * arcTTt β P X q n) =
      ∑ q ∈ s, mainWeight q n * arcIntegral P X q n + ∑ q ∈ s, excWeight χ q n * arcTt β P X q n +
        2 * ∑ q ∈ s, crossWeight χ q n * arcTTt β P X q n := by
    rw [sum_add_distrib, sum_add_distrib, mul_sum]
    congr 1
    refine sum_congr rfl (fun q _ => by ring)
  have hA2 : ∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ)) =
      ∑ q ∈ s, mainWeight q n * arcIntegral P X q n - (∑ q ∈ s, mainWeight q n) * (n : ℂ) := by
    rw [sum_mul, ← sum_sub_distrib]; refine sum_congr rfl (fun q _ => by ring)
  have hE4 : ∑ q ∈ s, excWeight χ q n * (arcTt β P X q n - I) =
      ∑ q ∈ s, excWeight χ q n * arcTt β P X q n - (∑ q ∈ s, excWeight χ q n) * I := by
    rw [sum_mul, ← sum_sub_distrib]; refine sum_congr rfl (fun q _ => by ring)
  have hK6 : ∑ q ∈ s, crossWeight χ q n * (arcTTt β P X q n - J) =
      ∑ q ∈ s, crossWeight χ q n * arcTTt β P X q n - (∑ q ∈ s, crossWeight χ q n) * J := by
    rw [sum_mul, ← sum_sub_distrib]; refine sum_congr rfl (fun q _ => by ring)
  have hsplit : R1 P X (n : ℤ) - (((n : ℝ) * singularSeries n : ℝ) : ℂ) - I * ((tS : ℝ) : ℂ) =
      (R1 P X (n : ℤ) - ∑ q ∈ s, (mainWeight q n * arcIntegral P X q n +
          excWeight χ q n * arcTt β P X q n + 2 * crossWeight χ q n * arcTTt β P X q n)) +
        ∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ)) +
        (n : ℂ) * ((∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ)) +
        ∑ q ∈ s, excWeight χ q n * (arcTt β P X q n - I) +
        I * ((∑ q ∈ s, excWeight χ q n) - ((tS : ℝ) : ℂ)) +
        2 * ∑ q ∈ s, crossWeight χ q n * (arcTTt β P X q n - J) +
        2 * J * ∑ q ∈ s, crossWeight χ q n := by
    rw [hS3, hA2, hE4, hK6]
    push_cast
    ring
  -- the norm bound
  set WT := Wt * Real.sqrt X + Wt ^ 2 with hWT
  set v := X * ‖χ ((n : ℤ) : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M with hv
  have hv0 : 0 ≤ v := by positivity
  have hw0 : 0 ≤ M * WT := by
    have h0 := le_trans (norm_nonneg _) hT1
    have : C1 * M * WT = C1 * (M * WT) := by ring
    rw [this] at h0
    exact (mul_nonneg_iff_of_pos_left hC1).mp h0
  have hkey : ‖R1 P X (n : ℤ) - (((n : ℝ) * singularSeries n : ℝ) : ℂ) - I * ((tS : ℝ) : ℂ)‖ ≤
      (C1 + (C2 + 1) * Ca + (C5 + 2 * C6 + 3) * Cw + 2 * C7) * X * (D1 + D2) +
        (C1 + (C2 + 1) * Ca + (C5 + 2 * C6 + 3) * Cw + 2 * C7) * v +
        (C1 + (C2 + 1) * Ca + (C5 + 2 * C6 + 3) * Cw + 2 * C7) * (M * WT) := by
    rw [hsplit]
    refine (norm_add7_le _ _ _ _ _ _ _).trans ?_
    simp only [← hPdef] at hAbs
    rw [hD] at hAbs
    have hAbs' : (X / P) * ∑ q ∈ s, ‖mainWeight q n‖ * q +
        (n : ℝ) * ∑' q : ℕ, (if P < (q : ℝ) then ‖mainWeight q n‖ else 0) ≤
        Ca * (X * (D1 + D2)) + Ca * v + Ca * (M * WT) := by
      refine hAbs.trans (le_of_eq ?_); rw [hv]; ring
    have hT1' : ‖R1 P X (n : ℤ) - ∑ q ∈ s, (mainWeight q n * arcIntegral P X q n +
          excWeight χ q n * arcTt β P X q n + 2 * crossWeight χ q n * arcTTt β P X q n)‖ ≤
        C1 * (M * WT) := hT1.trans (le_of_eq (by ring))
    have hT7' : ‖2 * J * ∑ q ∈ s, crossWeight χ q n‖ ≤ 2 * C7 * v + 2 * Cw * (X * D2) :=
      hT7.trans (le_of_eq (by rw [hv]; ring))
    have hT5' : ‖I * ((∑ q ∈ s, excWeight χ q n) - ((tS : ℝ) : ℂ))‖ ≤ Cw * (X * D2) :=
      hT5.trans (le_of_eq (by ring))
    have hXD1 : 0 ≤ X * D1 := mul_nonneg hX.le hD1n
    have hXD2 : 0 ≤ X * D2 := mul_nonneg hX.le hD2n
    have hm0 : 0 ≤ (X / P) * ∑ q ∈ s, ‖mainWeight q n‖ * q :=
      mul_nonneg (div_nonneg hX.le hP0) (sum_nonneg (fun q _ => by positivity))
    have hT45 : ‖∑ q ∈ s, excWeight χ q n * (arcTt β P X q n - I)‖ +
        ‖2 * ∑ q ∈ s, crossWeight χ q n * (arcTTt β P X q n - J)‖ ≤
        (C5 + 2 * C6) * Cw * (X * D1) := by
      exact arith_three C5 C6 Cw _ _ (X * D1) _ _ hC5.le hC6.le hT4 hT6
        (hEfin.trans (le_of_eq (mul_assoc _ _ _))) (hKfin.trans (le_of_eq (mul_assoc _ _ _)))
    have hT23 : ‖∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ))‖ +
        ‖(n : ℂ) * ((∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ))‖ ≤
        (C2 + 1) * (Ca * (X * (D1 + D2)) + Ca * v + Ca * (M * WT)) := by
      have htail0 : 0 ≤ (n : ℝ) * ∑' q : ℕ, (if P < (q : ℝ) then ‖mainWeight q n‖ else 0) :=
        mul_nonneg (by positivity) (tsum_nonneg (fun q => by split_ifs <;> positivity))
      exact arith_two C2 _ _ _ _ _ hC2.le hm0 htail0 hT2 hT3 hAbs'
    have hfin := arith_final C1 C2 Ca C5 C6 Cw C7 (X * D1) (X * D2) v (M * WT) hC1.le hC2.le
      hCa.le hC5.le hC6.le hCw.le hC7.le hXD1 hXD2 hv0 hw0
    have hXD : X * (D1 + D2) = X * D1 + X * D2 := by ring
    rw [hXD] at hT23
    rw [mul_assoc _ X (D1 + D2), hXD]
    linarith [hT1', hT23, hT45, hT5', hT7', hfin]
  have hre : (R1 P X (n : ℤ)).re - ((n : ℝ) * singSeries (n : ℤ) + I.re * tS) =
      (R1 P X (n : ℤ) - (((n : ℝ) * singularSeries n : ℝ) : ℂ) - I * ((tS : ℝ) : ℂ)).re := by
    rw [singSeries_natCast]
    simp [Complex.sub_re, Complex.mul_re]
    ring
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans (hkey.trans (le_of_eq ?_))
  rw [hD, hv]
  ring

/-- The assembly has exactly the type of the parent leaf. -/
example : type_of% @mv_617_tilde_integral_of_steps =
    type_of% @Lemma3MV617Split.mv_617_tilde_integral := rfl

end LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral.mv_617_tilde_integral_of_steps
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral.tail_weight_le
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral.fin_weight_le
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral.mv_618_tilde
