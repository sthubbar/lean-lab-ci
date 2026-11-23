import LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelectedDecisions
import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Singular616
import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.ArcMain611
import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Truncation613
import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Tail614
import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Gallagher42Core

/-!
# Split of `Lemma2NoExcBP` into the displays of Montgomery and Vaughan 1975

Burst burst-20261122, unit P1122-0119, run by a Claude cloud session.

Source P0082, Brüdern and Perelli 1998, page 358 Lemma 2, whose whole proof is
"Combine (6.17) and (7.1) of Montgomery & Vaughan". Source P0015, Montgomery and Vaughan,
The exceptional set in Goldbach's problem, Acta Arith. 27 (1975) 353-370, pages 355 to 366,
read from the page images of `papers/P0015.pdf`.

Notation of P0015 section 2: `P = X^{6δ}`, `Q = X^{1-6δ}`, so `1/(qQ) = P/(qX)`; the major arc
`𝔐(q,a) = [a/q - 1/(qQ), a/q + 1/(qQ)]` for `1 ≤ a ≤ q ≤ P`, `(a,q) = 1`. P0082 page 357 says its
`R₁(m)` "coincides exactly with the quantity R₁(m) used by Montgomery & Vaughan"; the lab's
`U1539.R1` is that integral, over `N ∩ [0,1]`, which equals the integral over MV's union by
periodicity.

Structure.
* LEAF `mv_remainder_66_68`: displays (6.1) to (6.9), the remainder of the major arc expansion.
* LEAF `mv_arc_main_611`: display (6.11) for one modulus.
* LEAF `mv_truncation_613`: display (6.13).
* LEAF `mv_singular_series_616`: display (6.16), the series equals the product.
* LEAF `mv_tail_614`: display (6.14).
* LEAF `mv_gallagher_lemma42_step`: the first display of section 7, from Lemma 4.2.
* LEAF `mv_gallagher_lemma43`: Lemma 4.3, Gallagher's Theorem 7, run with zero free constant `a`.
* PROVED in burst S53, session claude/ExceptionalSet-lemma2-split-p2: `mv_arc_main_611`,
  `mv_truncation_613`, `mv_tail_614`, `mv_singular_series_616`, `mv_gallagher_lemma42_step`, through
  the helper modules in `UpJ200/Lemma2MV`. `mv_remainder_66_68` is split in
  `Lemma2MV/Remainder66Split.lean` down to the one LEAF `rem66_lemma55`, P0015 Lemma 5.5.
* PROVED from the leaves: `mv_617`, display (6.17); `mv_71`, display (7.1);
  `lemma2NoExcSmallDelta_of_leaves`, P0082 Lemma 2 for small `δ`.
* PROVED sorry free: `lemma2NoExcSmallDelta_of_BP` and `leaf_absent_selected_of_small`, which gives
  the exact type of `Decomp559b.leaf_absent_selected` from the weaker named hypothesis
  `Lemma2NoExcSmallDelta`.

Why the twin `Lemma2NoExcSmallDelta`. `Lemma2NoExcBP` asks for `c₁, K` uniform over every
`0 < δ < 1/100`. P0082 page 357 does state that range, but MV prove (6.17) with (7.1) only through
Lemma 4.3, which needs `P ≤ N^{c₄}` with a small absolute `c₄`, and MV take `δ` "eventually a small
positive absolute constant", P0015 page 354. The leaf only ever uses small `δ`, so the twin asks for
the bound below some `δ₁ > 0`. See the notes file for the QUESTION.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 eC nu)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)
open LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected
  (singularSeries NoExceptionalReal Lemma2NoExcBP SingularSeriesEvenLowerBP exp_neg_le_inv
    noExceptionalReal_of_selected_one)

/-! ### Definitions, each a display of P0015 -/

/-- P0015 page 361: `T(η) = Σ_{P<n≤X} e(nη)`. -/
noncomputable def T (P X η : ℝ) : ℂ :=
  ∑ n ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, eC (η * n)

/-- P0015 display (2.3): `S(χ,η) = Σ_{P<p≤X} (log p) χ(p) e(pη)`. -/
noncomputable def Schi {q : ℕ} (P X : ℝ) (χ : DirichletCharacter ℂ q) (η : ℝ) : ℂ :=
  ∑ p ∈ (Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, (Real.log p : ℂ) * χ (p : ZMod q) * eC (η * p)

open Classical in
/-- P0015 page 361, the line before (6.2): `S(χ₀,η) = T(η) + W(χ₀,η)` and `S(χ,η) = W(χ,η)` for
`χ ≠ χ₀`. The exceptional modification `(6.2~)` is not made, so this `W` is the one of (6.2). -/
noncomputable def Wchi {q : ℕ} (P X : ℝ) (χ : DirichletCharacter ℂ q) (η : ℝ) : ℂ :=
  Schi P X χ η - if χ = 1 then T P X η else 0

/-- P0015 display (6.5), with `1/(rQ) = P/(rX)`:
`W(χ) = (∫_{-1/rQ}^{1/rQ} |W(χ,η)|² dη)^{1/2}` for `χ` of modulus `r`. -/
noncomputable def Wnorm {r : ℕ} (P X : ℝ) (χ : DirichletCharacter ℂ r) : ℝ :=
  Real.sqrt (∫ η in (-(P / (r * X)))..(P / (r * X)), ‖Wchi P X χ η‖ ^ 2)

/-- P0015 display (6.9): `W = Σ_{q≤P} Σ*_χ W(χ)`, the inner sum over primitive `χ` mod `q`. -/
noncomputable def mvW (P X : ℝ) : ℝ :=
  ∑ r ∈ Icc 1 ⌊P⌋₊, ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, Wnorm P X χ.1

/-- Ramanujan's sum `c_q(m) = Σ'_{h mod q} e(hm/q)`, P0015 page 354. -/
noncomputable def ramanujan (q : ℕ) (m : ℤ) : ℂ :=
  ∑ h ∈ (range q).filter (fun h => Nat.Coprime h q), eC ((h : ℝ) * m / q)

/-- The coefficient `μ(q)² φ(q)⁻² c_q(-n)` of the first term of P0015 display (6.4). -/
noncomputable def mainWeight (q n : ℕ) : ℂ :=
  (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) *
    ramanujan q (-(n : ℤ))

/-- The integral `∫_{-1/qQ}^{1/qQ} T(η)² e(-nη) dη` of the first term of P0015 display (6.4). -/
noncomputable def arcIntegral (P X : ℝ) (q n : ℕ) : ℂ :=
  ∫ η in (-(P / (q * X)))..(P / (q * X)), T P X η ^ 2 * eC (-(η * n))

open Classical in
/-- The sum `Σ^#_{x-h<n≤x}` of P0015 Lemma 4.3, restricted to `P < n ≤ X` as in the first display
of section 7: `χ(p) log p` at primes, minus `1` at every integer when `χ` is principal. These are
the coefficients of `W(χ,η)`. -/
noncomputable def sharpSum {r : ℕ} (P X : ℝ) (χ : DirichletCharacter ℂ r) (x h : ℝ) : ℂ :=
  ∑ n ∈ (Ioc ⌊P⌋₊ ⌊X⌋₊).filter (fun n : ℕ => x - h < (n : ℝ) ∧ (n : ℝ) ≤ x),
    ((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) - if χ = 1 then 1 else 0)

/-! ### Bridges to the helper modules of `Lemma2MV`, PROVED -/

/-- The coefficient of the first term of P0015 display (6.4) is `HeathBrown1985.gm n q`, by
`Lemma2MV.sing616_weight_eq`. -/
lemma mainWeight_eq_gm (q n : ℕ) :
    mainWeight q n = ((LeanLab.HeathBrown1985.gm n q : ℝ) : ℂ) :=
  Lemma2MV.sing616_weight_eq q n

lemma norm_mainWeight_eq (q n : ℕ) :
    ‖mainWeight q n‖ = |LeanLab.HeathBrown1985.gm n q| := by
  rw [mainWeight_eq_gm, Complex.norm_real, Real.norm_eq_abs]

open LeanLab.ExceptionalSet.UpJ200.Lemma2MV (gall42_S gall42_B gall42_gallagher)

open Classical in
/-- P0015 page 361: `W(χ,η)` is the exponential sum with the coefficients of `Σ^#`, page 366. -/
lemma gall42_Wchi_eq {r : ℕ} (P X : ℝ) (χ : DirichletCharacter ℂ r) (η : ℝ) :
    Wchi P X χ η = gall42_S (Ioc ⌊P⌋₊ ⌊X⌋₊) (fun n =>
      (if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
        if χ = 1 then 1 else 0) η := by
  unfold Wchi Schi T gall42_S
  rw [sum_filter]
  split_ifs with h
  · rw [← sum_sub_distrib]
    refine sum_congr rfl (fun n _ => ?_)
    by_cases hp : Nat.Prime n <;> simp only [hp, if_true, if_false] <;> ring
  · rw [sub_zero]
    refine sum_congr rfl (fun n _ => ?_)
    by_cases hp : Nat.Prime n <;> simp only [hp, if_true, if_false] <;> ring

open Classical in
/-- P0015 page 366: the sum `Σ^#_{m-H<n≤m}` at integer `m` and `H` is the block sum of
Lemma 4.2, page 357. -/
lemma gall42_sharp_eq {r : ℕ} (P X : ℝ) (χ : DirichletCharacter ℂ r) (m H : ℕ) :
    sharpSum P X χ (m : ℝ) (H : ℝ) = gall42_B (Ioc ⌊P⌋₊ ⌊X⌋₊) (fun n =>
      (if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
        if χ = 1 then 1 else 0) H m := by
  unfold sharpSum gall42_B
  refine sum_congr (filter_congr (fun n _ => ?_)) (fun _ _ => rfl)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by exact_mod_cast h2, ?_⟩
    have : (m : ℝ) < n + H := by linarith
    exact_mod_cast this
  · rintro ⟨h1, h2⟩
    have h1' : (n : ℝ) ≤ m := by exact_mod_cast h1
    have h2' : (m : ℝ) < n + H := by exact_mod_cast h2
    exact ⟨by linarith, h1'⟩

/-! ### The leaves -/

/-- LEAF: P0015 displays (6.1) to (6.9), pages 361 to 363, class HARD.
For `α ∈ 𝔐(q,a)` expand `S(α)` by characters, (6.1) and (6.2); square, (6.3); integrate over the
arcs of modulus `q`, (6.4); bound the second and third terms by Cauchy Schwarz with (6.7)
`∫|T|² ≤ X`, giving (6.6); group by primitive characters and apply Lemma 5.5, giving (6.8):
the remainder is `≪ n φ(n)⁻¹ (W X^{1/2} + W²)` with `W` of (6.9). Constants absolute, P0015 page
354. No zero free hypothesis is used, since `W(χ,η)` is defined without the exceptional term. -/
theorem mv_remainder_66_68 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      ‖R1 (X ^ (6 * δ)) X (n : ℤ) -
          ∑ q ∈ Icc 1 ⌊X ^ (6 * δ)⌋₊, mainWeight q n * arcIntegral (X ^ (6 * δ)) X q n‖ ≤
        C * ((n : ℝ) / (n.totient : ℝ)) *
          (mvW (X ^ (6 * δ)) X * Real.sqrt X + mvW (X ^ (6 * δ)) X ^ 2) := by
  sorry

/-- PROVED in burst S53, formerly LEAF: P0015 displays (6.10) and (6.11), page 363, class MEDIUM.
`T(η) ≪ ‖η‖⁻¹` gives `∫_{1/qQ}^{1/2} |T|² ≪ qQ`, so the arc integral is
`∫_0^1 T(η)² e(-nη) dη + O(qQ) = n + O(qQ)` for `n ≤ X`, with `qQ = qX/P`. -/
theorem mv_arc_main_611 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ X ^ (6 * δ) →
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
        ‖arcIntegral (X ^ (6 * δ)) X q n - (n : ℂ)‖ ≤ C * q * (X / X ^ (6 * δ)) := by
  exact Lemma2MV.arc611_main

/-- PROVED in burst S53, formerly LEAF: P0015 display (6.13), page 363, class MEDIUM.
By (5.2), `Q Σ_{q≤P} μ(q)² φ(q)⁻² |c_q(n)| q ≪ Q n φ(n)⁻¹ d(n) log P ≪ X^{1+δ} P⁻¹`, with
`Q = X/P`; the `X^δ` absorbs `d(n) log P` and needs `X` large in terms of `δ`. -/
theorem mv_truncation_613 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      (X / X ^ (6 * δ)) * ∑ q ∈ Icc 1 ⌊X ^ (6 * δ)⌋₊, ‖mainWeight q n‖ * q ≤
        C * (X ^ (1 + δ) / X ^ (6 * δ)) := by
  obtain ⟨C, hC, h⟩ := Lemma2MV.trunc613_main
  refine ⟨C, hC, fun δ hδ hδ1 => ?_⟩
  obtain ⟨X₀, hX⟩ := h δ hδ hδ1
  refine ⟨X₀, fun X hX' n hn hnX => ?_⟩
  simpa only [norm_mainWeight_eq] using hX X hX' n hn hnX

/-- PROVED in burst S53, formerly LEAF: P0015 display (6.16), page 363, class MEDIUM.
`𝔖(n) = Σ_{q≥1} μ(q)² φ(q)⁻² c_q(-n) = ∏_{p∤n} (1 - (p-1)⁻²) ∏_{p∣n} (1 + (p-1)⁻¹)`, by (5.2);
the series converges absolutely. The `q = 0` term is zero since `μ(0) = 0`. -/
theorem mv_singular_series_616 (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun q : ℕ => ‖mainWeight q n‖) ∧
      HasSum (fun q : ℕ => mainWeight q n) ((singularSeries n : ℝ) : ℂ) := by
  obtain ⟨hs, hh⟩ := Lemma2MV.sing616_main n hn
  have hw : ∀ q : ℕ, mainWeight q n = ((LeanLab.HeathBrown1985.gm n q : ℝ) : ℂ) :=
    fun q => Lemma2MV.sing616_weight_eq q n
  refine ⟨?_, ?_⟩
  · refine hs.congr (fun q => ?_)
    rw [hw, Complex.norm_real, Real.norm_eq_abs]
  · rw [show (fun q : ℕ => mainWeight q n) =
        (fun q : ℕ => ((LeanLab.HeathBrown1985.gm n q : ℝ) : ℂ)) from funext hw]
    exact Complex.hasSum_ofReal.mpr hh

/-- PROVED in burst S53, formerly LEAF: P0015 display (6.14), page 363, class MEDIUM.
Extending the main term to all `q ≥ 1` costs
`n Σ_{q>P} φ(q)⁻¹ φ(q/(q,n))⁻¹ ≪ n P⁻¹ d(n) n φ(n)⁻¹ ≪ X^{1+δ} P⁻¹` for `n ≤ X`. -/
theorem mv_tail_614 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      (n : ℝ) * ∑' q : ℕ, (if X ^ (6 * δ) < (q : ℝ) then ‖mainWeight q n‖ else 0) ≤
        C * (X ^ (1 + δ) / X ^ (6 * δ)) := by
  obtain ⟨C, hC, h⟩ := Lemma2MV.tail614_main
  refine ⟨C, hC, fun δ hδ hδ1 => ?_⟩
  obtain ⟨X₀, hX⟩ := h δ hδ hδ1
  refine ⟨X₀, fun X hX' n hn hnX => ?_⟩
  simpa only [norm_mainWeight_eq] using hX X hX' n hn hnX

/-- PROVED in burst S53, formerly LEAF: P0015 page 366, the first display of section 7, from Lemma 4.2 (Gallagher's Lemma 1),
class MEDIUM. With `κ = 1/(rQ)`,
`W(χ) ≪ X^{1/2} max_{x≤2X} max_{0<h≤X} (h + X P⁻¹)⁻¹ |Σ^#_{x-h<p≤x} χ(p) log p|`.
Stated with any bound `M` for the double maximum; the constant is absolute. -/
theorem mv_gallagher_lemma42_step : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ X ^ (6 * δ) →
      ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive → ∀ M : ℝ,
        (∀ x h : ℝ, 0 ≤ x → x ≤ 2 * X → 0 < h → h ≤ X →
          ‖sharpSum (X ^ (6 * δ)) X χ x h‖ ≤ M * (h + X / X ^ (6 * δ))) →
        Wnorm (X ^ (6 * δ)) X χ ≤ C * Real.sqrt X * M := by
  classical
  refine ⟨49, by norm_num, ?_⟩
  intro δ hδ hδ1
  refine ⟨256, ?_⟩
  intro X hX r hr1 hrP χ _ M hM
  set P := X ^ (6 * δ) with hPdef
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hP1 : 1 ≤ P := Real.one_le_rpow hX1 (by linarith)
  have hP0 : 0 < P := by linarith
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hPs : P ≤ Real.sqrt X := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have h16 : 16 ≤ Real.sqrt X := Real.le_sqrt_of_sq_le (by linarith)
  have hXP : 16 ≤ X / P := by
    rw [le_div_iff₀ hP0]; nlinarith
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  set Q := (r : ℝ) * X / P with hQ
  have hXPQ : X / P ≤ Q := by
    rw [hQ, mul_div_assoc]; nlinarith
  have hQX : Q ≤ X := by
    rw [hQ, div_le_iff₀ hP0]; nlinarith
  have hQ0 : 0 < Q := by linarith
  set H := ⌊Q / 8⌋₊ with hHdef
  have hHle : (H : ℝ) ≤ Q / 8 := Nat.floor_le (by positivity)
  have hHge : Q / 8 - 1 < H := Nat.sub_one_lt_floor _
  have hHpos : (0 : ℝ) < H := by linarith
  have hH1 : 1 ≤ H := by
    have : (1 : ℝ) ≤ H := by linarith
    exact_mod_cast this
  have hκ : P / (r * X) = 1 / Q := by
    rw [hQ]; field_simp
  have hM0 : 0 ≤ M := by
    have h := hM 0 1 le_rfl (by linarith) one_pos hX1
    have h' : 0 ≤ M * (1 + X / P) := le_trans (norm_nonneg _) h
    rcases le_or_gt 0 M with h0 | hneg
    · exact h0
    have : M * (1 + X / P) < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    linarith
  set a : ℕ → ℂ := fun n =>
    (if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
      if χ = 1 then 1 else 0 with ha
  set s := Ioc ⌊P⌋₊ ⌊X⌋₊ with hsdef
  have hs : ∀ n ∈ s, n < ⌊X⌋₊ + 1 := by
    intro n hn; have := (mem_Ioc.mp hn).2; omega
  have hcore := gall42_gallagher s a (⌊X⌋₊ + 1) H hs hH1 (1 / Q) (by positivity)
    (by rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hQ0]; linarith)
  have hHQ : X / P ≤ 16 * H := by linarith
  have hB : ∀ m ∈ range (⌊X⌋₊ + 1 + H), ‖gall42_B s a H m‖ ^ 2 ≤ (17 * M * H) ^ 2 := by
    intro m hm
    have hmlt : m < ⌊X⌋₊ + 1 + H := mem_range.mp hm
    have hmle : (m : ℝ) ≤ X + H := by
      have h1 : m ≤ ⌊X⌋₊ + H := by omega
      have h2 : ((m : ℕ) : ℝ) ≤ ((⌊X⌋₊ + H : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2; linarith [Nat.floor_le hX0.le]
    have hb := hM m H (Nat.cast_nonneg _) (by linarith) hHpos (by linarith)
    rw [gall42_sharp_eq] at hb
    have h17 : ‖gall42_B s a H m‖ ≤ 17 * M * H := le_trans hb (by nlinarith)
    exact pow_le_pow_left₀ (norm_nonneg _) h17 2
  have hsum : ∑ m ∈ range (⌊X⌋₊ + 1 + H), ‖gall42_B s a H m‖ ^ 2 ≤
      ((⌊X⌋₊ + 1 + H : ℕ) : ℝ) * (17 * M * H) ^ 2 := by
    calc _ ≤ ∑ m ∈ range (⌊X⌋₊ + 1 + H), (17 * M * H) ^ 2 := sum_le_sum hB
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
  have hcard : ((⌊X⌋₊ + 1 + H : ℕ) : ℝ) ≤ 2 * X := by
    push_cast; linarith [Nat.floor_le hX0.le]
  have hint : ∫ η in (-(P / (r * X)))..(P / (r * X)), ‖Wchi P X χ η‖ ^ 2 ≤
      2312 * X * M ^ 2 := by
    simp_rw [gall42_Wchi_eq P X χ]
    rw [hκ]
    calc _ ≤ 4 / (H : ℝ) ^ 2 * ∑ m ∈ range (⌊X⌋₊ + 1 + H), ‖gall42_B s a H m‖ ^ 2 := hcore
      _ ≤ 4 / (H : ℝ) ^ 2 * (((⌊X⌋₊ + 1 + H : ℕ) : ℝ) * (17 * M * H) ^ 2) := by gcongr
      _ ≤ 4 / (H : ℝ) ^ 2 * (2 * X * (17 * M * H) ^ 2) := by gcongr
      _ = 2312 * X * M ^ 2 := by field_simp; ring
  have h49 : 2312 * X * M ^ 2 ≤ (49 * Real.sqrt X * M) ^ 2 := by
    have : (49 * Real.sqrt X * M) ^ 2 = 2401 * (Real.sqrt X * Real.sqrt X) * M ^ 2 := by ring
    rw [this, hsq]; nlinarith [sq_nonneg M]
  unfold Wnorm
  exact (Real.sqrt_le_sqrt hint).trans
    ((Real.sqrt_le_sqrt h49).trans_eq (Real.sqrt_sq (by positivity)))

/-- LEAF: P0015 Lemma 4.3, pages 357 and 358, Gallagher 1970 Theorem 7 made effective, applied
with `N = 2X`, class HARD, a citation wall. For each zero free constant `a > 0` there are
`c₃ > 0`, `B > 0` and a range `P ≤ N^{c₄}`, here `δ < δ₁`, such that when no primitive character
of modulus at most `P` has a real zero in `[1 - a/log P, 1)`,
`Σ_{q≤P} Σ*_χ max_{x≤N} max_{h≤N} (h + N/P)⁻¹ |Σ^#| ≪ exp(-c₃ log N / log P)`.
Stated with bounds `M r χ` for the maxima. The constants depend on `a`, because MV's absolute
constants come from the zero free constant `c₁` of Lemma 4.1, which here is `min a c` with `c` the
classical constant for complex zeros, Davenport chapter 14. -/
theorem mv_gallagher_lemma43 : ∀ a : ℝ, 0 < a → ∃ c₃ B δ₁ : ℝ, 0 < c₃ ∧ 0 < B ∧ 0 < δ₁ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      NoExceptionalReal a (X ^ (6 * δ)) →
      ∃ M : (r : ℕ) → DirichletCharacter ℂ r → ℝ,
        (∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ X ^ (6 * δ) → ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive →
          ∀ x h : ℝ, 0 ≤ x → x ≤ 2 * X → 0 < h → h ≤ X →
            ‖sharpSum (X ^ (6 * δ)) X χ x h‖ ≤ M r χ * (h + X / X ^ (6 * δ))) ∧
        ∑ r ∈ Icc 1 ⌊X ^ (6 * δ)⌋₊,
            ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, M r χ.1 ≤
          B * Real.exp (-(c₃ * Real.log X / Real.log (X ^ (6 * δ)))) := by
  sorry

/-! ### Assembly from the leaves -/

lemma mainWeight_zero (n : ℕ) : mainWeight 0 n = 0 := by
  simp [mainWeight]

/-- The tail of an absolutely summable series beyond a finite set. PROVED. -/
lemma norm_sum_sub_tsum_le {f : ℕ → ℂ} {S : ℂ} (hs : Summable (fun q => ‖f q‖))
    (hS : HasSum f S) (s : Finset ℕ) :
    ‖(∑ q ∈ s, f q) - S‖ ≤ ∑' q : ℕ, (if q ∈ s then 0 else ‖f q‖) := by
  have hf : Summable f := hs.of_norm
  have h1 : (∑ q ∈ s, f q) - S = -∑' q : ℕ, (if q ∈ s then 0 else f q) := by
    have hsplit : ∑' q : ℕ, f q = ∑ q ∈ s, f q + ∑' q : ℕ, (if q ∈ s then 0 else f q) := by
      rw [← hf.sum_add_tsum_compl (s := s), tsum_subtype (↑s : Set ℕ)ᶜ f]
      congr 1
      refine tsum_congr (fun q => ?_)
      by_cases hq : q ∈ s <;> simp [hq, Set.indicator]
    rw [hS.tsum_eq] at hsplit
    rw [hsplit]; ring
  rw [h1, norm_neg]
  have hsum : Summable (fun q : ℕ => (if q ∈ s then 0 else ‖f q‖)) :=
    hs.of_nonneg_of_le (fun q => by split_ifs <;> simp) (fun q => by split_ifs <;> simp)
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr (fun q => ?_)))
  · refine hsum.congr (fun q => ?_)
    by_cases hq : q ∈ s <;> simp [hq]
  · by_cases hq : q ∈ s <;> simp [hq]

/-- P0015 display (6.17): `R₁(n) = 𝔖(n) n + O(X^{1+δ} P⁻¹) + O(n φ(n)⁻¹ (W X^{1/2} + W²))` for
`1 ≤ n ≤ X`. PROVED from the five leaves of section 6. -/
theorem mv_617 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      ‖R1 (X ^ (6 * δ)) X (n : ℤ) - (((n : ℝ) * singularSeries n : ℝ) : ℂ)‖ ≤
        C * (X ^ (1 + δ) / X ^ (6 * δ)) + C * ((n : ℝ) / (n.totient : ℝ)) *
          (mvW (X ^ (6 * δ)) X * Real.sqrt X + mvW (X ^ (6 * δ)) X ^ 2) := by
  obtain ⟨C1, hC1, h1⟩ := mv_remainder_66_68
  obtain ⟨C2, hC2, h2⟩ := mv_arc_main_611
  obtain ⟨C3, hC3, h3⟩ := mv_truncation_613
  obtain ⟨C4, hC4, h4⟩ := mv_tail_614
  refine ⟨C1 + C2 * C3 + C4, by positivity, ?_⟩
  intro δ hδ hδ1
  obtain ⟨X1, hX1⟩ := h1 δ hδ hδ1
  obtain ⟨X2, hX2⟩ := h2 δ hδ hδ1
  obtain ⟨X3, hX3⟩ := h3 δ hδ hδ1
  obtain ⟨X4, hX4⟩ := h4 δ hδ hδ1
  refine ⟨max (max X1 X2) (max X3 (max X4 1)), ?_⟩
  intro X hX n hn hnX
  have hXa : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXb : X2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXc : X3 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXd : X4 ≤ X := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hX
  have hX1' : (1 : ℝ) ≤ X := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hX
  set P := X ^ (6 * δ) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg (by linarith) _
  set s := Icc 1 ⌊P⌋₊ with hs
  set W := mvW P X
  set ρ := (n : ℝ) / (n.totient : ℝ)
  have hφ : (0 : ℝ) < (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hρ1 : 1 ≤ ρ := by
    rw [le_div_iff₀ hφ, one_mul]; exact_mod_cast Nat.totient_le n
  have hW0 : 0 ≤ W := by
    refine sum_nonneg (fun r _ => finsum_nonneg (fun χ => Real.sqrt_nonneg _))
  set E := X ^ (1 + δ) / P
  have hE0 : 0 ≤ E := div_nonneg (Real.rpow_nonneg (by linarith) _) hP0
  -- the three pieces
  have hA := hX1 X hXa n hn hnX
  have hB : ‖∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ))‖ ≤ C2 * C3 * E := by
    calc ‖∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ))‖
        ≤ ∑ q ∈ s, ‖mainWeight q n‖ * (C2 * q * (X / P)) := by
          refine (norm_sum_le _ _).trans (sum_le_sum (fun q hq => ?_))
          rw [norm_mul]
          have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
          have hqP : (q : ℝ) ≤ P := by
            have := (mem_Icc.mp hq).2
            exact le_trans (by exact_mod_cast this) (Nat.floor_le hP0)
          exact mul_le_mul_of_nonneg_left (hX2 X hXb q hq1 hqP n hn hnX) (norm_nonneg _)
      _ = C2 * ((X / P) * ∑ q ∈ s, ‖mainWeight q n‖ * q) := by
          rw [mul_sum, mul_sum]; refine sum_congr rfl (fun q _ => by ring)
      _ ≤ C2 * (C3 * E) := mul_le_mul_of_nonneg_left (hX3 X hXc n hn hnX) hC2.le
      _ = C2 * C3 * E := by ring
  have hC : ‖(n : ℂ) * ((∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ))‖ ≤ C4 * E := by
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
    calc (n : ℝ) * ‖(∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ)‖
        ≤ (n : ℝ) * ∑' q : ℕ, (if P < (q : ℝ) then ‖mainWeight q n‖ else 0) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ C4 * E := hX4 X hXd n hn hnX
  -- assemble
  have hsplit : R1 P X (n : ℤ) - (((n : ℝ) * singularSeries n : ℝ) : ℂ) =
      (R1 P X (n : ℤ) - ∑ q ∈ s, mainWeight q n * arcIntegral P X q n) +
        ∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ)) +
        (n : ℂ) * ((∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ)) := by
    simp only [mul_sub, sum_sub_distrib, mul_sum]
    push_cast
    have : ∑ q ∈ s, mainWeight q n * (n : ℂ) = ∑ q ∈ s, (n : ℂ) * mainWeight q n :=
      sum_congr rfl (fun q _ => mul_comm _ _)
    rw [this]; ring
  rw [hsplit]
  have hrem : 0 ≤ ρ * (W * Real.sqrt X + W ^ 2) := by positivity
  calc _ ≤ ‖R1 P X (n : ℤ) - ∑ q ∈ s, mainWeight q n * arcIntegral P X q n‖ +
          ‖∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ))‖ +
          ‖(n : ℂ) * ((∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ))‖ :=
        norm_add₃_le
    _ ≤ C1 * ρ * (W * Real.sqrt X + W ^ 2) + C2 * C3 * E + C4 * E := by
        gcongr
    _ ≤ (C1 + C2 * C3 + C4) * E + (C1 + C2 * C3 + C4) * ρ * (W * Real.sqrt X + W ^ 2) := by
        have h23 : 0 ≤ C2 * C3 := by positivity
        nlinarith [mul_nonneg h23 hrem, mul_nonneg hC4.le hrem, mul_nonneg hC1.le hE0]

/-- P0015 display (7.1): `W ≪ X^{1/2} exp(-c₆ log X / log P)` when there is no exceptional term,
here for the zero free constant `a`. PROVED from the two leaves of section 7. -/
theorem mv_71 : ∀ a : ℝ, 0 < a → ∃ c₆ B δ₁ : ℝ, 0 < c₆ ∧ 0 < B ∧ 0 < δ₁ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      NoExceptionalReal a (X ^ (6 * δ)) →
      mvW (X ^ (6 * δ)) X ≤
        B * Real.sqrt X * Real.exp (-(c₆ * Real.log X / Real.log (X ^ (6 * δ)))) := by
  intro a ha
  obtain ⟨C, hC, hG⟩ := mv_gallagher_lemma42_step
  obtain ⟨c₃, B, δ₁, hc₃, hB, hδ₁, hL⟩ := mv_gallagher_lemma43 a ha
  refine ⟨c₃, C * B, min δ₁ (1 / 100), hc₃, by positivity, lt_min hδ₁ (by norm_num), ?_⟩
  intro δ hδ hδm
  obtain ⟨X1, hX1⟩ := hG δ hδ (lt_of_lt_of_le hδm (min_le_right _ _))
  obtain ⟨X2, hX2⟩ := hL δ hδ (lt_of_lt_of_le hδm (min_le_left _ _))
  refine ⟨max X1 (max X2 0), ?_⟩
  intro X hX hno
  have hXa : X1 ≤ X := le_trans (le_max_left _ _) hX
  have hXb : X2 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX0 : 0 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  obtain ⟨M, hM, hsum⟩ := hX2 X hXb hno
  set P := X ^ (6 * δ) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg hX0 _
  have hstep : ∀ r ∈ Icc 1 ⌊P⌋₊,
      ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, Wnorm P X χ.1 ≤
        C * Real.sqrt X * ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, M r χ.1 := by
    intro r hr
    have hr1 : 1 ≤ r := (mem_Icc.mp hr).1
    have hrP : (r : ℝ) ≤ P := le_trans (by exact_mod_cast (mem_Icc.mp hr).2) (Nat.floor_le hP0)
    have : NeZero r := ⟨by omega⟩
    rw [mul_finsum]
    refine finsum_le_finsum (Set.toFinite _) (Set.toFinite _) (fun χ => ?_)
    exact hX1 X hXa r hr1 hrP χ.1 χ.2 (M r χ.1) (hM r hr1 hrP χ.1 χ.2)
  calc mvW P X ≤ ∑ r ∈ Icc 1 ⌊P⌋₊, C * Real.sqrt X *
          ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, M r χ.1 := sum_le_sum hstep
    _ = C * Real.sqrt X * ∑ r ∈ Icc 1 ⌊P⌋₊,
          ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, M r χ.1 := by rw [mul_sum]
    _ ≤ C * Real.sqrt X * (B * Real.exp (-(c₃ * Real.log X / Real.log P))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C * B * Real.sqrt X * Real.exp (-(c₃ * Real.log X / Real.log P)) := by ring

/-! ### The faithful twin of `Lemma2NoExcBP` and its assembly -/

/-- P0082 page 358 Lemma 2 for small `δ`, the range Montgomery and Vaughan cover: for every zero
free constant `a > 0` there are `c₁, K > 0` and `δ₁ > 0` such that for `0 < δ < δ₁`,
`P = X^{6δ}`, all large `X` with no exceptional character, and every `1 ≤ m ≤ X`,
`|R₁(m) - m 𝔖(m)| ≤ K m φ(m)⁻¹ X exp(-c₁ log X / log P)`. It differs from `Lemma2NoExcBP` only by
`δ < δ₁` in place of `δ < 1/100`; `lemma2NoExcSmallDelta_of_BP` shows it is weaker. -/
def Lemma2NoExcSmallDelta : Prop :=
  ∀ a : ℝ, 0 < a → ∃ c₁ K : ℝ, 0 < c₁ ∧ 0 < K ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      NoExceptionalReal a (X ^ (6 * δ)) →
      ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ X →
        ‖R1 (X ^ (6 * δ)) X (m : ℤ) - (((m : ℝ) * singularSeries m : ℝ) : ℂ)‖ ≤
          K * ((m : ℝ) / (m.totient : ℝ)) * X *
            Real.exp (-(c₁ * Real.log X / Real.log (X ^ (6 * δ))))

/-- `Lemma2NoExcBP` implies its small `δ` twin. PROVED, sorry free. -/
theorem lemma2NoExcSmallDelta_of_BP (h : Lemma2NoExcBP) : Lemma2NoExcSmallDelta := by
  intro a ha
  obtain ⟨c₁, K, hc₁, hK, hL⟩ := h a ha
  exact ⟨c₁, K, hc₁, hK, 1 / 100, by norm_num, hL⟩

/-- P0082 Lemma 2 for small `δ`, "Combine (6.17) and (7.1) of Montgomery & Vaughan".
PROVED from the seven leaves above: `X^{1+δ}P⁻¹ = X·X^{-5δ}` is below `X exp(-c₆/(6δ))` once
`log X ≥ c₆/(30δ²)`, and `W² ≤ B² X exp(-2c₆ log X / log P)`. -/
theorem lemma2NoExcSmallDelta_of_leaves : Lemma2NoExcSmallDelta := by
  intro a ha
  obtain ⟨CA, hCA, hA⟩ := mv_617
  obtain ⟨c₆, B, δ₁, hc₆, hB, hδ₁, hW⟩ := mv_71 a ha
  refine ⟨c₆, CA * (1 + B + B ^ 2), hc₆, by positivity, min δ₁ (1 / 100),
    lt_min hδ₁ (by norm_num), ?_⟩
  intro δ hδ hδm
  obtain ⟨XA, hXA⟩ := hA δ hδ (lt_of_lt_of_le hδm (min_le_right _ _))
  obtain ⟨XB, hXB⟩ := hW δ hδ (lt_of_lt_of_le hδm (min_le_left _ _))
  refine ⟨max (max XA XB) (max 2 (Real.exp (c₆ / (30 * δ ^ 2)))), ?_⟩
  intro X hX hno m hm hmX
  have hXa : XA ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXb : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX2 : (2 : ℝ) ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXe : Real.exp (c₆ / (30 * δ ^ 2)) ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogP : Real.log (X ^ (6 * δ)) = 6 * δ * Real.log X := Real.log_rpow hX0 _
  have hratio : c₆ * Real.log X / Real.log (X ^ (6 * δ)) = c₆ / (6 * δ) := by
    rw [hlogP]; field_simp
  have hbA := hXA X hXa m hm hmX
  have hbW := hXB X hXb hno
  rw [hratio] at hbW ⊢
  set e := Real.exp (-(c₆ / (6 * δ))) with he
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := by
    rw [he, Real.exp_le_one_iff]; have : 0 < c₆ / (6 * δ) := by positivity
    linarith
  set W := mvW (X ^ (6 * δ)) X
  have hW0 : 0 ≤ W := sum_nonneg (fun r _ => finsum_nonneg (fun χ => Real.sqrt_nonneg _))
  set ρ := (m : ℝ) / (m.totient : ℝ)
  have hφ : (0 : ℝ) < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hρ1 : 1 ≤ ρ := by
    rw [le_div_iff₀ hφ, one_mul]; exact_mod_cast Nat.totient_le m
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hsq0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  -- the first error term
  have hE : X ^ (1 + δ) / X ^ (6 * δ) ≤ X * e := by
    rw [Real.rpow_def_of_pos hX0, Real.rpow_def_of_pos hX0, ← Real.exp_sub, he]
    have hsplit : Real.log X * (1 + δ) - Real.log X * (6 * δ) =
        Real.log X + -(5 * δ * Real.log X) := by ring
    rw [hsplit, Real.exp_add, Real.exp_log hX0]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hX0.le
    have hl : c₆ / (30 * δ ^ 2) ≤ Real.log X := by
      rw [← Real.log_exp (c₆ / (30 * δ ^ 2))]
      exact Real.log_le_log (Real.exp_pos _) hXe
    have h30 : c₆ / (6 * δ) = 5 * δ * (c₆ / (30 * δ ^ 2)) := by field_simp; ring
    rw [h30]
    have : 5 * δ * (c₆ / (30 * δ ^ 2)) ≤ 5 * δ * Real.log X :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    linarith
  -- the W terms
  have hW1 : W * Real.sqrt X ≤ B * X * e := by
    calc W * Real.sqrt X ≤ B * Real.sqrt X * e * Real.sqrt X :=
          mul_le_mul_of_nonneg_right hbW hsq0
      _ = B * X * e := by linear_combination (B * e) * hsq
  have hW2 : W ^ 2 ≤ B ^ 2 * X * e := by
    have h1 : W ^ 2 ≤ (B * Real.sqrt X * e) ^ 2 := pow_le_pow_left₀ hW0 hbW 2
    have h2 : (B * Real.sqrt X * e) ^ 2 = B ^ 2 * X * (e * e) := by
      linear_combination (B ^ 2 * e ^ 2) * hsq
    have h3 : B ^ 2 * X * (e * e) ≤ B ^ 2 * X * e := by
      have : e * e ≤ e := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  calc _ ≤ CA * (X ^ (1 + δ) / X ^ (6 * δ)) + CA * ρ * (W * Real.sqrt X + W ^ 2) := hbA
    _ ≤ CA * (ρ * (X * e)) + CA * ρ * (B * X * e + B ^ 2 * X * e) := by
        have hXe0 : 0 ≤ X * e := by positivity
        gcongr
        calc X ^ (1 + δ) / X ^ (6 * δ) ≤ X * e := hE
          _ ≤ ρ * (X * e) := by nlinarith
    _ = CA * (1 + B + B ^ 2) * ρ * X * e := by ring

/-- P0082 page 362 Lemma 7 case i, the exact statement of `Decomp559b.leaf_absent_selected`,
CONDITIONAL ON `Lemma2NoExcSmallDelta` and `SingularSeriesEvenLowerBP`, the latter proved as
`Prep1121SingSeries.singularSeriesEvenLowerBP_split`. The proof is that of
`DQLeafAbsentSelected.leaf_absent_selected_of_lemma2` with `δ₀` also below `δ₁`. Sorry free. -/
theorem leaf_absent_selected_of_small (hL : Lemma2NoExcSmallDelta)
    (hS : SingularSeriesEvenLowerBP)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              r = 1 →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  obtain ⟨c₁, K, hc₁, hK, δ₁, hδ₁, hL⟩ := hL a ha
  obtain ⟨Cs, hCs, hS⟩ := hS
  refine ⟨min δ₁ (c₁ * Cs / (24 * K)), lt_min hδ₁ (by positivity), ?_⟩
  intro δ hδ hδ₀
  have hδ1 : δ < δ₁ := lt_of_lt_of_le hδ₀ (min_le_left _ _)
  have hδ2 : δ < c₁ * Cs / (24 * K) := lt_of_lt_of_le hδ₀ (min_le_right _ _)
  obtain ⟨X₀, hX₀⟩ := hL δ hδ hδ1
  refine ⟨1, one_pos, ?_⟩
  intro κ _ _
  refine ⟨Cs / 4, 1, by positivity, one_pos, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hF.eventually_ge_atTop (max X₀ 2))
  refine ⟨N₀, ?_⟩
  intro N hN r _ _ hs j hj n hn heven hm hr1
  subst hr1
  have hXbig := hN₀ N hN
  have hX₀X : X₀ ≤ F γ N := le_trans (le_max_left _ _) hXbig
  have hX2 : 2 ≤ F γ N := le_trans (le_max_right _ _) hXbig
  have hnoexc := noExceptionalReal_of_selected_one hs
  have hwin := (Finset.mem_filter.mp hn).2
  have hνpos : (0 : ℤ) < nu γ n := by
    have : (0 : ℝ) < (nu γ n : ℝ) := by linarith [hwin.1]
    exact_mod_cast this
  have hj0 : 0 ≤ j := by rcases hj with h | h <;> omega
  have hnn : 0 ≤ nu γ n + j := by omega
  set k : ℕ := (nu γ n + j).toNat with hkdef
  have hk : ((k : ℕ) : ℤ) = nu γ n + j := Int.toNat_of_nonneg hnn
  rw [← hk] at heven hm ⊢
  have hk1 : 1 ≤ k := by omega
  have hkX : (k : ℝ) ≤ F γ N := by exact_mod_cast hm
  have hkeven : Even k := Int.even_coe_nat k |>.mp heven
  have hkhalf : F γ N / 2 < (k : ℝ) := by
    have h1' : (nu γ n : ℤ) ≤ (k : ℤ) := by omega
    have h2' : ((nu γ n : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) := by exact_mod_cast h1'
    have h3' : ((k : ℤ) : ℝ) = (k : ℝ) := by push_cast; rfl
    linarith [hwin.1]
  have hbound := hX₀ (F γ N) hX₀X hnoexc k hk1 hkX
  set X := F γ N with hXdef
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogP : Real.log (X ^ (6 * δ)) = 6 * δ * Real.log X := Real.log_rpow hX0 _
  have hratio : c₁ * Real.log X / Real.log (X ^ (6 * δ)) = c₁ / (6 * δ) := by
    rw [hlogP]; field_simp
  rw [hratio] at hbound
  set e := Real.exp (-(c₁ / (6 * δ))) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hKe : K * e ≤ Cs / 4 := by
    have h1' : e ≤ 1 / (c₁ / (6 * δ)) := exp_neg_le_inv (by positivity)
    have h2' : 1 / (c₁ / (6 * δ)) = 6 * δ / c₁ := by field_simp
    rw [h2'] at h1'
    have h3' : K * e ≤ K * (6 * δ / c₁) := mul_le_mul_of_nonneg_left h1' hK.le
    have h4' : K * (6 * δ / c₁) ≤ Cs / 4 := by
      rw [lt_div_iff₀ (by positivity)] at hδ2
      rw [mul_div_assoc', div_le_iff₀ hc₁]
      nlinarith
    linarith
  set ρ := (k : ℝ) / (k.totient : ℝ) with hρ
  have hφ : (0 : ℝ) < (k.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hρ1 : 1 ≤ ρ := by
    rw [hρ, le_div_iff₀ hφ, one_mul]; exact_mod_cast Nat.totient_le k
  have hsing := hS k hk1 hkeven
  have hre : (k : ℝ) * singularSeries k - K * ρ * X * e ≤
      (R1 (X ^ (6 * δ)) X ((k : ℕ) : ℤ)).re := by
    have h := Complex.abs_re_le_norm
      (R1 (X ^ (6 * δ)) X ((k : ℕ) : ℤ) - (((k : ℝ) * singularSeries k : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h
    have := (abs_le.mp (h.trans hbound)).1
    linarith
  have hmain : Cs / 4 * X ≤ (R1 (X ^ (6 * δ)) X ((k : ℕ) : ℤ)).re := by
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hA1 : (k : ℝ) * (Cs * ρ) ≤ (k : ℝ) * singularSeries k :=
      mul_le_mul_of_nonneg_left hsing hk0
    have hA2 : K * ρ * X * e ≤ ρ * X * (Cs / 4) := by
      have := mul_le_mul_of_nonneg_left hKe (by positivity : (0 : ℝ) ≤ ρ * X)
      nlinarith
    have hA3 : ρ * (Cs * (X / 2)) ≤ ρ * (Cs * k) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkhalf.le hCs.le) (by positivity)
    have hA4 : Cs / 4 * X ≤ ρ * (Cs / 4 * X) := by
      have : 0 ≤ Cs / 4 * X := by positivity
      nlinarith
    nlinarith
  have hP0 : 0 ≤ X ^ (6 * δ) := Real.rpow_nonneg hX0.le _
  have hD : 0 ≤ divisorError 1 (X ^ (6 * δ)) ((k : ℕ) : ℤ) := by
    unfold divisorError
    apply add_nonneg
    · refine mul_nonneg ?_ (sum_nonneg (fun q _ => div_nonneg (by positivity) (by positivity)))
      simpa using div_nonneg zero_le_one hP0
    · refine mul_nonneg ?_ (tsum_nonneg (fun q => by split_ifs <;> positivity))
      simp
  have : 0 ≤ 1 * X * divisorError 1 (X ^ (6 * δ)) ((k : ℕ) : ℤ) := by positivity
  linarith

/-- Twin check: `leaf_absent_selected_of_small` has exactly the type of the open leaf
`Decomp559b.leaf_absent_selected`. -/
example (hL : Lemma2NoExcSmallDelta) (hS : SingularSeriesEvenLowerBP) : True :=
  let _f : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_absent_selected :=
    leaf_absent_selected_of_small hL hS
  trivial

#print axioms mv_arc_main_611
#print axioms mv_truncation_613
#print axioms mv_tail_614
#print axioms mv_singular_series_616
#print axioms mv_gallagher_lemma42_step
#print axioms lemma2NoExcSmallDelta_of_BP
#print axioms leaf_absent_selected_of_small
#print axioms mv_617
#print axioms mv_71
#print axioms lemma2NoExcSmallDelta_of_leaves

end LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit
