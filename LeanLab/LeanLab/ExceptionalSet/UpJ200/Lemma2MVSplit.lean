import LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelectedDecisions

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

/-! ### Private helpers for the arc main term, P0015 (6.10) and (6.11) -/

private lemma eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma eC_zero : eC 0 = 1 := by
  unfold eC
  simp

private lemma eC_intCast (k : ℤ) : eC (k : ℝ) = 1 := by
  unfold eC
  have h : (2 * ↑Real.pi * Complex.I * ((k : ℝ) : ℂ)) = (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

private lemma norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have h : (2 * ↑Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- `∫₀¹ e(ηk) dη` is `1` for `k = 0` and `0` otherwise. P0015 orthogonality. -/
private lemma integral_eC_int (k : ℤ) :
    (∫ η in (0 : ℝ)..1, eC (η * (k : ℝ))) = if k = 0 then 1 else 0 := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    simp [eC_zero]
  · have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have h2pi : (2 : ℂ) * ↑Real.pi * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_pos.ne')) Complex.I_ne_zero
    have hc : (2 * ↑Real.pi * Complex.I * (k : ℂ)) ≠ 0 := mul_ne_zero h2pi hk' 
    have hfun : (fun η : ℝ => eC (η * (k : ℝ))) =
        fun η : ℝ => Complex.exp ((2 * ↑Real.pi * Complex.I * (k : ℂ)) * η) := by
      funext η
      unfold eC
      congr 1
      push_cast
      ring
    rw [hfun, integral_exp_mul_complex hc]
    have h1 : (2 * ↑Real.pi * Complex.I * (k : ℂ)) = (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by ring
    rw [h1]
    have hexp : Complex.exp ((k : ℂ) * (2 * ↑Real.pi * Complex.I)) = 1 :=
      Complex.exp_int_mul_two_pi_mul_I k
    simp [hexp, hk]

private lemma continuous_eC : Continuous eC := by
  unfold eC
  fun_prop

private lemma continuous_eC_mul (c : ℝ) : Continuous fun η : ℝ => eC (η * c) :=
  continuous_eC.comp (continuous_id.mul continuous_const)

/-- `arcIntegral` expanded over the pairs `(m, m')` of the sum `T`. P0015 display (6.4). -/
private lemma arcIntegral_eq_double (P X : ℝ) (q n : ℕ) :
    arcIntegral P X q n =
      ∑ m ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, ∑ m' ∈ Ioc ⌊P⌋₊ ⌊X⌋₊,
        ∫ η in (-(P / (q * X)))..(P / (q * X)), eC (η * ((m : ℝ) + (m' : ℝ) - (n : ℝ))) := by
  have hpt : ∀ η : ℝ,
      (∑ m ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, eC (η * (m : ℝ))) ^ 2 * eC (-(η * (n : ℝ))) =
        ∑ m ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, ∑ m' ∈ Ioc ⌊P⌋₊ ⌊X⌋₊,
          eC (η * ((m : ℝ) + (m' : ℝ) - (n : ℝ))) := by
    intro η
    have hm : ∀ m m' : ℕ, eC (η * (m : ℝ)) * eC (η * (m' : ℝ)) * eC (-(η * (n : ℝ)))
        = eC (η * ((m : ℝ) + (m' : ℝ) - (n : ℝ))) := by
      intro m m'
      rw [← eC_add, ← eC_add]
      congr 1
      ring
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum, hm]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    congr 1
    ring
  unfold arcIntegral T
  simp only [hpt]
  rw [intervalIntegral.integral_finsetSum (f := fun (m : ℕ) η =>
    ∑ m' ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, eC (η * ((m : ℝ) + (m' : ℝ) - (n : ℝ)))) (fun (m : ℕ) _ =>
    (continuous_finsetSum _
      (fun (m' : ℕ) _ => continuous_eC_mul ((m : ℝ) + (m' : ℝ) - (n : ℝ)))).intervalIntegrable _ _)]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [intervalIntegral.integral_finsetSum (f := fun (m' : ℕ) η =>
    eC (η * ((m : ℝ) + (m' : ℝ) - (n : ℝ)))) (fun (m' : ℕ) _ =>
    (continuous_eC_mul ((m : ℝ) + (m' : ℝ) - (n : ℝ))).intervalIntegrable _ _)]

/-- The integrand of the arc integral, expanded over pairs. P0015 display (6.4). -/
private lemma T_sq_mul_eC (P X : ℝ) (n : ℕ) (η : ℝ) :
    T P X η ^ 2 * eC (-(η * (n : ℝ))) =
      ∑ m ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, ∑ m' ∈ Ioc ⌊P⌋₊ ⌊X⌋₊,
        eC (η * ((m : ℝ) + (m' : ℝ) - (n : ℝ))) := by
  have hm : ∀ m m' : ℕ, eC (η * (m : ℝ)) * eC (η * (m' : ℝ)) * eC (-(η * (n : ℝ)))
      = eC (η * ((m : ℝ) + (m' : ℝ) - (n : ℝ))) := by
    intro m m'
    rw [← eC_add, ← eC_add]
    congr 1
    ring
  simp only [T, pow_two, Finset.sum_mul, Finset.mul_sum, hm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  congr 1
  ring

/-- The single-period integral of one term of the pair expansion. -/
private lemma integral_eC_pair (m m' n : ℕ) :
    (∫ η in (0 : ℝ)..1, eC (η * ((m : ℝ) + (m' : ℝ) - (n : ℝ)))) =
      if m + m' = n then 1 else 0 := by
  have harg : ∀ η : ℝ, η * ((m : ℝ) + (m' : ℝ) - (n : ℝ))
      = η * ((((m : ℤ) + (m' : ℤ) - (n : ℤ) : ℤ)) : ℝ) := by
    intro η
    push_cast
    ring
  simp only [harg]
  rw [integral_eC_int ((m : ℤ) + (m' : ℤ) - (n : ℤ))]
  have hiff : ((m : ℤ) + (m' : ℤ) - (n : ℤ) = 0) ↔ (m + m' = n) := by omega
  by_cases h : m + m' = n
  · simp [hiff, h]
  · simp [hiff, h]

/-- The inner sum over `m'`: for `m` in the index, the pairs `m + m' = n` correspond to the
values `m'` with `m + m' = n`, which exist exactly when `a < m ≤ n - 1 - a`. -/
private lemma inner_pair_sum (P X : ℝ) (n m : ℕ) (hnX : n ≤ ⌊X⌋₊)
    (hm : m ∈ Ioc ⌊P⌋₊ ⌊X⌋₊) :
    (∑ m' ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, (if m + m' = n then (1 : ℂ) else 0)) =
      if m ∈ Ioc ⌊P⌋₊ (n - 1 - ⌊P⌋₊) then 1 else 0 := by
  set a := ⌊P⌋₊ with ha
  set B := ⌊X⌋₊ with hB
  have ham : a < m := (mem_Ioc.mp hm).1
  by_cases hcase : m ≤ n - 1 - a
  · have hmn : m ≤ n := by omega
    have hmem : n - m ∈ Ioc a B := mem_Ioc.mpr ⟨by omega, by omega⟩
    refine (Finset.sum_eq_single (n - m) ?_ (fun h => absurd hmem h)).trans ?_
    · intro m' _ hne
      have hne' : m + m' ≠ n := by omega
      simp [hne']
    · have hsum : m + (n - m) = n := by omega
      rw [if_pos hsum, if_pos (mem_Ioc.mpr ⟨ham, hcase⟩)]
  · have hout : m ∉ Ioc a (n - 1 - a) := fun h => hcase (mem_Ioc.mp h).2
    rw [if_neg hout]
    refine Finset.sum_eq_zero (fun m' hm' => ?_)
    have ham' : a < m' := (mem_Ioc.mp hm').1
    have hne : m + m' ≠ n := by omega
    simp [hne]

/-- The single-period integral is the number of pairs `(m, m')` of the index with `m + m' = n`. -/
private lemma integral_one_period (P X : ℝ) (n : ℕ) (hnX : n ≤ ⌊X⌋₊) :
    (∫ η in (0 : ℝ)..1, T P X η ^ 2 * eC (-(η * (n : ℝ)))) =
      (((Ioc ⌊P⌋₊ (n - 1 - ⌊P⌋₊)).card : ℕ) : ℂ) := by
  set a := ⌊P⌋₊ with ha
  set B := ⌊X⌋₊ with hB
  have hstep : (∫ η in (0 : ℝ)..1, T P X η ^ 2 * eC (-(η * (n : ℝ))))
      = ∑ m ∈ Ioc a B, ∑ m' ∈ Ioc a B, (if m + m' = n then (1 : ℂ) else 0) := by
    simp only [T_sq_mul_eC]
    rw [intervalIntegral.integral_finsetSum (f := fun (m : ℕ) η =>
      ∑ m' ∈ Ioc a B, eC (η * ((m : ℝ) + (m' : ℝ) - (n : ℝ)))) (fun (m : ℕ) _ =>
      (continuous_finsetSum _ (fun (m' : ℕ) _ =>
        continuous_eC_mul ((m : ℝ) + (m' : ℝ) - (n : ℝ)))).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [intervalIntegral.integral_finsetSum (f := fun (m' : ℕ) η =>
      eC (η * ((m : ℝ) + (m' : ℝ) - (n : ℝ)))) (fun (m' : ℕ) _ =>
      (continuous_eC_mul ((m : ℝ) + (m' : ℝ) - (n : ℝ))).intervalIntegrable _ _)]
    exact Finset.sum_congr rfl (fun m' _ => integral_eC_pair m m' n)
  rw [hstep]
  have hsub : Ioc a (n - 1 - a) ⊆ Ioc a B := by
    intro x hx
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hx).1, by have := (mem_Ioc.mp hx).2; omega⟩
  calc ∑ m ∈ Ioc a B, ∑ m' ∈ Ioc a B, (if m + m' = n then (1 : ℂ) else 0)
      = ∑ m ∈ Ioc a B, (if m ∈ Ioc a (n - 1 - a) then (1 : ℂ) else 0) :=
        Finset.sum_congr rfl (fun m hm => inner_pair_sum P X n m (by simpa [hB] using hnX) (by simpa [ha, hB] using hm))
    _ = ((Ioc a (n - 1 - a)).card : ℂ) := by
        rw [Finset.sum_ite_mem]
        rw [Finset.inter_eq_right.mpr hsub]
        simp

private lemma eC_pow (η : ℝ) (m : ℕ) : eC (η * (m : ℝ)) = eC η ^ m := by
  induction m with
  | zero => simp [eC_zero]
  | succ k ih =>
      rw [Nat.cast_succ, mul_add, mul_one, eC_add, ih, pow_succ]

/-- `‖1 - e(η)‖ = 2|sin πη|`, hence at least `4|η|` for `|η| ≤ 1/2`. -/
private lemma norm_one_sub_eC (t : ℝ) (ht : |t| ≤ 1 / 2) :
    ‖1 - eC t‖ ^ 2 = 4 * Real.sin (Real.pi * t) ^ 2 := by
  set θ := 2 * Real.pi * t with hθ
  have hθ2 : θ = 2 * (Real.pi * t) := by rw [hθ]; ring
  have hexp : eC t = Complex.exp ((θ : ℂ) * Complex.I) := by
    unfold eC
    rw [hθ]
    congr 1
    push_cast
    ring
  have hre : (Complex.exp ((θ : ℂ) * Complex.I)).re = Real.cos θ := by
    rw [Complex.exp_mul_I]
    simp [Complex.cos_ofReal_re]
  have him : (Complex.exp ((θ : ℂ) * Complex.I)).im = Real.sin θ := by
    rw [Complex.exp_mul_I]
    simp [Complex.sin_ofReal_re]
  have hcs : Real.cos (Real.pi * t) ^ 2 = 1 - Real.sin (Real.pi * t) ^ 2 := by
    have := Real.cos_sq_add_sin_sq (Real.pi * t)
    linarith
  have hcos : Real.cos θ = 1 - 2 * Real.sin (Real.pi * t) ^ 2 := by
    rw [hθ2]
    rw [Real.cos_two_mul]
    linarith
  have hsin : Real.sin θ = 2 * Real.sin (Real.pi * t) * Real.cos (Real.pi * t) := by
    rw [hθ2]
    rw [Real.sin_two_mul]
  rw [hexp, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hre, him]
  rw [hcos, hsin]
  nlinarith [hcs]

private lemma norm_one_sub_eC_ge (t : ℝ) (ht : |t| ≤ 1 / 2) :
    4 * |t| ≤ ‖1 - eC t‖ := by
  have hsq := norm_one_sub_eC t ht
  have hsin : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
    have hle : |Real.pi * t| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      calc Real.pi * |t| ≤ Real.pi * (1 / 2) := mul_le_mul_of_nonneg_left ht (le_of_lt Real.pi_pos)
        _ = Real.pi / 2 := by ring
    have h := Real.mul_abs_le_abs_sin (x := Real.pi * t) hle
    have hpi : 2 / Real.pi * |Real.pi * t| = 2 * |t| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp
    linarith [h]
  have h4 : (4 * |t|) ^ 2 ≤ Real.sin (Real.pi * t) ^ 2 * 4 := by
    have h0 : (0:ℝ) ≤ 2 * |t| := by positivity
    have h1 : (2 * |t|) ^ 2 ≤ Real.sin (Real.pi * t) ^ 2 := by
      have h2 : (2 * |t|) ^ 2 ≤ |Real.sin (Real.pi * t)| ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) hsin 2
      rwa [sq_abs] at h2
    nlinarith [h1]
  have hnn : (0:ℝ) ≤ 4 * |t| := by positivity
  have := hsq
  nlinarith [h4, this, hnn, norm_nonneg (1 - eC t : ℂ)]

/-- The partial geometric sum: `‖Σ_{i<n} z^i‖ ≤ 2/‖1 - z‖` for `‖z‖ = 1`, `z ≠ 1`. -/
private lemma norm_geom_sum_le (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, z ^ i‖ ≤ 2 / ‖1 - z‖ := by
  have h1 : (1:ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  rw [geom_sum_eq hz1 n, div_eq_mul_inv, norm_mul, norm_inv]
  have hnum : ‖z ^ n - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, hz, one_pow]
    norm_num
  have hnorm : ‖z - 1‖ = ‖1 - z‖ := by rw [← norm_neg]; ring_nf
  rw [hnorm]
  have hpos : (0:ℝ) < ‖1 - z‖ := norm_pos_iff.mpr h1
  rw [div_eq_mul_inv]
  calc ‖z ^ n - 1‖ * ‖1 - z‖⁻¹ ≤ 2 * ‖1 - z‖⁻¹ := by
        have : (0:ℝ) ≤ ‖1 - z‖⁻¹ := by positivity
        exact mul_le_mul_of_nonneg_right hnum this
    _ = 2 / ‖1 - z‖ := by rw [div_eq_mul_inv]

/-- The sum over `Ioc A B` is the difference of two partial sums, for `A ≤ B`. -/
private lemma sum_Ioc_eq_range_sub (f : ℕ → ℂ) (A B : ℕ) (hAB : A ≤ B) :
    (∑ m ∈ Ioc A B, f m) = ∑ m ∈ Finset.range (B + 1), f m - ∑ m ∈ Finset.range (A + 1), f m := by
  have hsub : Finset.range (A + 1) ⊆ Finset.range (B + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hset : Ioc A B = Finset.range (B + 1) \ Finset.range (A + 1) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_range, not_lt]
    omega
  have hsdiff := Finset.sum_sdiff (f := f) hsub
  rw [← hset] at hsdiff
  rw [← hsdiff]
  ring

private lemma eC_sub_int (η : ℝ) (k : ℤ) : eC η = eC (η - k) := by
  have h : η = (η - (k : ℝ)) + (k : ℝ) := by ring
  conv_lhs => rw [h]
  rw [eC_add, eC_intCast, mul_one]

private lemma norm_one_sub_eC_ge_int (η : ℝ) (k : ℤ) (hk : |η - (k : ℝ)| ≤ 1 / 2) :
    4 * |η - (k : ℝ)| ≤ ‖1 - eC η‖ := by
  rw [eC_sub_int η k]
  exact norm_one_sub_eC_ge (η - (k : ℝ)) hk

/-- Dirichlet kernel bound: `‖T(η)‖ ≤ 4/‖1 - e(η)‖`. P0015 page 363. -/
private lemma norm_T_le (P X η : ℝ) (hPX : ⌊P⌋₊ ≤ ⌊X⌋₊) (hη : eC η ≠ 1) :
    ‖T P X η‖ ≤ 4 / ‖1 - eC η‖ := by
  have hz : ‖eC η‖ = 1 := norm_eC η
  have h1 := norm_geom_sum_le (eC η) hz hη (⌊X⌋₊ + 1)
  have h2 := norm_geom_sum_le (eC η) hz hη (⌊P⌋₊ + 1)
  have hT : T P X η = ∑ m ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, eC η ^ m := by
    simp only [T]
    exact Finset.sum_congr rfl (fun m _ => eC_pow η m)
  rw [hT, sum_Ioc_eq_range_sub (fun m => eC η ^ m) ⌊P⌋₊ ⌊X⌋₊ hPX]
  calc ‖∑ m ∈ Finset.range (⌊X⌋₊ + 1), eC η ^ m - ∑ m ∈ Finset.range (⌊P⌋₊ + 1), eC η ^ m‖
      ≤ ‖∑ m ∈ Finset.range (⌊X⌋₊ + 1), eC η ^ m‖ +
          ‖∑ m ∈ Finset.range (⌊P⌋₊ + 1), eC η ^ m‖ := norm_sub_le _ _
    _ ≤ 2 / ‖1 - eC η‖ + 2 / ‖1 - eC η‖ := add_le_add h1 h2
    _ = 4 / ‖1 - eC η‖ := by ring

private lemma integral_inv_sq (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, 1 / x ^ 2) = 1 / a - 1 / b := by
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => -(1 / y)) (1 / x ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have h0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx.1)
    have h := (hasDerivAt_inv h0).const_mul (-1 : ℝ)
    have hval : (-1 : ℝ) * (-(x ^ 2)⁻¹) = 1 / x ^ 2 := by
      rw [one_div]
      ring
    rw [← hval]
    simpa [neg_div, one_div] using h
  have hcont : ContinuousOn (fun x : ℝ => 1 / x ^ 2) (Set.uIcc a b) := by
    have hne : ∀ x ∈ Set.uIcc a b, x ≠ 0 := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ne_of_gt (lt_of_lt_of_le ha hx.1)
    exact ContinuousOn.div continuousOn_const ((continuousOn_id).pow 2)
      (fun x hx => pow_ne_zero 2 (hne x hx))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  ring

private lemma card_bound (a B n : ℕ) (hnB : n ≤ B) :
    ‖(((Ioc a (n - 1 - a)).card : ℕ) : ℂ) - (n : ℂ)‖ ≤ 2 * (a : ℝ) + 2 := by
  have hcard : (Ioc a (n - 1 - a)).card = (n - 1 - a) - a := Nat.card_Ioc a (n - 1 - a)
  rw [hcard]
  have hle : (n - 1 - a) - a ≤ n := by omega
  have hdif : n - ((n - 1 - a) - a) ≤ 2 * a + 2 := by omega
  have hnorm : ‖(((n - 1 - a) - a : ℕ) : ℂ) - (n : ℂ)‖ = ((n - ((n - 1 - a) - a) : ℕ) : ℝ) := by
    have hneg : ((((n - 1 - a) - a : ℕ) : ℂ) - (n : ℂ)) = -(((n - ((n - 1 - a) - a) : ℕ) : ℂ)) := by
      push_cast [Nat.cast_sub hle]
      ring
    rw [hneg, norm_neg, Complex.norm_natCast]
  rw [hnorm]
  have hcast : ((n - ((n - 1 - a) - a) : ℕ) : ℝ) ≤ ((2 * a + 2 : ℕ) : ℝ) := by
    exact_mod_cast hdif
  have hR : ((2 * a + 2 : ℕ) : ℝ) = 2 * (a : ℝ) + 2 := by push_cast; ring
  linarith [hcast, hR.le, hR.ge]

private lemma eC_conj (x : ℝ) : eC (-x) = (starRingEnd ℂ) (eC x) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private lemma T_neg (P X : ℝ) (t : ℝ) : T P X (-t) = (starRingEnd ℂ) (T P X t) := by
  simp only [T, map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [show -t * (m : ℝ) = -(t * (m : ℝ)) by ring]
  exact eC_conj (t * (m : ℝ))

private lemma T_add_one (P X : ℝ) (t : ℝ) : T P X (t + 1) = T P X t := by
  simp only [T]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [add_mul, one_mul, eC_add]
  have hm : eC ((m : ℝ)) = 1 := by
    have h := eC_intCast (m : ℤ)
    simpa using h
  rw [hm, mul_one]

private lemma eC_neg_natCast (n : ℕ) : eC (-(n : ℝ)) = 1 := by
  have h := eC_intCast (-(n : ℤ))
  simpa using h

/-- The integrand of the arc integral is `1`-periodic. -/
private lemma F_add_one (P X : ℝ) (n : ℕ) (t : ℝ) :
    T P X (t + 1) ^ 2 * eC (-((t + 1) * (n : ℝ))) =
      T P X t ^ 2 * eC (-(t * (n : ℝ))) := by
  rw [T_add_one]
  have harg : -((t + 1) * (n : ℝ)) = -(t * (n : ℝ)) + -(n : ℝ) := by ring
  rw [harg, eC_add, eC_neg_natCast, mul_one]

private lemma eC_ne_one_of_between (η : ℝ) (h1 : 0 < η) (h2 : η < 1) : eC η ≠ 1 := by
  intro h
  unfold eC at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  have h2pi : (2 : ℂ) * ↑Real.pi * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_pos.ne')) Complex.I_ne_zero
  have hkey : (η : ℂ) * (2 * ↑Real.pi * Complex.I) = (m : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    rw [← hm]
    ring
  have hc := mul_right_cancel₀ h2pi hkey
  have hre : η = (m : ℝ) := by exact_mod_cast hc
  rw [hre] at h1 h2
  have h1' : (0 : ℤ) < m := by exact_mod_cast h1
  have h2' : m < 1 := by exact_mod_cast h2
  omega

/-- `‖T(η)‖ ≤ 1/η` on `(0, 1/2]`. -/
private lemma norm_T_le_inv (P X : ℝ) (η : ℝ) (hPX : ⌊P⌋₊ ≤ ⌊X⌋₊) (h1 : 0 < η)
    (h2 : η ≤ 1 / 2) : ‖T P X η‖ ≤ 1 / η := by
  have hne : eC η ≠ 1 := eC_ne_one_of_between η h1 (by linarith)
  have hle := norm_T_le P X η hPX hne
  have hge : 4 * η ≤ ‖1 - eC η‖ := by
    have := norm_one_sub_eC_ge η (by rw [abs_of_pos h1]; exact h2)
    rwa [abs_of_pos h1] at this
  have hpos : (0:ℝ) < 4 * η := by linarith
  calc ‖T P X η‖ ≤ 4 / ‖1 - eC η‖ := hle
    _ ≤ 4 / (4 * η) := div_le_div_of_nonneg_left (by norm_num) hpos hge
    _ = 1 / η := by field_simp

/-- `‖T(η)‖ ≤ 1/(1-η)` on `[1/2, 1)`. -/
private lemma norm_T_le_inv' (P X : ℝ) (η : ℝ) (hPX : ⌊P⌋₊ ≤ ⌊X⌋₊) (h1 : 1 / 2 ≤ η)
    (h2 : η < 1) : ‖T P X η‖ ≤ 1 / (1 - η) := by
  have hη0 : 0 < η := by linarith
  have hne : eC η ≠ 1 := eC_ne_one_of_between η hη0 h2
  have hle := norm_T_le P X η hPX hne
  have hge : 4 * (1 - η) ≤ ‖1 - eC η‖ := by
    rw [eC_sub_int η 1]
    have habs : |η - ((1 : ℤ) : ℝ)| = 1 - η := by
      rw [abs_of_neg (by push_cast; linarith)]
      ring
    have h := norm_one_sub_eC_ge (η - ((1 : ℤ) : ℝ)) (by rw [habs]; linarith)
    rw [habs] at h
    simpa using h
  have hpos : (0:ℝ) < 4 * (1 - η) := by linarith
  calc ‖T P X η‖ ≤ 4 / ‖1 - eC η‖ := hle
    _ ≤ 4 / (4 * (1 - η)) := div_le_div_of_nonneg_left (by norm_num) hpos hge
    _ = 1 / (1 - η) := by field_simp

/-- The discarded part of the period: `∫_κ^{1-κ} |T|² ≤ 2/κ`, P0015 page 363. -/
private lemma norm_integral_T_sq_le (P X : ℝ) (n : ℕ) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1 / 2)
    (hPX : ⌊P⌋₊ ≤ ⌊X⌋₊) :
    ‖∫ η in κ..(1 - κ), T P X η ^ 2 * eC (-(η * (n : ℝ)))‖ ≤ 2 / κ := by
  have hκle : κ ≤ 1 - κ := by linarith
  have hcontT : Continuous fun η : ℝ => ‖T P X η‖ ^ 2 := by
    have hc : Continuous fun η : ℝ => T P X η := by
      simp only [T]
      exact continuous_finsetSum _ (fun m _ => continuous_eC_mul ((m : ℝ)))
    exact hc.norm.pow 2
  have hmain : ‖∫ η in κ..(1 - κ), T P X η ^ 2 * eC (-(η * (n : ℝ)))‖ ≤
      ∫ η in κ..(1 - κ), ‖T P X η‖ ^ 2 := by
    calc ‖∫ η in κ..(1 - κ), T P X η ^ 2 * eC (-(η * (n : ℝ)))‖
        ≤ ∫ η in κ..(1 - κ), ‖T P X η ^ 2 * eC (-(η * (n : ℝ)))‖ :=
          intervalIntegral.norm_integral_le_integral_norm hκle
      _ = ∫ η in κ..(1 - κ), ‖T P X η‖ ^ 2 := by
          refine intervalIntegral.integral_congr (fun η _ => ?_)
          rw [norm_mul, norm_pow, norm_eC, mul_one]
  refine hmain.trans ?_
  have hInt : (∫ η in κ..(1 / 2), 1 / η ^ 2) = 1 / κ - 2 := by
    rw [integral_inv_sq κ (1 / 2) hκ0 (by linarith)]
    norm_num
  have hsplit : (∫ η in κ..(1 - κ), ‖T P X η‖ ^ 2) =
      (∫ η in κ..(1 / 2), ‖T P X η‖ ^ 2) + (∫ η in (1 / 2)..(1 - κ), ‖T P X η‖ ^ 2) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hcontT.intervalIntegrable _ _)
      (hcontT.intervalIntegrable _ _)]
  have hsubst : (∫ η in (1 / 2)..(1 - κ), ‖T P X η‖ ^ 2) = ∫ x in κ..(1 / 2), ‖T P X x‖ ^ 2 := by
    have hcomp := intervalIntegral.integral_comp_sub_left (a := κ) (b := 1 / 2)
      (f := fun η : ℝ => ‖T P X η‖ ^ 2) (1 : ℝ)
    rw [show (1:ℝ) - 1 / 2 = 1 / 2 by norm_num] at hcomp
    rw [← hcomp]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    have hper : T P X (1 - x) = T P X (-x) := by
      rw [show 1 - x = -x + 1 by ring]
      exact T_add_one P X (-x)
    rw [hper, T_neg]
    simp
  have hb : (∫ η in κ..(1 / 2), ‖T P X η‖ ^ 2) ≤ 1 / κ - 2 := by
    have hcontInv : ContinuousOn (fun x : ℝ => 1 / x ^ 2) (Set.uIcc κ (1 / 2)) := by
      apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
      intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hκ0 hx.1))
    calc (∫ η in κ..(1 / 2), ‖T P X η‖ ^ 2) ≤ ∫ η in κ..(1 / 2), 1 / η ^ 2 := by
          refine intervalIntegral.integral_mono_on (by linarith) (hcontT.intervalIntegrable _ _)
            hcontInv.intervalIntegrable (fun x hx => ?_)
          have hx1 : 0 < x := lt_of_lt_of_le hκ0 hx.1
          have hb1 := norm_T_le_inv P X x hPX hx1 hx.2
          have hnn : (0:ℝ) ≤ ‖T P X x‖ := norm_nonneg _
          calc ‖T P X x‖ ^ 2 ≤ (1 / x) ^ 2 := pow_le_pow_left₀ hnn hb1 2
            _ = 1 / x ^ 2 := by field_simp
      _ = 1 / κ - 2 := hInt
  rw [hsplit, hsubst]
  have hb' : (∫ x in κ..(1 / 2), ‖T P X x‖ ^ 2) ≤ 1 / κ - 2 := hb
  have hsum : (∫ x in κ..(1 / 2), ‖T P X x‖ ^ 2) + ∫ x in κ..(1 / 2), ‖T P X x‖ ^ 2 ≤
      (1 / κ - 2) + (1 / κ - 2) := add_le_add hb' hb'
  have hfin : (1 / κ - 2) + (1 / κ - 2) ≤ 2 / κ := by
    have hk : (0:ℝ) < κ := hκ0
    have htwo : 1 / κ + 1 / κ = 2 / κ := by ring
    linarith
  linarith [hsum, hfin]

/-- LEAF: P0015 displays (6.10) and (6.11), page 363, class MEDIUM.
`T(η) ≪ ‖η‖⁻¹` gives `∫_{1/qQ}^{1/2} |T|² ≪ qQ`, so the arc integral is
`∫_0^1 T(η)² e(-nη) dη + O(qQ) = n + O(qQ)` for `n ≤ X`, with `qQ = qX/P`. -/
theorem mv_arc_main_611 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ X ^ (6 * δ) →
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
        ‖arcIntegral (X ^ (6 * δ)) X q n - (n : ℂ)‖ ≤ C * q * (X / X ^ (6 * δ)) := by
  refine ⟨4, by norm_num, ?_⟩
  intro δ hδ hδ1
  refine ⟨32, ?_⟩
  intro X hX q hq _ n hn1 hnX
  set P := X ^ (6 * δ) with hPdef
  set κ := P / (q * X) with hκdef
  set F : ℝ → ℂ := fun η => T P X η ^ 2 * eC (-(η * (n : ℝ))) with hFdef
  have hX0 : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hP0 : (0 : ℝ) < P := Real.rpow_pos_of_pos hX0 _
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqX : (0 : ℝ) < (q : ℝ) * X := mul_pos hq0 hX0
  have hδ6 : 6 * δ ≤ 1 / 2 := by linarith
  have hδ12 : 12 * δ ≤ 1 / 2 := by linarith
  have hroot : X ^ (1 / 2 : ℝ) ≤ X / 5 := by
    rw [← Real.sqrt_eq_rpow]
    have h5 : (5 : ℝ) ≤ Real.sqrt X := by
      have h25 : Real.sqrt 25 = 5 := by
        have h : Real.sqrt 25 ^ 2 = 25 := Real.sq_sqrt (by norm_num)
        have h0 : (0:ℝ) ≤ Real.sqrt 25 := Real.sqrt_nonneg 25
        nlinarith
      rw [← h25]
      exact Real.sqrt_le_sqrt (by linarith)
    have hs : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX0.le
    have ht : (0 : ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg X
    have hprod : 0 ≤ (Real.sqrt X - 5) * Real.sqrt X :=
      mul_nonneg (by linarith) ht
    nlinarith [hs, ht, hprod]
  have hP5 : P ≤ X / 5 :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hX1 hδ6) hroot
  have hP52 : P ^ 2 ≤ X / 5 := by
    have hsq : P ^ 2 = X ^ (12 * δ) := by
      rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
      congr 1
      ring
    rw [hsq]
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hX1 hδ12) hroot
  have hPXle : P ^ 2 + P ≤ (q : ℝ) * X := by
    nlinarith [hP5, hP52, hX0, hq1]
  have hκ0 : 0 < κ := by
    rw [hκdef]
    positivity
  have hκ1 : κ ≤ 1 / 2 := by
    rw [hκdef, div_le_iff₀ hqX]
    nlinarith [hP5, hq1, hX0]
  have hκle : κ ≤ 1 - κ := by linarith
  -- the two halves of the period
  have hcontF : Continuous F := by
    rw [hFdef]
    exact (Continuous.mul
      ((by
        have hc : Continuous fun η : ℝ => T P X η := by
          simp only [T]
          exact continuous_finsetSum _ (fun m _ => continuous_eC_mul ((m : ℝ)))
        exact hc.pow 2) :
        Continuous fun η : ℝ => T P X η ^ 2)
      (by
        have hc : Continuous fun η : ℝ => eC (-(η * (n : ℝ))) := by
          apply continuous_eC.comp
          fun_prop
        exact hc))
  have hper : Function.Periodic F 1 := fun t => by
    rw [hFdef]
    exact F_add_one P X n t
  have hshift : (∫ η in (-κ)..(1 - κ), F η) = ∫ η in (0 : ℝ)..1, F η := by
    have h := hper.intervalIntegral_add_eq (-κ) 0
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hsplit : (∫ η in (-κ)..(1 - κ), F η) = (∫ η in (-κ)..κ, F η) + ∫ η in κ..(1 - κ), F η := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hcontF.intervalIntegrable _ _)
      (hcontF.intervalIntegrable _ _)]
  have hnfloor : n ≤ ⌊X⌋₊ := Nat.le_floor hnX
  have haB : ⌊P⌋₊ ≤ ⌊X⌋₊ := Nat.floor_mono (by linarith)
  have hone : (∫ η in (0 : ℝ)..1, F η) = (((Ioc ⌊P⌋₊ (n - 1 - ⌊P⌋₊)).card : ℕ) : ℂ) := by
    rw [hFdef]
    exact integral_one_period P X n hnfloor
  have hdecomp : (∫ η in (-κ)..κ, F η) =
      (((Ioc ⌊P⌋₊ (n - 1 - ⌊P⌋₊)).card : ℕ) : ℂ) - ∫ η in κ..(1 - κ), F η := by
    rw [hone] at hshift
    linear_combination hshift - hsplit
  have harc : arcIntegral P X q n = ∫ η in (-κ)..κ, F η := by
    simp only [hFdef, hκdef, arcIntegral]
  rw [harc, hdecomp]
  have hrearr : (((((Ioc ⌊P⌋₊ (n - 1 - ⌊P⌋₊)).card : ℕ) : ℂ) - ∫ η in κ..(1 - κ), F η) - (n : ℂ)) =
      ((((Ioc ⌊P⌋₊ (n - 1 - ⌊P⌋₊)).card : ℕ) : ℂ) - (n : ℂ)) - ∫ η in κ..(1 - κ), F η := by ring
  rw [hrearr]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖(((Ioc ⌊P⌋₊ (n - 1 - ⌊P⌋₊)).card : ℕ) : ℂ) - (n : ℂ)‖ ≤ 2 * (⌊P⌋₊ : ℝ) + 2 :=
    card_bound ⌊P⌋₊ ⌊X⌋₊ n hnfloor
  have h2 : ‖∫ η in κ..(1 - κ), F η‖ ≤ 2 / κ := by
    rw [hFdef]
    exact norm_integral_T_sq_le P X n κ hκ0 hκ1 haB
  have hmain2 : 2 * (⌊P⌋₊ : ℝ) + 2 ≤ 2 * ((q : ℝ) * X / P) := by
    have ha : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le hP0.le
    rw [show (2 : ℝ) * ((q : ℝ) * X / P) = (2 * ((q : ℝ) * X)) / P by ring, le_div_iff₀ hP0]
    nlinarith [ha, hPXle, hP0]
  have hkappa : 2 / κ = 2 * ((q : ℝ) * X / P) := by
    rw [hκdef]
    field_simp
  have hfinal : 2 * (⌊P⌋₊ : ℝ) + 2 + 2 / κ ≤ 4 * (q : ℝ) * (X / P) := by
    rw [hkappa]
    have heq : 2 * ((q : ℝ) * X / P) + 2 * ((q : ℝ) * X / P) = 4 * (q : ℝ) * (X / P) := by ring
    linarith [hmain2, heq.le, heq.ge]
  linarith [h1, h2, hfinal]

/-- LEAF: P0015 display (6.13), page 363, class MEDIUM.
By (5.2), `Q Σ_{q≤P} μ(q)² φ(q)⁻² |c_q(n)| q ≪ Q n φ(n)⁻¹ d(n) log P ≪ X^{1+δ} P⁻¹`, with
`Q = X/P`; the `X^δ` absorbs `d(n) log P` and needs `X` large in terms of `δ`. -/
theorem mv_truncation_613 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      (X / X ^ (6 * δ)) * ∑ q ∈ Icc 1 ⌊X ^ (6 * δ)⌋₊, ‖mainWeight q n‖ * q ≤
        C * (X ^ (1 + δ) / X ^ (6 * δ)) := by
  sorry

/-- LEAF: P0015 display (6.16), page 363, class MEDIUM.
`𝔖(n) = Σ_{q≥1} μ(q)² φ(q)⁻² c_q(-n) = ∏_{p∤n} (1 - (p-1)⁻²) ∏_{p∣n} (1 + (p-1)⁻¹)`, by (5.2);
the series converges absolutely. The `q = 0` term is zero since `μ(0) = 0`. -/
theorem mv_singular_series_616 (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun q : ℕ => ‖mainWeight q n‖) ∧
      HasSum (fun q : ℕ => mainWeight q n) ((singularSeries n : ℝ) : ℂ) := by
  sorry

/-- LEAF: P0015 display (6.14), page 363, class MEDIUM.
Extending the main term to all `q ≥ 1` costs
`n Σ_{q>P} φ(q)⁻¹ φ(q/(q,n))⁻¹ ≪ n P⁻¹ d(n) n φ(n)⁻¹ ≪ X^{1+δ} P⁻¹` for `n ≤ X`. -/
theorem mv_tail_614 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      (n : ℝ) * ∑' q : ℕ, (if X ^ (6 * δ) < (q : ℝ) then ‖mainWeight q n‖ else 0) ≤
        C * (X ^ (1 + δ) / X ^ (6 * δ)) := by
  sorry

/-- LEAF: P0015 page 366, the first display of section 7, from Lemma 4.2 (Gallagher's Lemma 1),
class MEDIUM. With `κ = 1/(rQ)`,
`W(χ) ≪ X^{1/2} max_{x≤2X} max_{0<h≤X} (h + X P⁻¹)⁻¹ |Σ^#_{x-h<p≤x} χ(p) log p|`.
Stated with any bound `M` for the double maximum; the constant is absolute. -/
theorem mv_gallagher_lemma42_step : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ X ^ (6 * δ) →
      ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive → ∀ M : ℝ,
        (∀ x h : ℝ, 0 ≤ x → x ≤ 2 * X → 0 < h → h ≤ X →
          ‖sharpSum (X ^ (6 * δ)) X χ x h‖ ≤ M * (h + X / X ^ (6 * δ))) →
        Wnorm (X ^ (6 * δ)) X χ ≤ C * Real.sqrt X * M := by
  sorry

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

#print axioms lemma2NoExcSmallDelta_of_BP
#print axioms leaf_absent_selected_of_small
#print axioms mv_arc_main_611
#print axioms mv_617
#print axioms mv_71
#print axioms lemma2NoExcSmallDelta_of_leaves

end LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit

