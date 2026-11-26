import LeanLab.ExceptionalSet.Lu2010Orth
import LeanLab.Perelli1996.PrincipalTail320
import LeanLab.PNTPort.Gallagher.Basic
import LeanLab.ExceptionalSet.MVArithmetic685
import LeanLab.Perelli1996.Series320
import LeanLab.Perelli1996.RamanujanInt400
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

/-- Montgomery and Vaughan page 363 display 6.16, the signed coefficient in the existing natural frequency normalization. -/
theorem mainWeight_eq_coefficient685 (q n : ℕ) : mainWeight q n =
    LeanLab.Perelli1996.Series320.coefficient n q := by
  have hram (q : ℕ) : ramanujan q (-(n : ℤ)) =
      LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n := by
    by_cases hq : q = 0
    · subst q
      simp [ramanujan, LeanLab.Perelli1996.Ramanujan103.ramanujanSum]
    have heq (m : ℤ) : ramanujan q m =
        LeanLab.Perelli1996.RamanujanInt400.ramanujanSumInt q m := by
      unfold ramanujan LeanLab.Perelli1996.RamanujanInt400.ramanujanSumInt
      apply Finset.sum_congr rfl
      intro a _
      unfold eC LeanLab.Perelli1996.Kernel.e
      congr 1
      push_cast
      ring
    rw [heq, LeanLab.Perelli1996.RamanujanInt400.ramanujanSumInt_eq_natAbs q
      (-(n : ℤ)) (Nat.pos_of_ne_zero hq)]
    simp
  unfold mainWeight LeanLab.Perelli1996.Series320.coefficient
  rw [hram]
  push_cast
  rfl

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

/-- LEAF: P0015 displays (6.10) and (6.11), page 363, class MEDIUM.
`T(η) ≪ ‖η‖⁻¹` gives `∫_{1/qQ}^{1/2} |T|² ≪ qQ`, so the arc integral is
`∫_0^1 T(η)² e(-nη) dη + O(qQ) = n + O(qQ)` for `n ≤ X`, with `qQ = qX/P`. -/
theorem mv_arc_main_611 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ X ^ (6 * δ) →
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
        ‖arcIntegral (X ^ (6 * δ)) X q n - (n : ℂ)‖ ≤ C * q * (X / X ^ (6 * δ)) := by
  classical
  have coefficient_cut685 (A B n : ℕ) (hn : n ≤ B) :
      (∫ α in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        (∑ p ∈ Ioc A B, LeanLab.Perelli1996.Kernel.e ((p : ℝ) * α)) ^ 2 * LeanLab.Perelli1996.Kernel.e (-(n : ℝ) * α)) =
          (((n - A - 1 - A : ℕ) : ℕ) : ℂ) := by
    classical
    have hterm (p q : ℕ) :
        (∫ α in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          LeanLab.Perelli1996.Kernel.e ((p : ℝ) * α) * LeanLab.Perelli1996.Kernel.e ((q : ℝ) * α) * LeanLab.Perelli1996.Kernel.e (-(n : ℝ) * α)) =
        if p + q = n then 1 else 0 := by
      have heq (α : ℝ) :
          LeanLab.Perelli1996.Kernel.e ((p : ℝ) * α) * LeanLab.Perelli1996.Kernel.e ((q : ℝ) * α) * LeanLab.Perelli1996.Kernel.e (-(n : ℝ) * α) =
          LeanLab.ExceptionalSet.Lu2010Orth.ee ((((p : ℤ) + q - n : ℤ) : ℝ) * α) := by
        rw [← LeanLab.Perelli1996.Parseval103.e_add, ← LeanLab.Perelli1996.Parseval103.e_add]
        unfold LeanLab.Perelli1996.Kernel.e LeanLab.ExceptionalSet.Lu2010Orth.ee
        congr 1
        push_cast
        ring
      simp_rw [heq]
      have h := LeanLab.ExceptionalSet.Lu2010Orth.integral_ee ((p : ℤ) + q - n) (-1 / 2)
      norm_num only [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
      rw [neg_div, h]
      have hz : ((p : ℤ) + q - n = 0) ↔ p + q = n := by omega
      rw [if_congr hz rfl rfl]
    have hexpand (α : ℝ) :
        (∑ p ∈ Ioc A B, LeanLab.Perelli1996.Kernel.e ((p : ℝ) * α)) ^ 2 * LeanLab.Perelli1996.Kernel.e (-(n : ℝ) * α) =
        ∑ p ∈ Ioc A B, ∑ q ∈ Ioc A B,
          LeanLab.Perelli1996.Kernel.e ((p : ℝ) * α) * LeanLab.Perelli1996.Kernel.e ((q : ℝ) * α) * LeanLab.Perelli1996.Kernel.e (-(n : ℝ) * α) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    have hint (p q : ℕ) : IntervalIntegrable (fun α : ℝ =>
        LeanLab.Perelli1996.Kernel.e ((p : ℝ) * α) * LeanLab.Perelli1996.Kernel.e ((q : ℝ) * α) * LeanLab.Perelli1996.Kernel.e (-(n : ℝ) * α))
        MeasureTheory.volume (-1 / 2) (1 / 2) := by
      apply Continuous.intervalIntegrable
      unfold LeanLab.Perelli1996.Kernel.e
      fun_prop
    simp_rw [hexpand]
    rw [intervalIntegral.integral_finsetSum (fun p _ =>
      (Continuous.intervalIntegrable (by unfold LeanLab.Perelli1996.Kernel.e; fun_prop)) (-1 / 2) (1 / 2))]
    simp_rw [intervalIntegral.integral_finsetSum (fun q _ => hint _ q), hterm]
    have hinner (p : ℕ) (hp : p ∈ Ioc A B) :
        (∑ q ∈ Ioc A B, if p + q = n then (1 : ℂ) else 0) =
          if p + A < n then 1 else 0 := by
      simp only [mem_Ioc] at hp
      by_cases h : p + A < n
      · rw [if_pos h, Finset.sum_eq_single (n - p)]
        · simp [Nat.add_sub_of_le (show p ≤ n by omega)]
        · intro q hq hne
          rw [if_neg (by omega)]
        · intro hnot
          have hmem : n - p ∈ Ioc A B := by simp only [mem_Ioc]; omega
          exact (hnot hmem).elim
      · rw [if_neg h]
        apply Finset.sum_eq_zero
        intro q hq
        simp only [mem_Ioc] at hq
        rw [if_neg (by omega)]
    rw [Finset.sum_congr rfl hinner]
    have hsub : Ioc A (n - A - 1) ⊆ Ioc A B := by
      intro p hp
      simp only [mem_Ioc] at hp ⊢
      omega
    rw [← Finset.sum_subset hsub]
    · have heq : (∑ p ∈ Ioc A (n - A - 1), if p + A < n then (1 : ℂ) else 0) =
          ∑ _p ∈ Ioc A (n - A - 1), (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [mem_Ioc] at hp
        rw [if_pos (by omega)]
      rw [heq]
      simp
    · intro p hp hpnot
      simp only [mem_Ioc] at hp hpnot
      rw [if_neg (by omega)]

  have kernel_form685 (A B : ℕ) (α : ℝ) :
      (∑ p ∈ Ioc A B, LeanLab.Perelli1996.Kernel.e ((p : ℝ) * α)) = LeanLab.Perelli1996.Kernel.T (A + 1) (B - A) α := by
    have hset : Ioc A B = Ico (A + 1) (B + 1) := by ext n; simp only [mem_Ioc, mem_Ico]; omega
    rw [hset, Finset.sum_Ico_eq_sum_range]
    have hlen : B + 1 - (A + 1) = B - A := by omega
    rw [hlen]
    rfl

  have arc_cut_error685 (A B n : ℕ) (hn : n ≤ B) (δ : ℝ)
      (hδ : 0 < δ) (hhalf : δ ≤ 1 / 2) :
      ‖(∫ α in (-δ)..δ,
        (∑ p ∈ Ioc A B, LeanLab.Perelli1996.Kernel.e ((p : ℝ) * α)) ^ 2 * LeanLab.Perelli1996.Kernel.e (-(n : ℝ) * α)) - (n : ℂ)‖ ≤
          2 * A + 1 + 1 / (2 * δ) := by
    let f : ℝ → ℂ := fun α =>
      (∑ p ∈ Ioc A B, LeanLab.Perelli1996.Kernel.e ((p : ℝ) * α)) ^ 2 * LeanLab.Perelli1996.Kernel.e (-(n : ℝ) * α)
    have hcont : Continuous f := by dsimp [f]; unfold LeanLab.Perelli1996.Kernel.e; fun_prop
    have hnorm (α : ℝ) : ‖f α‖ = ‖LeanLab.Perelli1996.Kernel.T (A + 1) (B - A) α‖ ^ 2 := by
      dsimp [f]
      rw [kernel_form685, norm_mul, norm_pow]
      simp [LeanLab.Perelli1996.Kernel.e, Complex.norm_exp]
    have h12 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hcont.intervalIntegrable (-1 / 2) (-δ)) (hcont.intervalIntegrable (-δ) δ)
    have h23 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hcont.intervalIntegrable (-1 / 2) δ) (hcont.intervalIntegrable δ (1 / 2))
    let K : ℕ := n - A - 1 - A
    have hs : ((∫ α in (-1 / 2 : ℝ)..(-δ), f α) + ∫ α in (-δ)..δ, f α) +
        (∫ α in δ..(1 / 2 : ℝ), f α) = (K : ℂ) := by
      rw [h12, h23]
      exact coefficient_cut685 A B n hn
    have heq : (∫ α in (-δ)..δ, f α) - (n : ℂ) =
        ((K : ℂ) - n) - ((∫ α in (-1 / 2 : ℝ)..(-δ), f α) + ∫ α in δ..(1 / 2 : ℝ), f α) := by
      linear_combination hs
    have hK : K ≤ n := by dsimp [K]; omega
    have hKn : n - K ≤ 2 * A + 1 := by dsimp [K]; omega
    have hkd : ‖(K : ℂ) - n‖ ≤ (2 * A + 1 : ℝ) := by
      rw [norm_sub_rev, ← Nat.cast_sub hK, Complex.norm_natCast]
      exact_mod_cast hKn
    have hl := intervalIntegral.norm_integral_le_integral_norm
      (f := f) (μ := MeasureTheory.volume) (by linarith : (-1 / 2 : ℝ) ≤ -δ)
    have hr := intervalIntegral.norm_integral_le_integral_norm
      (f := f) (μ := MeasureTheory.volume) hhalf
    simp_rw [hnorm] at hl hr
    have htail := LeanLab.Perelli1996.Kernel.integral_norm_T_sq_two_tails (A + 1) (B - A) hδ hhalf
    change ‖(∫ α in (-δ)..δ, f α) - (n : ℂ)‖ ≤ _
    rw [heq]
    calc
      _ ≤ ‖(K : ℂ) - n‖ + ‖(∫ α in (-1 / 2 : ℝ)..(-δ), f α) +
          ∫ α in δ..(1 / 2 : ℝ), f α‖ := norm_sub_le _ _
      _ ≤ (2 * A + 1 : ℝ) + (‖∫ α in (-1 / 2 : ℝ)..(-δ), f α‖ +
          ‖∫ α in δ..(1 / 2 : ℝ), f α‖) := by
        have hnormadd := norm_add_le (∫ α in (-1 / 2 : ℝ)..(-δ), f α)
          (∫ α in δ..(1 / 2 : ℝ), f α)
        linarith
      _ ≤ (2 * A + 1 : ℝ) + ((∫ α in (-1 / 2 : ℝ)..(-δ), ‖LeanLab.Perelli1996.Kernel.T (A + 1) (B - A) α‖ ^ 2) +
          ∫ α in δ..(1 / 2 : ℝ), ‖LeanLab.Perelli1996.Kernel.T (A + 1) (B - A) α‖ ^ 2) := by linarith
      _ ≤ _ := by linarith
  refine ⟨4, by norm_num, fun δ hδ hδ' => ⟨16, fun X hX q hq _ n _ hnX => ?_⟩⟩
  have hephase (α : ℝ) (p : ℕ) : eC (α * p) = LeanLab.Perelli1996.Kernel.e ((p : ℝ) * α) := by
    unfold eC LeanLab.Perelli1996.Kernel.e
    congr 1
    push_cast
    ring
  have hefreq (α : ℝ) : eC (-(α * n)) = LeanLab.Perelli1996.Kernel.e (-(n : ℝ) * α) := by
    unfold eC LeanLab.Perelli1996.Kernel.e
    congr 1
    push_cast
    ring
  unfold arcIntegral T
  simp_rw [hephase, hefreq]
  let P : ℝ := X ^ (6 * δ)
  have hXp : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hP : 1 ≤ P := Real.one_le_rpow hX1 (by positivity)
  have hPp : 0 < P := by linarith
  have hPX : P ^ 2 ≤ X := by
    dsimp [P]
    rw [← Real.rpow_mul_natCast hXp.le]
    calc
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num; linarith)
      _ = X := Real.rpow_one X
  have h4P : 4 * P ≤ X := by by_cases h : P ≤ 4 <;> nlinarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqp : (0 : ℝ) < q := by linarith
  have hd : 0 < P / ((q : ℝ) * X) := by positivity
  have hhalf : P / ((q : ℝ) * X) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hnB : n ≤ ⌊X⌋₊ := Nat.le_floor hnX
  have hb := arc_cut_error685 ⌊P⌋₊ ⌊X⌋₊ n hnB (P / ((q : ℝ) * X)) hd hhalf
  have hPi : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le hPp.le
  have hPQ : P ≤ X / P := (le_div_iff₀ hPp).mpr (by nlinarith [hPX])
  have hQ : 1 ≤ X / P := hP.trans hPQ
  have hqQ : X / P ≤ (q : ℝ) * (X / P) := by nlinarith
  have he : 1 / (2 * (P / ((q : ℝ) * X))) = (q : ℝ) * (X / P) / 2 := by field_simp
  change ‖(∫ α in (-(P / ((q : ℝ) * X)))..(P / ((q : ℝ) * X)),
      (∑ p ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, LeanLab.Perelli1996.Kernel.e ((p : ℝ) * α)) ^ 2 *
        LeanLab.Perelli1996.Kernel.e (-(n : ℝ) * α)) - (n : ℂ)‖ ≤ _
  apply hb.trans
  rw [he]
  nlinarith

/-- LEAF: P0015 display (6.13), page 363, class MEDIUM.
By (5.2), `Q Σ_{q≤P} μ(q)² φ(q)⁻² |c_q(n)| q ≪ Q n φ(n)⁻¹ d(n) log P ≪ X^{1+δ} P⁻¹`, with
`Q = X/P`; the `X^δ` absorbs `d(n) log P` and needs `X` large in terms of `δ`. -/
theorem mv_truncation_613 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      (X / X ^ (6 * δ)) * ∑ q ∈ Icc 1 ⌊X ^ (6 * δ)⌋₊, ‖mainWeight q n‖ * q ≤
        C * (X ^ (1 + δ) / X ^ (6 * δ)) := by
  have weighted_identity (a : ℕ → ℝ) (L : ℕ) :
      (∑ q ∈ Icc 1 L, (q : ℝ) * a q) = ∑ r ∈ Icc 1 L, ∑ q ∈ Icc r L, a q := by
    induction L with
    | zero => simp
    | succ L ih =>
      have inner : (∑ r ∈ Icc 1 L, ∑ q ∈ Icc r (L + 1), a q) =
          (∑ r ∈ Icc 1 L, ∑ q ∈ Icc r L, a q) + (L : ℝ) * a (L + 1) := by
        calc
          _ = ∑ r ∈ Icc 1 L, ((∑ q ∈ Icc r L, a q) + a (L + 1)) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [Finset.sum_Icc_succ_top (by have := (Finset.mem_Icc.mp hr).2; omega)]
          _ = _ := by simp [Finset.sum_add_distrib]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ L + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ L + 1), inner, ih]
      simp
      ring
  obtain ⟨K, hK, ht⟩ := LeanLab.Perelli1996.InverseTotient320.inverse_totient_sq_tail
  refine ⟨2 * K, by positivity, fun δ hδ hδhi => ?_⟩
  have he : (0 : ℝ) < δ / 2 := by positivity
  obtain ⟨X₀, hweight⟩ := LeanLab.ExceptionalSet.Task685.divisor_weight_eventually (δ / 2) he
  obtain ⟨X₁, hloglim⟩ := eventually_atTop.mp
    ((isLittleO_log_rpow_atTop he).bound (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨X₂, hpowlim⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop he).eventually_ge_atTop (2 : ℝ))
  refine ⟨max 2 (max X₀ (max X₁ X₂)), fun X hX n hn hnX => ?_⟩
  obtain ⟨hX2, hXrest⟩ := max_le_iff.mp hX
  obtain ⟨hX0, hXrest⟩ := max_le_iff.mp hXrest
  obtain ⟨hX1, hXpow⟩ := max_le_iff.mp hXrest
  have hXp : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hXone
  have hXe : 0 ≤ X ^ (δ / 2) := by positivity
  have hl : Real.log X ≤ (1 / 2 : ℝ) * X ^ (δ / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogX, abs_of_nonneg hXe] using hloglim X hX1
  have hp2 : 2 ≤ X ^ (δ / 2) := hpowlim X hXpow
  let P : ℝ := X ^ (6 * δ)
  have hP1 : 1 ≤ P := Real.one_le_rpow hXone (by positivity)
  have hP : 0 < P := by linarith
  have hlogP : Real.log P ≤ Real.log X := by
    dsimp [P]
    rw [Real.log_rpow hXp]
    nlinarith
  have hlogbound : 1 + Real.log P ≤ X ^ (δ / 2) := by linarith
  have hwgt := hweight X hX0 n hn hnX
  have hw0 : 0 ≤ (n : ℝ) * n.divisors.card / n.totient := by positivity
  have hpart (r : ℕ) (hr : r ∈ Icc 1 ⌊P⌋₊) :
      (∑ q ∈ Icc r ⌊P⌋₊, ‖mainWeight q n‖) ≤
        2 * K * ((n : ℝ) * n.divisors.card / n.totient) / r := by
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrp : (0 : ℝ) < r := by exact_mod_cast hr1
    have hqp (q : ℕ) (hq : q ∈ Icc r ⌊P⌋₊) : 0 < q ∧ (r : ℝ) / 2 < q := by
      have hrq : (r : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
      have hq0 : (0 : ℝ) < q := hrp.trans_le hrq
      exact ⟨by exact_mod_cast hq0, by linarith⟩
    calc
      _ ≤ ∑ q ∈ Icc r ⌊P⌋₊, 1 / ((q.totient : ℝ) * (q / Nat.gcd q n).totient) := by
        apply Finset.sum_le_sum
        intro q hq
        rw [mainWeight_eq_coefficient685]
        exact LeanLab.Perelli1996.Ramanujan400.norm_weighted_ramanujanSum_le q n (hqp q hq).1
      _ ≤ K / ((r : ℝ) / 2) * ((n : ℝ) * n.divisors.card / n.totient) :=
        LeanLab.Perelli1996.Tail320.finite_totient_tail n (by omega) _ K (by positivity) ht _ hqp
      _ = _ := by ring
  have hh : (∑ r ∈ Icc 1 ⌊P⌋₊, 1 / (r : ℝ)) ≤ 1 + Real.log P := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div] using
      harmonic_floor_le_one_add_log P hP1
  have hsum : (∑ q ∈ Icc 1 ⌊P⌋₊, ‖mainWeight q n‖ * q) ≤ 2 * K * X ^ δ := by
    calc
      _ = ∑ r ∈ Icc 1 ⌊P⌋₊, ∑ q ∈ Icc r ⌊P⌋₊, ‖mainWeight q n‖ := by
        rw [← weighted_identity]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ ≤ ∑ r ∈ Icc 1 ⌊P⌋₊, 2 * K * ((n : ℝ) * n.divisors.card / n.totient) / r :=
        Finset.sum_le_sum hpart
      _ = (2 * K * ((n : ℝ) * n.divisors.card / n.totient)) *
          (∑ r ∈ Icc 1 ⌊P⌋₊, 1 / (r : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ ≤ (2 * K * ((n : ℝ) * n.divisors.card / n.totient)) * (1 + Real.log P) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = 2 * K * (((n : ℝ) * n.divisors.card / n.totient) * (1 + Real.log P)) := by ring
      _ ≤ 2 * K * (X ^ (δ / 2) * X ^ (δ / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hwgt hlogbound (by linarith [Real.log_nonneg hP1]) hXe
      _ = 2 * K * X ^ δ := by rw [← Real.rpow_add hXp]; congr 2; ring
  calc
    _ ≤ (X / P) * (2 * K * X ^ δ) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * K * (X ^ (1 + δ) / P) := by rw [Real.rpow_add hXp, Real.rpow_one]; ring

/-- LEAF: P0015 display (6.16), page 363, class MEDIUM.
`𝔖(n) = Σ_{q≥1} μ(q)² φ(q)⁻² c_q(-n) = ∏_{p∤n} (1 - (p-1)⁻²) ∏_{p∣n} (1 + (p-1)⁻¹)`, by (5.2);
the series converges absolutely. The `q = 0` term is zero since `μ(0) = 0`. -/
theorem mv_singular_series_616 (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun q : ℕ => ‖mainWeight q n‖) ∧
      HasSum (fun q : ℕ => mainWeight q n) ((singularSeries n : ℝ) : ℂ) := by
  have hs : singularSeries n = LeanLab.Perelli1996.Sing n := by
    rfl
  simp_rw [mainWeight_eq_coefficient685]
  have hnorm := LeanLab.Perelli1996.Series320.summable_norm_coefficient n (by omega)
  refine ⟨hnorm, ?_⟩
  rw [hs, ← LeanLab.Perelli1996.Series320.tsum_coefficient n (by omega)]
  exact hnorm.of_norm.hasSum

/-- LEAF: P0015 display (6.14), page 363, class MEDIUM.
Extending the main term to all `q ≥ 1` costs
`n Σ_{q>P} φ(q)⁻¹ φ(q/(q,n))⁻¹ ≪ n P⁻¹ d(n) n φ(n)⁻¹ ≪ X^{1+δ} P⁻¹` for `n ≤ X`. -/
theorem mv_tail_614 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      (n : ℝ) * ∑' q : ℕ, (if X ^ (6 * δ) < (q : ℝ) then ‖mainWeight q n‖ else 0) ≤
        C * (X ^ (1 + δ) / X ^ (6 * δ)) := by
  obtain ⟨K, hK, ht⟩ := LeanLab.Perelli1996.InverseTotient320.inverse_totient_sq_tail
  refine ⟨K, hK, fun δ hδ _ => ?_⟩
  obtain ⟨X₀, hweight⟩ := LeanLab.ExceptionalSet.Task685.divisor_weight_eventually δ hδ
  refine ⟨max X₀ 1, fun X hX n hn hnX => ?_⟩
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hXp : 0 < X := by linarith
  have hP : 0 < X ^ (6 * δ) := Real.rpow_pos_of_pos hXp _
  have hwgt := hweight X ((le_max_left _ _).trans hX) n hn hnX
  have htail : (∑' q : ℕ, if X ^ (6 * δ) < (q : ℝ) then ‖mainWeight q n‖ else 0) ≤
      K / X ^ (6 * δ) * ((n : ℝ) * n.divisors.card / n.totient) := by
    apply Real.tsum_le_of_sum_le (fun q => by split_ifs <;> positivity)
    intro s
    rw [← Finset.sum_filter]
    have hqpos (q : ℕ) (hq : q ∈ s.filter (fun q : ℕ => X ^ (6 * δ) < (q : ℝ))) : 0 < q := by
      have hqR : (0 : ℝ) < q := hP.trans (Finset.mem_filter.mp hq).2
      exact_mod_cast hqR
    calc
      _ ≤ ∑ q ∈ s.filter (fun q : ℕ => X ^ (6 * δ) < (q : ℝ)),
          1 / ((q.totient : ℝ) * (q / Nat.gcd q n).totient) := by
        apply Finset.sum_le_sum
        intro q hq
        rw [mainWeight_eq_coefficient685]
        exact LeanLab.Perelli1996.Ramanujan400.norm_weighted_ramanujanSum_le q n (hqpos q hq)
      _ ≤ _ := LeanLab.Perelli1996.Tail320.finite_totient_tail n (by omega) (X ^ (6 * δ)) K hP ht _
        (fun q hq => ⟨hqpos q hq, (Finset.mem_filter.mp hq).2⟩)
  calc
    _ ≤ (n : ℝ) * (K / X ^ (6 * δ) * ((n : ℝ) * n.divisors.card / n.totient)) :=
      mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg n)
    _ ≤ X * (K / X ^ (6 * δ) * X ^ δ) :=
      mul_le_mul hnX (mul_le_mul_of_nonneg_left hwgt (by positivity))
        (by positivity) (by positivity)
    _ = K * (X ^ (1 + δ) / X ^ (6 * δ)) := by
      rw [Real.rpow_add hXp, Real.rpow_one]
      ring

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
  classical
  have sum_form685 {r : ℕ} (P X η : ℝ) (χ : DirichletCharacter ℂ r) :
    Wchi P X χ η = ∑ n ∈ Ioc ⌊P⌋₊ ⌊X⌋₊,
      ((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
        if χ = 1 then 1 else 0) * eC (η * n) := by
    classical
    by_cases hχ : χ = 1
    all_goals simp [Wchi, Schi, T, hχ, Finset.sum_sub_distrib, Finset.sum_filter,
      sub_mul, ite_mul]

  have window_form685 {r : ℕ} (P X : ℝ) (χ : DirichletCharacter ℂ r) (m L : ℕ) :
    LeanLab.PNTPort.Gallagher.win (fun n => if n ∈ Ioc ⌊P⌋₊ ⌊X⌋₊ then
      ((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
        if χ = 1 then 1 else 0) else 0) (⌊X⌋₊ + 1) L m =
      sharpSum P X χ (m : ℝ) L := by
    classical
    unfold LeanLab.PNTPort.Gallagher.win sharpSum
    rw [Finset.sum_filter, Finset.sum_filter]
    have hsub : Ioc ⌊P⌋₊ ⌊X⌋₊ ⊆ range (⌊X⌋₊ + 1) := by
      intro n hn
      simp only [mem_Ioc] at hn
      simp only [mem_range]
      omega
    calc
      _ = ∑ n ∈ Ioc ⌊P⌋₊ ⌊X⌋₊,
          if n ≤ m ∧ m < n + L then
            (if n ∈ Ioc ⌊P⌋₊ ⌊X⌋₊ then
              ((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
                if χ = 1 then 1 else 0) else 0) else 0 := by
        exact (Finset.sum_subset hsub (by intro n hn hn'; simp [hn'])).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [hn, ite_true]
        congr 1
        apply propext
        constructor
        · intro h
          constructor
          · exact_mod_cast (show (m : ℤ) - L < n by omega)
          · exact_mod_cast h.1
        · intro h
          have h₁ : (n : ℝ) + L > m := by linarith [h.1]
          constructor
          · exact_mod_cast h.2
          · exact_mod_cast h₁

  have wnorm_generic685 {r : ℕ} (P X M : ℝ) (χ : DirichletCharacter ℂ r)
      (hX : 16 ≤ X) (hP : 1 ≤ P) (hPX : P ^ 2 ≤ X) (hr : 1 ≤ r)
      (hsharp : ∀ x h : ℝ, 0 ≤ x → x ≤ 2 * X → 0 < h → h ≤ X →
        ‖sharpSum P X χ x h‖ ≤ M * (h + X / P)) :
      Wnorm P X χ ≤ 10 * Real.pi * Real.sqrt X * M := by
    classical
    have hXp : 0 < X := by linarith
    have hPp : 0 < P := by linarith
    have h4P : 4 * P ≤ X := by
      by_cases h : P ≤ 4
      · nlinarith
      · nlinarith
    let L : ℕ := ⌊X / (2 * P)⌋₊
    have hratio : 2 ≤ X / (2 * P) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hLp : 0 < L := Nat.floor_pos.mpr (by linarith)
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hLp
    have hLle : (L : ℝ) ≤ X / (2 * P) := Nat.floor_le (by positivity)
    have hLlt : X / (2 * P) < (L : ℝ) + 1 := Nat.lt_floor_add_one _
    have hLlow : X / P ≤ 4 * L := by
      have : X / P = 2 * (X / (2 * P)) := by field_simp
      rw [this]
      linarith
    have hLX : (L : ℝ) ≤ X := by
      apply hLle.trans
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hM : 0 ≤ M := by
      have h := hsharp 0 1 (by norm_num) (by linarith) (by norm_num) (by linarith)
      have hd : 0 < 1 + X / P := by positivity
      nlinarith [norm_nonneg (sharpSum P X χ 0 1)]
    let a : ℕ → ℂ := fun n => if n ∈ Ioc ⌊P⌋₊ ⌊X⌋₊ then
      ((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
        if χ = 1 then 1 else 0) else 0
    let N : ℕ := ⌊X⌋₊ + 1
    have hsum (η : ℝ) : Wchi P X χ η =
        ∑ n ∈ range N, a n * LeanLab.PNTPort.LargeSieve.e (n * η) := by
      rw [sum_form685]
      have he (n : ℕ) : eC (η * n) = LeanLab.PNTPort.LargeSieve.e (n * η) := by
        unfold eC LeanLab.PNTPort.LargeSieve.e
        congr 1
        push_cast
        ring
      simp_rw [he]
      have hsub : Ioc ⌊P⌋₊ ⌊X⌋₊ ⊆ range N := by
        intro n hn
        simp only [mem_Ioc] at hn
        simp only [mem_range, N]
        omega
      calc
        _ = ∑ n ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, a n * LeanLab.PNTPort.LargeSieve.e (n * η) := by
          apply Finset.sum_congr rfl
          intro n hn
          simp only [a, if_pos hn]
        _ = _ := Finset.sum_subset hsub (by intro n hn hn'; simp only [a, if_neg hn', zero_mul])
    have hcount : ((N + L : ℕ) : ℝ) ≤ 3 * X := by
      have hf := Nat.floor_le hXp.le
      dsimp [N]
      push_cast
      linarith
    have hwin (m : ℕ) (hm : m ∈ range (N + L)) : ‖LeanLab.PNTPort.Gallagher.win a N L m‖ ≤ 5 * L * M := by
      have hmN : m ≤ ⌊X⌋₊ + L := by simp only [mem_range, N] at hm; omega
      have hmx : (m : ℝ) ≤ 2 * X := by
        have hmR : (m : ℝ) ≤ (⌊X⌋₊ : ℝ) + L := by exact_mod_cast hmN
        have hf := Nat.floor_le hXp.le
        linarith
      have hw : LeanLab.PNTPort.Gallagher.win a N L m = sharpSum P X χ m L := window_form685 P X χ m L
      rw [hw]
      calc
        _ ≤ M * ((L : ℝ) + X / P) := hsharp m L (Nat.cast_nonneg _) hmx (by exact_mod_cast hLp) hLX
        _ ≤ 5 * L * M := by nlinarith
    have hsumBound : ∑ m ∈ range (N + L), ‖LeanLab.PNTPort.Gallagher.win a N L m‖ ^ 2 ≤
        (N + L : ℕ) * (5 * (L : ℝ) * M) ^ 2 := by
      calc
        _ ≤ ∑ _m ∈ range (N + L), (5 * (L : ℝ) * M) ^ 2 :=
          Finset.sum_le_sum (fun m hm => pow_le_pow_left₀ (norm_nonneg _) (hwin m hm) 2)
        _ = _ := by simp
    have hb : P / X ≤ 1 / (2 * L) := by
      rw [div_le_div_iff₀ hXp (by positivity)]
      have hh := (le_div_iff₀ (show 0 < 2 * P by positivity)).mp hLle
      nlinarith
    have ha : 0 ≤ P / ((r : ℝ) * X) := by positivity
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hab : P / ((r : ℝ) * X) ≤ 1 / (2 * L) := by
      apply le_trans _ hb
      apply div_le_div_of_nonneg_left hPp.le hXp
      nlinarith
    have hc : Continuous (fun η : ℝ => ‖Wchi P X χ η‖ ^ 2) := by
      simp_rw [hsum]
      unfold LeanLab.PNTPort.LargeSieve.e
      fun_prop
    have hg := LeanLab.PNTPort.Gallagher.gallagher a N L hLp
    simp_rw [← hsum] at hg
    have hi : (∫ η in (-(P / ((r : ℝ) * X)))..(P / ((r : ℝ) * X)), ‖Wchi P X χ η‖ ^ 2) ≤
        (Real.pi / (2 * L)) ^ 2 * ((N + L : ℕ) : ℝ) * (5 * (L : ℝ) * M) ^ 2 := by
      calc
        _ ≤ ∫ η in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖Wchi P X χ η‖ ^ 2 :=
          intervalIntegral.integral_mono_interval (neg_le_neg hab) (by linarith) hab
            (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) (hc.intervalIntegrable _ _)
        _ ≤ _ := hg.trans (by nlinarith [mul_le_mul_of_nonneg_left hsumBound (sq_nonneg (Real.pi / (2 * L)))])
    have hbound : (∫ η in (-(P / ((r : ℝ) * X)))..(P / ((r : ℝ) * X)), ‖Wchi P X χ η‖ ^ 2) ≤
        (10 * Real.pi * Real.sqrt X * M) ^ 2 := by
      calc
        _ ≤ _ := hi
        _ = (25 / 4 : ℝ) * Real.pi ^ 2 * ((N + L : ℕ) : ℝ) * M ^ 2 := by
          field_simp
          ring
        _ ≤ (25 / 4 : ℝ) * Real.pi ^ 2 * (3 * X) * M ^ 2 := by gcongr
        _ ≤ _ := by
          rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hXp.le]
          have hz : 0 ≤ Real.pi ^ 2 * X * M ^ 2 := by positivity
          nlinarith
    unfold Wnorm
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hbound⟩
  refine ⟨10 * Real.pi, by positivity, fun δ hδ hδ' => ⟨16, fun X hX r hr _ χ _ M hM => ?_⟩⟩
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hP : 1 ≤ X ^ (6 * δ) := Real.one_le_rpow hX1 (by positivity)
  have hPX : (X ^ (6 * δ)) ^ 2 ≤ X := by
    rw [← Real.rpow_mul_natCast hXp.le]
    calc
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num; linarith)
      _ = X := Real.rpow_one X
  exact wnorm_generic685 _ _ _ χ hX hP hPX hr hM

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
  intro a ha
  have h_exp_ratio : ∀ {X δ : ℝ}, 1 < X → 0 < δ → Real.exp (-(1 * Real.log X / Real.log (X ^ (6 * δ)))) = Real.exp (-(1 / (6 * δ))) := by
    intro X hX δ hδ
    have hlogP : Real.log (X ^ (6 * δ)) = 6 * δ * Real.log X := by
      rw [Real.log_rpow (by positivity)]; <;> ring_nf
      <;> norm_num at *
      <;> linarith
    calc
      Real.exp (-(1 * Real.log X / Real.log (X ^ (6 * δ)))) = Real.exp (-(Real.log X / (6 * δ * Real.log X))) := by rw [hlogP]; field_simp
      _ = Real.exp (-(1 / (6 * δ))) := by
        have h : Real.log X ≠ 0 := by
          have h₁ : Real.log X > 0 := Real.log_pos hX
          linarith
        field_simp [h]
        <;> ring_nf
        <;> field_simp [h]
        <;> linarith
  -- The exp factor is constant in X once P = X^(6δ): exp(-c₃ log X / log P) = exp(-c₃/(6δ)).
  -- The remaining content is Gallagher 1970 Theorem 7 / MV 1975 Lemma 4.3:
  -- Σ_{r≤P} Σ*_χ sup_{x,h} ‖sharpSum‖/(h + X/P) ≪ exp(-c₃/(6δ)), uniformly in X.
  -- This requires:
  --   (1) a zero-free region for complex zeros of L(s, χ), |γ| ≥ 2 (have: ZeroFree.lean)
  --   (2) an explicit formula for ψ(x, χ) in terms of zeros (partial: PsiChi/Assembly.lean)
  --   (3) Gallagher's density theorem / large sieve summed over all primitive characters (missing)
  --   (4) a short-interval PNT for the r = 1 principal character (missing)
  -- None of (3) or (4) exists in Mathlib or this lab; the lab's Gallagher module has only
  -- Gallagher's Lemma 1 (the basic large sieve inequality), not Theorem 7.
  -- Attempting to construct M as the supremum over windows satisfies the first conjunct by
  -- definition, but the second conjunct (sum of suprema bounded by a constant in X) is exactly
  -- the missing analytic input.
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
#print axioms mv_617
#print axioms mv_71
#print axioms lemma2NoExcSmallDelta_of_leaves

end LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit
