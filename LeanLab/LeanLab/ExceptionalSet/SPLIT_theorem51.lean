/-
Split of `theorem51` of `LeanLab.ExceptionalSet.BhowmikGrimmelt2026` into two leaves.

`theorem51` asserts `PowerSaving`, that is `E X ≤ C X^{1-δ}` for one `δ > 0`. The lab's circle
method frame reduces it to two analytic inputs on the concrete data of the power saving route:
`M = 2x + 1`, `Φ(j) = log p` on the primes `p ≤ x`, the minor arcs the complement of the major
arcs at level `Q = x^{1/10}`, and the level `T = M x / 4`.

* LEAF 1, the counting half: the even `n` in the window `(x/2, x]` whose major arc part has
  modulus at most `T` number at most `C x^θ` with `θ < 1`. This is where the enlarged arcs
  `q ≤ x^{1/10}` are paid for, by the large sieve and a zero density bound.
* LEAF 2, the mean value half: `M` times the fourth moment of the exponential sum over the
  minor arcs, divided by `T²`, is at most `C x^θ` with `θ < 1`.

`bad_le_skeleton` covers the exceptional evens of the window by those two counts, and
`powerBound_of_window` sums the window bound over the dyadic halvings to `E`. Both are proved
in the modules imported below, so the assembly carries no input of its own beyond the leaves.
Neither leaf alone gives `PowerSaving`: the skeleton needs the two together.

Every leaf is OPEN. The assembly `theorem51_split` has no sorry and does not use `theorem51`.
UPDATE (proving run): LEAF 2 `minor_arc_l4_power` is now PROVED from `MVVinogradovProved`;
LEAF 1 `major_arc_count_power` is still OPEN (see the run report).
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.BhowmikGrimmelt2026
import LeanLab.ExceptionalSet.MVConditional
import LeanLab.ExceptionalSet.MVEstermann
-- The one import added by the proving run: Vaughan's Theorem 3.1 (Vaughan, Hardy-Littlewood
-- Method, Thm 3.1) in the dft form `VinogradovDFT`, PROVED in the lab as
-- `vinogradovDFT_proved`, axiom-clean. Needed by LEAF 2 on the minor arcs.
import LeanLab.ExceptionalSet.MVVinogradovProved

namespace LeanLab.ExceptionalSet.BG2026
open Real Finset ArithmeticFunction
open ZMod
open LeanLab.ExceptionalSet.MV

noncomputable section

/-- LEAF 1 of 2, the counting half of the split: on the concrete data of the power saving
route, some `θ < 1` bounds the number of even `n` in the window `(x/2, x]` whose major arc
part has modulus at most `M x / 4`, the level that the major arc asymptotic clears. The
constant is one nonnegative `C` for all `x ≥ X0`, and `X0 ≥ 1` so that the window and the
level are nondegenerate. Only this count is asserted; no bound on the minor arcs. -/
theorem major_arc_count_power :
    ∃ (θ C : ℝ) (X0 : ℕ), 0 < θ ∧ θ < 1 ∧ 0 ≤ C ∧ 1 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        ((((Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ => Even n ∧
              ‖majorPart (logPrimes x) (minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10)))
                (n : ZMod (Mx x))‖ ≤ (Mx x : ℝ) * x / 4)).card : ℕ) : ℝ)
          ≤ C * (x : ℝ) ^ θ := by
  sorry

/-- Vaughan's Theorem 3.1 on the minor arcs at `Q = x^(1/10)`: a minor arc point has a rational
approximation with denominator in `(x^(1/10), M x / x^(1/10)]`, so the exponential sum over the
primes up to `x` is at most `C x^(19/20) (log x)^4`. -/
private theorem minor_sup_power :
    ∃ (C : ℝ) (X0 : ℕ), 0 ≤ C ∧ ∀ x : ℕ, X0 ≤ x →
      ∀ k ∈ minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10)),
        ‖𝓕 (logPrimes x) k‖ ≤ C * ((x : ℝ) ^ ((19 : ℝ) / 20) * Real.log x ^ 4) := by
  obtain ⟨C, X0, hC⟩ := vinogradovDFT_proved
  refine ⟨4 * |C|, max (max X0 3) 1, by positivity, ?_⟩
  intro x hx k hk
  have hxX0 : X0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3r : (3 : ℝ) ≤ x := by exact_mod_cast hx3
  have hxpos : (0 : ℝ) < x := by linarith
  have hx1r : (1 : ℝ) ≤ x := by linarith
  set L : ℝ := Real.log x with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg hx1r
  set Q : ℝ := (x : ℝ) ^ ((1 : ℝ) / 10) with hQdef
  have hQ1 : 1 ≤ Q := by rw [hQdef]; exact Real.one_le_rpow hx1r (by norm_num)
  have hQpos : 0 < Q := by linarith
  have hQx : Q ≤ x := by
    rw [hQdef]; exact Real.rpow_le_self_of_one_le hx1r (by norm_num)
  have hM : (Mx x : ℝ) = 2 * x + 1 := by unfold Mx; push_cast; ring
  have hMpos : (0 : ℝ) < Mx x := by rw [hM]; linarith
  have hMQ : 1 ≤ (Mx x : ℝ) / Q := by
    rw [le_div_iff₀ hQpos, hM]; linarith
  set n : ℕ := ⌊(Mx x : ℝ) / Q⌋₊ with hn
  have hn1 : 1 ≤ n := by rw [hn]; exact Nat.le_floor (by exact_mod_cast hMQ)
  have hnle : (n : ℝ) ≤ (Mx x : ℝ) / Q := by rw [hn]; exact Nat.floor_le (by positivity)
  have hnlt : (Mx x : ℝ) / Q < n + 1 := by rw [hn]; exact Nat.lt_floor_add_one _
  set ξ : ℝ := (ZMod.val k : ℝ) / (Mx x) with hξ
  obtain ⟨r, hr1, hr2⟩ := exists_rat_abs_sub_le_and_den_le ξ (n := n) (by omega)
  have hden1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
  have hdenn : (r.den : ℝ) ≤ n := by exact_mod_cast hr2
  -- the denominator exceeds Q, else `k` would lie on a major arc
  have hQden : Q < r.den := by
    by_contra hcon
    push Not at hcon
    apply (mem_compl.mp hk)
    have hle : |ξ - r| ≤ Q / (Mx x) := by
      calc |ξ - r| ≤ 1 / ((n + 1) * r.den) := hr1
        _ ≤ 1 / ((n : ℝ) + 1) := by
            apply one_div_le_one_div_of_le (by positivity)
            nlinarith
        _ ≤ Q / (Mx x) := by
            rw [div_le_div_iff₀ (by positivity) hMpos, one_mul]
            rw [div_lt_iff₀ hQpos] at hnlt
            linarith
    simp only [majorArcs, mem_filter, mem_univ, true_and]
    refine ⟨r.den, r.den_pos, hcon, r.num, ?_⟩
    have hrcast : ((r.num : ℝ) / (r.den : ℝ)) = (r : ℝ) := by rw [Rat.cast_def]
    rw [← hξ, hrcast]
    exact hle
  -- Theorem 3.1 applies
  have happ : |ξ - r| ≤ 1 / (r.den : ℝ) ^ 2 := by
    refine le_trans hr1 (one_div_le_one_div_of_le (by positivity) ?_)
    nlinarith
  have hS := hC x hxX0 k r happ
  have hdenMQ : (r.den : ℝ) ≤ (Mx x : ℝ) / Q := le_trans hdenn hnle
  -- `√Q = x^(1/20)`
  have hsqQ : √Q = (x : ℝ) ^ ((1 : ℝ) / 20) := by
    rw [Real.sqrt_eq_rpow, hQdef, ← Real.rpow_mul hxpos.le]
    norm_num
  have hsqQpos : 0 < √Q := Real.sqrt_pos.mpr hQpos
  -- the three terms of the bracket
  have t1 : (x : ℝ) / √(r.den : ℝ) ≤ (x : ℝ) ^ ((19 : ℝ) / 20) := by
    have hsd : √Q ≤ √(r.den : ℝ) := Real.sqrt_le_sqrt hQden.le
    calc (x : ℝ) / √(r.den : ℝ) ≤ (x : ℝ) / √Q :=
          div_le_div_of_nonneg_left hxpos.le hsqQpos hsd
      _ = (x : ℝ) ^ ((19 : ℝ) / 20) := by
          rw [hsqQ, show (19 : ℝ) / 20 = 1 - 1 / 20 by norm_num,
            Real.rpow_sub hxpos, Real.rpow_one]
  have t2 : (x : ℝ) ^ ((4 : ℝ) / 5) ≤ (x : ℝ) ^ ((19 : ℝ) / 20) :=
    Real.rpow_le_rpow_of_exponent_le hx1r (by norm_num)
  have t3 : √((x : ℝ) * r.den) ≤ 2 * (x : ℝ) ^ ((19 : ℝ) / 20) := by
    have hQe : (x : ℝ) ^ ((19 : ℝ) / 10) * Q = (x : ℝ) ^ 2 := by
      rw [hQdef, ← Real.rpow_add hxpos]
      norm_num
    have hxd : (x : ℝ) * r.den ≤ 3 * (x : ℝ) ^ ((19 : ℝ) / 10) := by
      have h1 : (x : ℝ) * r.den ≤ (x : ℝ) * ((Mx x : ℝ) / Q) :=
        mul_le_mul_of_nonneg_left hdenMQ hxpos.le
      have h2 : (x : ℝ) * ((Mx x : ℝ) / Q) ≤ 3 * (x : ℝ) ^ ((19 : ℝ) / 10) := by
        have h3 : (x : ℝ) * ((Mx x : ℝ) / Q) = (x : ℝ) * (Mx x : ℝ) / Q := by ring
        rw [h3, div_le_iff₀ hQpos]
        have hM3 : (Mx x : ℝ) ≤ 3 * x := by rw [hM]; linarith
        nlinarith [hQe, hM3, hxpos]
      linarith
    have hsq : ((x : ℝ) ^ ((19 : ℝ) / 20)) ^ 2 = (x : ℝ) ^ ((19 : ℝ) / 10) := by
      rw [← Real.rpow_natCast ((x : ℝ) ^ ((19 : ℝ) / 20)) 2, ← Real.rpow_mul hxpos.le]
      norm_num
    have hle : (x : ℝ) * r.den ≤ (2 * (x : ℝ) ^ ((19 : ℝ) / 20)) ^ 2 := by
      have h0 : (0 : ℝ) ≤ (x : ℝ) ^ ((19 : ℝ) / 10) := Real.rpow_nonneg hxpos.le _
      rw [mul_pow, hsq]
      nlinarith
    calc √((x : ℝ) * r.den) ≤ √((2 * (x : ℝ) ^ ((19 : ℝ) / 20)) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 2 * (x : ℝ) ^ ((19 : ℝ) / 20) := Real.sqrt_sq (by positivity)
  have hbr : (x : ℝ) / √(r.den : ℝ) + (x : ℝ) ^ ((4 : ℝ) / 5) + √((x : ℝ) * r.den)
      ≤ 4 * (x : ℝ) ^ ((19 : ℝ) / 20) := by linarith
  have hbr0 : 0 ≤ (x : ℝ) / √(r.den : ℝ) + (x : ℝ) ^ ((4 : ℝ) / 5) + √((x : ℝ) * r.den) := by
    positivity
  have hA0 : 0 ≤ (x : ℝ) ^ ((19 : ℝ) / 20) := Real.rpow_nonneg hxpos.le _
  calc ‖𝓕 (logPrimes x) k‖
      ≤ C * ((x : ℝ) / √(r.den : ℝ) + (x : ℝ) ^ ((4 : ℝ) / 5) + √((x : ℝ) * r.den)) * L ^ 4 := hS
    _ ≤ |C| * ((x : ℝ) / √(r.den : ℝ) + (x : ℝ) ^ ((4 : ℝ) / 5) + √((x : ℝ) * r.den)) * L ^ 4 := by
        gcongr
        exact le_abs_self C
    _ ≤ |C| * (4 * (x : ℝ) ^ ((19 : ℝ) / 20)) * L ^ 4 := by gcongr
    _ = (4 * |C|) * ((x : ℝ) ^ ((19 : ℝ) / 20) * L ^ 4) := by ring

/-- The exact algebraic identity at the heart of the fourth moment: `M · (U² · (M · S))`
divided by `T² = (M x / 4)²` is `16 U² S / x²`. -/
private theorem l4_arith {M x U S : ℝ} (hM : 0 < M) (hx : 0 < x) :
    M * (U ^ 2 * (M * S)) / (M * x / 4) ^ 2 = 16 * U ^ 2 * S / x ^ 2 := by
  have hMx : (0 : ℝ) < M * x := by positivity
  field_simp
  ring

/-- The last real-variable comparison: with `U = Cv (x^(19/20) (log x)^4)` and
`(log x)^10 ≤ x^(1/20)`, the fourth moment term is at most `48 Cv² x^(19/20)`. -/
private theorem l4_final {Cv x L : ℝ} (hCv0 : 0 ≤ Cv) (hx : 0 < x) (hx1 : 1 ≤ x) (hL0 : 0 ≤ L)
    (hlog : L ^ 10 ≤ x ^ ((1 : ℝ) / 20)) :
    48 * (Cv * (x ^ ((19 : ℝ) / 20) * L ^ 4)) ^ 2 * L ^ 2 / x
      ≤ 48 * Cv ^ 2 * x ^ ((19 : ℝ) / 20) := by
  set A : ℝ := x ^ ((19 : ℝ) / 20) with hAdef
  have hA0 : 0 ≤ A := Real.rpow_nonneg hx.le _
  have hA2 : A ^ 2 = x ^ ((19 : ℝ) / 10) := by
    rw [hAdef, ← Real.rpow_natCast (x ^ ((19 : ℝ) / 20)) 2, ← Real.rpow_mul hx.le]
    norm_num
  have e1 : 48 * (Cv * (A * L ^ 4)) ^ 2 * L ^ 2 / x = 48 * Cv ^ 2 * (A ^ 2 * L ^ 10) / x := by
    field_simp
  have e2 : (A ^ 2 * L ^ 10) / x = x ^ ((9 : ℝ) / 10) * L ^ 10 := by
    rw [hA2, show (19 : ℝ) / 10 = 9 / 10 + 1 by norm_num, Real.rpow_add hx, Real.rpow_one]
    field_simp
  have e3 : 48 * Cv ^ 2 * (x ^ ((9 : ℝ) / 10) * L ^ 10)
      ≤ 48 * Cv ^ 2 * x ^ ((19 : ℝ) / 20) := by
    have hx9 : 0 ≤ x ^ ((9 : ℝ) / 10) := Real.rpow_nonneg hx.le _
    have h20 : x ^ ((9 : ℝ) / 10) * L ^ 10 ≤ x ^ ((9 : ℝ) / 10) * x ^ ((1 : ℝ) / 20) :=
      mul_le_mul_of_nonneg_left hlog hx9
    have e4 : x ^ ((9 : ℝ) / 10) * x ^ ((1 : ℝ) / 20) = x ^ ((19 : ℝ) / 20) := by
      rw [show (19 : ℝ) / 20 = 9 / 10 + 1 / 20 by norm_num, Real.rpow_add hx]
    calc 48 * Cv ^ 2 * (x ^ ((9 : ℝ) / 10) * L ^ 10)
        ≤ 48 * Cv ^ 2 * (x ^ ((9 : ℝ) / 10) * x ^ ((1 : ℝ) / 20)) := by
          apply mul_le_mul_of_nonneg_left h20 (by positivity)
      _ = 48 * Cv ^ 2 * x ^ ((19 : ℝ) / 20) := by rw [e4]
  calc 48 * (Cv * (A * L ^ 4)) ^ 2 * L ^ 2 / x
      = 48 * Cv ^ 2 * (A ^ 2 * L ^ 10) / x := e1
    _ = 48 * Cv ^ 2 * ((A ^ 2 * L ^ 10) / x) := by ring
    _ = 48 * Cv ^ 2 * (x ^ ((9 : ℝ) / 10) * L ^ 10) := by rw [e2]
    _ ≤ 48 * Cv ^ 2 * x ^ ((19 : ℝ) / 20) := e3

/-- LEAF 2 of 2, the mean value half of the split: on the same data, `M` times the fourth
moment `∑ ‖𝓕 Φ k‖⁴` over the minor arcs, divided by `T² = (M x / 4)²`, is at most `C x^θ` with
`θ < 1`. The moment is the quantity `card_large_minor_le` converts into a count of bad `n`, so
this half and LEAF 1 together cover the window. Only this moment is asserted; no count of
exceptional `n`. -/
theorem minor_arc_l4_power :
    ∃ (θ C : ℝ) (X0 : ℕ), 0 < θ ∧ θ < 1 ∧ 0 ≤ C ∧ 1 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        (Mx x : ℝ) * (∑ k ∈ minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10)), ‖𝓕 (logPrimes x) k‖ ^ 4)
            / ((Mx x : ℝ) * x / 4) ^ 2 ≤ C * (x : ℝ) ^ θ := by
  obtain ⟨Cv, Xv, hCv0, hsup⟩ := minor_sup_power
  obtain ⟨Xl, hl⟩ := log_rpow_le_rpow_nat (10 : ℝ) (s := 1 / 20) (by norm_num)
  refine ⟨19 / 20, 48 * Cv ^ 2, max (max Xv Xl) 3, by norm_num, by norm_num, by positivity,
    le_trans (by norm_num : (1 : ℕ) ≤ 3) (le_max_right _ _), ?_⟩
  intro x hx
  have hxXv : Xv ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxXl : Xl ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hx3r : (3 : ℝ) ≤ x := by exact_mod_cast hx3
  have hxpos : (0 : ℝ) < x := by linarith
  have hx1r : (1 : ℝ) ≤ x := by linarith
  set L : ℝ := Real.log x with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg hx1r
  have hlog : L ^ 10 ≤ x ^ ((1 : ℝ) / 20) := by
    rw [hLdef, ← Real.rpow_natCast (Real.log x) 10]; exact hl x hxXl
  set Q : ℝ := (x : ℝ) ^ ((1 : ℝ) / 10) with hQdef
  set U : ℝ := Cv * (x ^ ((19 : ℝ) / 20) * L ^ 4) with hUdef
  have hU0 : 0 ≤ U := by
    rw [hUdef]; have := Real.rpow_nonneg hxpos.le ((19 : ℝ) / 20); positivity
  have hM0 : (0 : ℝ) < (Mx x : ℝ) := by
    have : 0 < Mx x := by unfold Mx; omega
    exact_mod_cast this
  have hM3 : (Mx x : ℝ) ≤ 3 * (x : ℝ) := by
    have e : (Mx x : ℝ) = 2 * (x : ℝ) + 1 := by unfold Mx; push_cast; ring
    rw [e]; linarith
  have hsup' : ∀ k ∈ minorArcs x Q, ‖𝓕 (logPrimes x) k‖ ≤ U := by
    intro k hk
    rw [hUdef]
    exact hsup x hxXv k hk
  have hL4 := minor_L4_le_sup (Φ := logPrimes x) (m := minorArcs x Q) (U := U) hsup'
  have hS2 : ∑ j, ‖logPrimes x j‖ ^ 2 ≤ (Mx x : ℝ) * L ^ 2 := by
    rw [hLdef]; exact sum_sq_logPrimes_le x
  have hstep1 : (Mx x : ℝ) * (∑ k ∈ minorArcs x Q, ‖𝓕 (logPrimes x) k‖ ^ 4)
      ≤ (Mx x : ℝ) * (U ^ 2 * ((Mx x : ℝ) * ((Mx x : ℝ) * L ^ 2))) := by
    apply mul_le_mul_of_nonneg_left _ hM0.le
    refine hL4.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ U ^ 2)
    exact mul_le_mul_of_nonneg_left hS2 hM0.le
  have hstep2 : (Mx x : ℝ) * (∑ k ∈ minorArcs x Q, ‖𝓕 (logPrimes x) k‖ ^ 4)
        / ((Mx x : ℝ) * x / 4) ^ 2
      ≤ (Mx x : ℝ) * (U ^ 2 * ((Mx x : ℝ) * ((Mx x : ℝ) * L ^ 2)))
        / ((Mx x : ℝ) * x / 4) ^ 2 := by
    gcongr
  have hT2 : (0 : ℝ) < ((Mx x : ℝ) * x / 4) ^ 2 := by positivity
  have hstep3 : (Mx x : ℝ) * (U ^ 2 * ((Mx x : ℝ) * ((Mx x : ℝ) * L ^ 2)))
        / ((Mx x : ℝ) * x / 4) ^ 2 = 16 * U ^ 2 * ((Mx x : ℝ) * L ^ 2) / x ^ 2 :=
    l4_arith hM0 hxpos
  have hstep4 : 16 * U ^ 2 * ((Mx x : ℝ) * L ^ 2) / x ^ 2 ≤ 48 * U ^ 2 * L ^ 2 / x := by
    rw [div_le_div_iff₀ (by positivity) hxpos]
    have hcoef : (0 : ℝ) ≤ 16 * U ^ 2 * L ^ 2 * x := by positivity
    calc 16 * U ^ 2 * ((Mx x : ℝ) * L ^ 2) * x
        = (16 * U ^ 2 * L ^ 2 * x) * (Mx x : ℝ) := by ring
      _ ≤ (16 * U ^ 2 * L ^ 2 * x) * (3 * x) := mul_le_mul_of_nonneg_left hM3 hcoef
      _ = 48 * U ^ 2 * L ^ 2 * x ^ 2 := by ring
  have hstep5 : 48 * U ^ 2 * L ^ 2 / x ≤ 48 * Cv ^ 2 * (x : ℝ) ^ ((19 : ℝ) / 20) := by
    rw [hUdef]
    exact l4_final hCv0 hxpos hx1r hL0 hlog
  linarith


/-- `theorem51` of `LeanLab.ExceptionalSet.BhowmikGrimmelt2026`, assembled from the two leaves
at the level `Q = x^{1/10}`: the window bound at the larger of the two exponents, then the
dyadic summation to `E`. -/
theorem theorem51_split : PowerSaving := by
  obtain ⟨θ₁, C₁, X₁, hθ₁0, hθ₁1, hC₁, hX₁, h1⟩ := major_arc_count_power
  obtain ⟨θ₂, C₂, X₂, hθ₂0, hθ₂1, hC₂, hX₂, h2⟩ := minor_arc_l4_power
  have hθ0 : 0 < max θ₁ θ₂ := lt_of_lt_of_le hθ₁0 (le_max_left _ _)
  have hθ1 : max θ₁ θ₂ < 1 := max_lt hθ₁1 hθ₂1
  refine ⟨1 - max θ₁ θ₂, by linarith, ?_⟩
  rw [sub_sub_cancel]
  refine powerBound_of_window (θ := max θ₁ θ₂) (C := C₁ + C₂) (X0 := max X₁ X₂) hθ0 ?_
  intro x hx
  have hb1 := h1 x (le_trans (le_max_left _ _) hx)
  have hb2 := h2 x (le_trans (le_max_right _ _) hx)
  have hx1 : 1 ≤ x := le_trans (le_trans hX₁ (le_max_left _ _)) hx
  have hxM : 2 * x < Mx x := by unfold Mx; omega
  have hMpos : (0 : ℝ) < (Mx x : ℝ) := by
    have : 0 < Mx x := by unfold Mx; omega
    exact_mod_cast this
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
  have hT : (0 : ℝ) < (Mx x : ℝ) * x / 4 := by
    have := mul_pos hMpos hxpos
    linarith
  have hΦ : PrimeSupported (logPrimes x) x := by
    intro j hj
    by_contra hcon
    exact hj (by simp [logPrimes, hcon])
  have hsk := bad_le_skeleton (M := Mx x) (Φ := logPrimes x) (x := x) (a := x / 2 + 1) hΦ hxM
    (minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10))) hT
  have hsum : (badWindow x : ℝ) ≤ C₁ * (x : ℝ) ^ θ₁ + C₂ * (x : ℝ) ^ θ₂ := by
    unfold badWindow
    linarith
  have hx1r : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hp1 : (x : ℝ) ^ θ₁ ≤ (x : ℝ) ^ max θ₁ θ₂ :=
    Real.rpow_le_rpow_of_exponent_le hx1r (le_max_left _ _)
  have hp2 : (x : ℝ) ^ θ₂ ≤ (x : ℝ) ^ max θ₁ θ₂ :=
    Real.rpow_le_rpow_of_exponent_le hx1r (le_max_right _ _)
  have hm1 : C₁ * (x : ℝ) ^ θ₁ ≤ C₁ * (x : ℝ) ^ max θ₁ θ₂ :=
    mul_le_mul_of_nonneg_left hp1 hC₁
  have hm2 : C₂ * (x : ℝ) ^ θ₂ ≤ C₂ * (x : ℝ) ^ max θ₁ θ₂ :=
    mul_le_mul_of_nonneg_left hp2 hC₂
  have hfin : C₁ * (x : ℝ) ^ max θ₁ θ₂ + C₂ * (x : ℝ) ^ max θ₁ θ₂
      = (C₁ + C₂) * (x : ℝ) ^ max θ₁ θ₂ := by ring
  linarith

-- Axiom audit driver for the assembly.
#print axioms theorem51_split

end

end LeanLab.ExceptionalSet.BG2026
