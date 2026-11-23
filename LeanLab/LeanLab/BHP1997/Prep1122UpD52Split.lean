/-
P0069 Baker Harman Pintz 1997, page 49, the proof of Lemma 34, cut for its conclusion 5.2.
Burst burst-20261122, unit P1122-0086, route step `upD_lemma34_52`.

Wiring note. The declaration `upD_lemma34_52` was written on branch
claude/BHP1997-upper_normalized_raw_conditions_slack-p2, file Prep1121DUpslackPieces, which is
not on main; the file of that name on main holds only the repaired `upD_j_rep`. So this file
does not touch it. The theorem `upD52_lemma34_52` below has the exact statement of
`upD_lemma34_52`, so that leaf closes by `exact upD52_lemma34_52 h4 h9 hε hε8 a b ha hrep`
once both are on main.

The page 49 proof, read from the page image. By Buchstab's identity
  b_m = sum_{nl = k, n <= Y^(1/2 + theta2/4 - 2 eps)} a_n psi(l, w)
      - sum_{n p1 n1 = k, w <= p1 < Y^c1, n <= Y^(1/2 + theta2/4 - 2 eps)} a_n psi(n1, p1)
      = f_m - g_m,
with w = exp(log^(9/10) x) from page 25. Then f satisfies 5.1 and 5.2 by Lemma 30; the part of
g with p1 >= Y^eps satisfies them by Lemma 5 and Lemma 33; the part with w <= p1 < Y^eps by the
iterated decomposition of Lemma 13 case ii, which ends after O(L^(1/10)) steps.

Here: the Buchstab split is PROVED for x past an explicit point, from
`upper_rough_buchstab_step` on main; the passage from 5.2 for the three pieces to 5.2 for b is
PROVED by |u - v - w|^2 <= 3(|u|^2 + |v|^2 + |w|^2) on each of the two t ranges; the three
piece bounds are LEAFs. No new definition, no existing statement changed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165dBase312
import LeanLab.BHP1997.Prep1122KeptLemma33Pieces52

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- LEAF: P0069 page 49, proof of Lemma 34, first line: "Here f_m satisfies 5.1 and 5.2 by
Lemma 30", the conclusion 5.2 of page 43 for the principal character. `c` is
f_m = sum over nl = k, n <= Y^(1/2 + theta2/4 - 2 eps), of a_n psi(l, w), with
w = exp(log^(9/10) x) of page 25 and `(a_n)` satisfying 3.1. Lemma 30 on page 44 applies since
n is at most Y^(1/2 + theta2/4 - 2 eps), inside the range 5.5. CONDITIONAL on the cited
Theorem 4 and Lemma 9, used in the proof of Lemma 30 through 3.3 and Lemma 9. Class HARD. -/
theorem upD52_leaf_f_lemma30 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℝ)
    (hc : ∀ x k, c x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * upperRough (k / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ)))) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  sorry

/-- Reduction for the g-big leaf: if the one-prime coefficient c of the big part of g_m
satisfies the well-spaced block bound in the shape of `kept52_wellspaced`, then display 5.2 on
page 43 holds for it. PROVED by the same unit-block and consecutive-block summation as
`kept52_of_leaves`; the well-spaced bound is the only analytic content left. No new definition,
no existing statement changed. AI wrote the Lean code. Goldbach is open. -/
theorem upD52_gbig_of_wellspaced {ε : ℝ} (c : ℝ → ℕ → ℝ)
    (hws : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ a b : ℝ, a ≤ b → b - a ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ((Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ a ∧ b ≤ x ^ (11 / 20 + ε)) ∨
        (-x ^ (11 / 20 + ε) ≤ a ∧ b ≤ -Real.exp (Real.log x ^ (1 / 3 : ℝ)))) →
      ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
        ∑ t ∈ S, ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
            (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C, hC⟩ := hws A hA
  refine ⟨max (12 * max C 0) (max C 1), fun x hx q hq1 hqQ => ?_⟩
  have hxC : C ≤ x := (le_max_left C 1).trans (hx.trans' (le_max_right _ _))
  have hx1 : 1 ≤ x := (le_max_right C 1).trans (hx.trans' (le_max_right _ _))
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  set Y := x ^ (11 / 20 + ε) with hYdef
  set T0 := Real.exp (Real.log x ^ (1 / 3 : ℝ)) with hT0def
  set T2 := x ^ (11 / 20 + ε) / (q * sieveQ ε x) with hT2def
  set Lg := Real.log x ^ (-A) with hLg
  set F : ℝ → ℝ := fun t => ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
      (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
    with hFdef
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hx0 _
  have hL0 : 0 ≤ Lg := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hQ1 : (1 : ℝ) ≤ (sieveQ ε x : ℝ) := by exact_mod_cast hq1.trans hqQ
  have hq1' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hT2 : 0 < T2 := by rw [hT2def]; positivity
  have hT0 : 0 ≤ T0 := (Real.exp_pos _).le
  have hFc : Continuous F := kept52_continuous ε x q (c x)
  have hF0 : ∀ t, 0 ≤ F t := fun t => sq_nonneg _
  set M := max C 0 with hM
  have hV : 0 ≤ 2 * (M * Y * Lg) := by positivity
  have hblock : ∀ a b : ℝ, a ≤ b → b - a ≤ T2 →
      ((T0 ≤ a ∧ b ≤ Y) ∨ (-Y ≤ a ∧ b ≤ -T0)) → ∫ t in a..b, F t ≤ 2 * (M * Y * Lg) := by
    intro a b hab hba hrange
    have h1 := kept52_block_le_two_wellspaced F hFc hF0 hab
      (hC x hxC q hq1 hqQ a b hab hba hrange)
    have h2 : C * Y * Lg ≤ M * Y * Lg :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hY0.le) hL0
    linarith
  have hpos : ∫ t in T0..Y, F t / (T2 ^ 2 + t ^ 2) ≤ 3 * (2 * (M * Y * Lg)) / T2 ^ 2 :=
    kept52_block_sum F hFc hF0 hT0 hT2 hV fun a b ha hab hb hba =>
      hblock a b hab hba (Or.inl ⟨ha, hb⟩)
  have hneg : ∫ t in -Y..-T0, F t / (T2 ^ 2 + t ^ 2) ≤ 3 * (2 * (M * Y * Lg)) / T2 ^ 2 := by
    have hc := intervalIntegral.integral_comp_neg (a := T0) (b := Y)
      (fun t => F t / (T2 ^ 2 + t ^ 2))
    simp only [neg_sq] at hc
    rw [← hc]
    refine kept52_block_sum (fun t => F (-t)) (hFc.comp continuous_neg) (fun t => hF0 _)
      hT0 hT2 hV fun a b ha hab hb hba => ?_
    have hc2 := intervalIntegral.integral_comp_neg (a := a) (b := b) F
    rw [hc2]
    exact hblock (-b) (-a) (by linarith) (by linarith) (Or.inr ⟨by linarith, by linarith⟩)
  have hmain : 3 * (2 * (M * Y * Lg)) / T2 ^ 2 + 3 * (2 * (M * Y * Lg)) / T2 ^ 2 =
      12 * M * (Y / T2 ^ 2) * Lg := by ring
  have hfin : 12 * M * (Y / T2 ^ 2) * Lg ≤ max (12 * M) (max C 1) * (Y / T2 ^ 2) * Lg :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hL0
  calc _ ≤ 3 * (2 * (M * Y * Lg)) / T2 ^ 2 + 3 * (2 * (M * Y * Lg)) / T2 ^ 2 :=
        add_le_add hneg hpos
    _ = 12 * M * (Y / T2 ^ 2) * Lg := hmain
    _ ≤ _ := hfin

/-- LEAF: P0069 pages 49 and 50, proof of Lemma 34, the part of g_m with p1 >= Y^eps: "of
course if P >= Y^eps we may obtain 5.1 and 5.2 from Lemma 33", with N(s, chi) the sum of
chi(p1) p1^(-s) over p1 ~ P satisfying 3.2 by Lemma 5. Conclusion 5.2 of page 43 for the
principal character. `c` is the sum over n p1 n1 = k, n <= Y^(1/2 + theta2/4 - 2 eps), with
w <= p1 < Y^c1 and Y^eps <= p1, of a_n psi(n1, p1), where n1 = (k / n) / p1. The page cuts
p1 into dyadic blocks p1 ~ P; here the cut at Y^eps is sharp, which changes only the one
block that meets Y^eps and keeps p1 a prime from an interval. CONDITIONAL on the cited
Theorem 4, through Lemma 33, and Lemma 9. Class HARD. -/
theorem upD52_leaf_g_big_lemma33 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℝ)
    (hc : ∀ x k, c x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          upperRough (k / n / p) (p : ℝ)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  refine upD52_gbig_of_wellspaced c ?_
  intro A hA
  -- Attempt 2026-11-22: the only well-spaced block bound in the lab is kept52_wellspaced,
  -- whose polynomial carries the upperKept coefficients, not the one-prime coefficient c of
  -- the big part of g_m. The attempt `exact kept52_wellspaced h4 h9 hε hε8 A hA` fails with
  -- a type mismatch, upperKept ε (x ^ (11 / 20 + ε)) m against c x m; see PROGRESS.md,
  -- BLOCKED 2026-11-22. The missing input is the page 48 Lemma 33 well-spaced block bound
  -- for the one-prime coefficient, case 5.13, whose paper proof needs the Lemma 5 bound 3.2
  -- for the prime polynomial, which the lab does not formalize either.
  sorry

/-- LEAF: P0069 page 50, proof of Lemma 34, the part of g_m with w <= p1 < Y^eps: "For
w <= P <= Y^eps, we iterate the decomposition in the same fashion as case ii of Lemma 13",
where after j steps n p1 ... pj <= Y^(1/2 + theta2/4 - eps), so a further decomposition is
possible, and the process ends after O(L^(1/10)) steps. Conclusion 5.2 of page 43 for the
principal character. `c` is the sum over n p1 n1 = k, n <= Y^(1/2 + theta2/4 - 2 eps), with
w <= p1 < Y^c1 and p1 < Y^eps, of a_n psi(n1, p1), where n1 = (k / n) / p1. CONDITIONAL on the
cited Theorem 4 and Lemma 9. Class HARD. -/
theorem upD52_leaf_g_small_iterate (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℝ)
    (hc : ∀ x k, c x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          upperRough (k / n / p) (p : ℝ)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  sorry

/-- P0069 pages 25 and 49: for x past exp(16^10), Y = x^(11/20 + eps) is at least 2, the
range of the Lemma 34 form, and w = exp(log^(9/10) x) is at most Y^c1, which Buchstab's
identity in the proof of Lemma 34 needs. PROVED. -/
theorem upD52_eventually {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ X0 : ℝ, 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      2 ≤ x ^ (11 / 20 + ε) ∧
      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (x ^ (11 / 20 + ε)) ^ upperC1 ε := by
  refine ⟨Real.exp (16 ^ 10), ?_, ?_⟩
  · have := Real.add_one_le_exp ((16 : ℝ) ^ 10)
    have h0 : (0 : ℝ) ≤ 16 ^ 10 := by positivity
    linarith
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : (16 : ℝ) ^ 10 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at this
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (by positivity) hL
  have hY : x ^ (11 / 20 + ε) = Real.exp (Real.log x * (11 / 20 + ε)) :=
    Real.rpow_def_of_pos hx0 _
  constructor
  · rw [hY]
    have h1 := Real.add_one_le_exp (Real.log x * (11 / 20 + ε))
    have h2 : (1 : ℝ) ≤ Real.log x * (11 / 20 + ε) := by nlinarith
    linarith
  · rw [Real.rpow_def_of_pos (Real.rpow_pos_of_pos hx0 _), Real.log_rpow hx0]
    apply Real.exp_le_exp.mpr
    have h16 : ((16 : ℝ) ^ (10 : ℝ)) ^ ((1 : ℝ) / 10) = 16 := by
      rw [← Real.rpow_mul (by norm_num)]; norm_num
    have h1610 : (16 : ℝ) ^ (10 : ℝ) = 16 ^ 10 := by
      rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hQ : (16 : ℝ) ≤ Real.log x ^ ((1 : ℝ) / 10) := by
      rw [← h16, h1610]
      exact Real.rpow_le_rpow (by positivity) hL (by norm_num)
    have hsplit : Real.log x ^ (9 / 10 : ℝ) * Real.log x ^ ((1 : ℝ) / 10) = Real.log x := by
      rw [← Real.rpow_add hLpos]; norm_num
    have hP : 0 ≤ Real.log x ^ (9 / 10 : ℝ) := Real.rpow_nonneg hLpos.le _
    have hc1 : (12 : ℝ) / 100 ≤ upperC1 ε := by
      unfold upperC1; norm_num; linarith
    have hec : (11 / 20 : ℝ) * (12 / 100) ≤ (11 / 20 + ε) * upperC1 ε := by nlinarith
    have hP16 : 16 * Real.log x ^ (9 / 10 : ℝ) ≤ Real.log x := by nlinarith
    nlinarith

/-- P0069 page 49, Buchstab's identity in the proof of Lemma 34, split at p1 = Y^eps: on J,
for Y at least 2 and w = exp(log^(9/10) x) at most Y^c1, the Lemma 34 sum b_m equals f_m
minus the part of g_m with p1 >= Y^eps minus the part with p1 < Y^eps. PROVED from
`upper_rough_buchstab_step`. -/
theorem upD52_buchstab_split {ε : ℝ} (a b : ℝ → ℕ → ℝ)
    (hrep : ∀ x : ℝ, 2 ≤ x ^ (11 / 20 + ε) → ∀ k ∈ rightInterval ε x,
      b x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * upperRough (k / n) ((x ^ (11 / 20 + ε)) ^ upperC1 ε))
    (x : ℝ) (hY : 2 ≤ x ^ (11 / 20 + ε))
    (hw : Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (x ^ (11 / 20 + ε)) ^ upperC1 ε)
    (k : ℕ) (hk : k ∈ rightInterval ε x) :
    b x k =
      (∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * upperRough (k / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ)))) -
      (∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          upperRough (k / n / p) (p : ℝ)) -
      (∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          upperRough (k / n / p) (p : ℝ)) := by
  rw [hrep x hY k hk, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [upper_rough_buchstab_step (k / n) hw,
    ← Finset.sum_filter_add_sum_filter_not ((k / n).primeFactors.filter (fun p : ℕ =>
      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
        (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε))
      (fun p : ℕ => (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ))]
  simp only [Finset.filter_filter]
  ring

/-- The window integrand of 5.2 is interval integrable on any range that avoids t = 0. -/
theorem upD52_intble (S : Finset ℕ) (hS : ∀ m ∈ S, m ≠ 0) (χ : ℕ → ℂ) (c : ℕ → ℝ)
    (T a d : ℝ) (h0 : ∀ t ∈ Set.uIcc a d, t ≠ 0) :
    IntervalIntegrable (fun t : ℝ =>
      ‖∑ m ∈ S, (c m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        (T ^ 2 + t ^ 2)) MeasureTheory.volume a d := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · apply Continuous.continuousOn
    refine Continuous.pow (Continuous.norm (continuous_finsetSum _ (fun m hm => ?_))) 2
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hS m hm
    refine Continuous.div continuous_const (Continuous.const_cpow (by fun_prop) (Or.inl hm0))
      (fun t => ?_)
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => hm0 h.1
  · exact (by fun_prop : Continuous fun t : ℝ => T ^ 2 + t ^ 2).continuousOn
  · intro t ht
    have := h0 t ht
    positivity

/-- One t range of 5.2: if b = f - g1 - g2 on S, then the window integral of b is at most
three times the sum of those of f, g1 and g2, by |u - v - w|^2 <= 3(|u|^2 + |v|^2 + |w|^2).
PROVED. -/
theorem upD52_interval (S : Finset ℕ) (hS : ∀ m ∈ S, m ≠ 0) (χ : ℕ → ℂ)
    (b f g1 g2 : ℕ → ℝ) (hb : ∀ m ∈ S, b m = f m - g1 m - g2 m) (T a d : ℝ) (had : a ≤ d)
    (h0 : ∀ t ∈ Set.uIcc a d, t ≠ 0) :
    (∫ t in a..d, ‖∑ m ∈ S, (b m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        (T ^ 2 + t ^ 2)) ≤
      3 * (∫ t in a..d, ‖∑ m ∈ S, (f m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        (T ^ 2 + t ^ 2)) +
      3 * (∫ t in a..d, ‖∑ m ∈ S, (g1 m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        (T ^ 2 + t ^ 2)) +
      3 * (∫ t in a..d, ‖∑ m ∈ S, (g2 m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        (T ^ 2 + t ^ 2)) := by
  have If := upD52_intble S hS χ f T a d h0
  have I1 := upD52_intble S hS χ g1 T a d h0
  have I2 := upD52_intble S hS χ g2 T a d h0
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (If.const_mul 3) (I1.const_mul 3),
    ← intervalIntegral.integral_add ((If.const_mul 3).add (I1.const_mul 3)) (I2.const_mul 3)]
  refine intervalIntegral.integral_mono_on had (upD52_intble S hS χ b T a d h0)
    (((If.const_mul 3).add (I1.const_mul 3)).add (I2.const_mul 3)) (fun t _ => ?_)
  have hsum : (∑ m ∈ S, (b m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) =
      (∑ m ∈ S, (f m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) -
      (∑ m ∈ S, (g1 m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) -
      (∑ m ∈ S, (g2 m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [hb m hm]
    push_cast
    ring
  rw [hsum]
  set u := ∑ m ∈ S, (f m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)
  set v := ∑ m ∈ S, (g1 m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)
  set w := ∑ m ∈ S, (g2 m : ℂ) * χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)
  have htri : ‖u - v - w‖ ≤ ‖u‖ + ‖v‖ + ‖w‖ := by
    calc ‖u - v - w‖ ≤ ‖u - v‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ ‖u‖ + ‖v‖ + ‖w‖ := by linarith [norm_sub_le u v]
  have hsq : ‖u - v - w‖ ^ 2 ≤ 3 * (‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2) := by
    have h0' : 0 ≤ ‖u - v - w‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖u‖ - ‖v‖), sq_nonneg (‖v‖ - ‖w‖), sq_nonneg (‖u‖ - ‖w‖),
      norm_nonneg u, norm_nonneg v, norm_nonneg w]
  have hd : 0 ≤ T ^ 2 + t ^ 2 := by positivity
  calc ‖u - v - w‖ ^ 2 / (T ^ 2 + t ^ 2)
      ≤ 3 * (‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2) / (T ^ 2 + t ^ 2) := by gcongr
    _ = 3 * (‖u‖ ^ 2 / (T ^ 2 + t ^ 2)) + 3 * (‖v‖ ^ 2 / (T ^ 2 + t ^ 2)) +
        3 * (‖w‖ ^ 2 / (T ^ 2 + t ^ 2)) := by ring

/-- A window integral of 5.2 taken with reversed limits is at most 0. PROVED. -/
theorem upD52_reversed (F : ℝ → ℝ) (hF : ∀ t, 0 ≤ F t) (a d : ℝ) (hda : d ≤ a) :
    (∫ t in a..d, F t) ≤ 0 := by
  rw [intervalIntegral.integral_symm]
  have := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hda (fun t _ => hF t)
  linarith

/-- P0069 page 49, Lemma 34, the conclusion 5.2 of page 43 for the principal character, with
the exact statement of `upD_lemma34_52`. PROVED from the three LEAFs above, one per term of
Buchstab's identity on page 49, with the split `upD52_buchstab_split` and the triangle
inequality `upD52_interval`. CONDITIONAL on the cited Theorem 4 and Lemma 9. -/
theorem upD52_lemma34_52 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a b : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (hrep : ∀ x : ℝ, 2 ≤ x ^ (11 / 20 + ε) → ∀ k ∈ rightInterval ε x,
      b x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * upperRough (k / n) ((x ^ (11 / 20 + ε)) ^ upperC1 ε)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  obtain ⟨fF, hfF⟩ : ∃ fF : ℝ → ℕ → ℝ, ∀ x k, fF x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * upperRough (k / n) (Real.exp (Real.log x ^ (9 / 10 : ℝ))) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨g1F, hg1F⟩ : ∃ g1F : ℝ → ℕ → ℝ, ∀ x k, g1F x k = ∑ n ∈ k.divisors.filter
        (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          upperRough (k / n / p) (p : ℝ) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨g2F, hg2F⟩ : ∃ g2F : ℝ → ℕ → ℝ, ∀ x k, g2F x k = ∑ n ∈ k.divisors.filter
        (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          upperRough (k / n / p) (p : ℝ) :=
    ⟨_, fun _ _ => rfl⟩
  intro A hA
  obtain ⟨Cf, hCf⟩ := upD52_leaf_f_lemma30 h4 h9 hε hε8 a ha fF hfF A hA
  obtain ⟨C1, hC1⟩ := upD52_leaf_g_big_lemma33 h4 h9 hε hε8 a ha g1F hg1F A hA
  obtain ⟨C2, hC2⟩ := upD52_leaf_g_small_iterate h4 h9 hε hε8 a ha g2F hg2F A hA
  obtain ⟨X0, hX01, hX0⟩ := upD52_eventually hε hε8
  refine ⟨max (max X0 (max Cf (max C1 C2))) (3 * (|Cf| + |C1| + |C2|)), ?_⟩
  intro x hx q hq1 hqQ
  have hX0x : X0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hCx : max X0 (max Cf (max C1 C2)) ≤ x := le_trans (le_max_left _ _) hx
  have hfx : Cf ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCx
  have h1x : C1 ≤ x := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hCx
  have h2x : C2 ≤ x := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hCx
  have hx1 : 1 ≤ x := le_trans hX01 hX0x
  obtain ⟨hY2, hw⟩ := hX0 x hX0x
  have hb : ∀ m ∈ rightInterval ε x, b x m = fF x m - g1F x m - g2F x m := by
    intro m hm
    rw [hfF, hg1F, hg2F]
    exact upD52_buchstab_split a b hrep x hY2 hw m hm
  have hS : ∀ m ∈ rightInterval ε x, m ≠ 0 := by
    intro m hm
    unfold rightInterval at hm
    rw [Finset.mem_Ioc] at hm
    omega
  set R := x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 with hRdef
  have hR : 0 ≤ R := by
    have : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
    positivity
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hRL : 0 ≤ R * Real.log x ^ (-A) := mul_nonneg hR hL
  have hCbig : 3 * (|Cf| + |C1| + |C2|) ≤
      max (max X0 (max Cf (max C1 C2))) (3 * (|Cf| + |C1| + |C2|)) := le_max_right _ _
  set Cbig := max (max X0 (max Cf (max C1 C2))) (3 * (|Cf| + |C1| + |C2|)) with hCbigdef
  have hfin : (3 * (|Cf| + |C1| + |C2|)) * (R * Real.log x ^ (-A)) ≤
      Cbig * (R * Real.log x ^ (-A)) := mul_le_mul_of_nonneg_right hCbig hRL
  have habs : 0 ≤ 3 * (|Cf| + |C1| + |C2|) := by positivity
  set χ : ℕ → ℂ := fun m => (1 : DirichletCharacter ℂ q) (m : ZMod q) with hχ
  set T := x ^ (11 / 20 + ε) / (q * sieveQ ε x) with hT
  set Y := x ^ (11 / 20 + ε) with hYdef
  set e := Real.exp (Real.log x ^ (1 / 3 : ℝ)) with hedef
  have he : 0 < e := Real.exp_pos _
  by_cases heY : e ≤ Y
  · have hneg : -Y ≤ -e := by linarith
    have h0n : ∀ t ∈ Set.uIcc (-Y) (-e), t ≠ 0 := by
      intro t ht
      rw [Set.uIcc_of_le hneg] at ht
      have := ht.2
      intro h; rw [h] at this; linarith
    have h0p : ∀ t ∈ Set.uIcc e Y, t ≠ 0 := by
      intro t ht
      rw [Set.uIcc_of_le heY] at ht
      have := ht.1
      intro h; rw [h] at this; linarith
    have Jn := upD52_interval (rightInterval ε x) hS χ (b x) (fF x) (g1F x) (g2F x) hb T
      (-Y) (-e) hneg h0n
    have Jp := upD52_interval (rightInterval ε x) hS χ (b x) (fF x) (g1F x) (g2F x) hb T
      e Y heY h0p
    have Kf := hCf x hfx q hq1 hqQ
    have K1 := hC1 x h1x q hq1 hqQ
    have K2 := hC2 x h2x q hq1 hqQ
    have Kf' : Cf * R * Real.log x ^ (-A) ≤ |Cf| * (R * Real.log x ^ (-A)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hRL
    have K1' : C1 * R * Real.log x ^ (-A) ≤ |C1| * (R * Real.log x ^ (-A)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hRL
    have K2' : C2 * R * Real.log x ^ (-A) ≤ |C2| * (R * Real.log x ^ (-A)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hRL
    rw [mul_assoc]
    nlinarith
  · have hrev1 := upD52_reversed (fun t => ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
        χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T ^ 2 + t ^ 2))
      (fun t => by positivity) (-Y) (-e) (by linarith)
    have hrev2 := upD52_reversed (fun t => ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
        χ m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T ^ 2 + t ^ 2))
      (fun t => by positivity) e Y (by linarith)
    rw [mul_assoc]
    nlinarith

end LeanLab.BHP1997.DecompC165d
