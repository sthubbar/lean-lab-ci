/-
The three-square case of Lemma 3.8 on pages 14 and 15.
Three analytic supply leaves remain OPEN. All assemblies are CONDITIONAL on them.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp403b

namespace LeanLab.KumchevLiu2007.Task403c

open Real Complex Task129b Task129c
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Page 13 display 45. The truncated three-square singular series. -/
noncomputable def series3 (n : ℕ) (P : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, A3 n q

/-- Page 13 display 45 and property ii. The three-square singular product
has odd prime factors and a separate factor at 2 with powers through 8. -/
noncomputable def product3 (n : ℕ) (Q : ℝ) : ℂ :=
  (if 2 ≤ Q then 1 + A3 n 2 + A3 n 4 + A3 n 8 else 1) *
    ∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter (fun p => p.Prime ∧ 2 < p),
      (1 + A3 n p)

/-- Page 14 below display 50. Direct subtraction gives the coefficient minus Psi.
This retains the corrected sign already used for the two-variable tail. -/
noncomputable def tail3 (n : ℕ) (P T Q : ℝ) : ℂ :=
  ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊T⌋₊, -(smoothWeight q Q : ℂ) * A3 n q

/-- LEAF. Page 14 display 50 and the smooth tail bound immediately below it,
for j equal to three. Only the error after removing the finite tail remains.
The coefficient bound in display 47 and Lemma 3.5 are the analytic inputs. -/
theorem truncation_input (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ‖(series3 n P - product3 n Q) - tail3 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
          C * (y / Real.log x ^ A) := by
  sorry

/-- LEAF. Page 15 first display for j equal to three. This is only the
sum over equal moduli, using display 47 and the reciprocal square tail. -/
theorem diagonal_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → 1 ≤ y → y ≤ x → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ‖-(smoothWeight q Q : ℂ) * A3 n q‖ ^ 2) ≤
        C * (y / P * Real.log x) := by
  sorry

/-- LEAF. Page 15 second and third displays for j equal to three.
Only distinct moduli occur. Task403b proves the incomplete period step.
The remaining coefficient estimate and modulus summation stay OPEN. -/
theorem off_diagonal_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x y P Q : ℝ,
      0 ≤ x → 1 ≤ y → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ((-(smoothWeight q Q : ℂ) * A3 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * A3 n r)).re) ≤
        C * y ^ (3 / 4 : ℝ) := by
  sorry

/-- Page 15 third display. The power saving absorbs every fixed log loss.
CONDITIONAL on off_diagonal_power_bound. -/
theorem off_diagonal_bound (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ( (-(smoothWeight q Q : ℂ) * A3 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * A3 n r)).re) ≤
        C * (y / Real.log x ^ A) := by
  obtain ⟨C, hC, hb⟩ := off_diagonal_power_bound
  obtain ⟨x0, hx0, ha⟩ := Task271b.quarter_power_absorption A ε hε
  refine ⟨C, x0, hC, hx0, ?_⟩
  intro x y P Q hx hy _hyx hP _hPQ _hQ
  have hx2 : 2 ≤ x := hx0.trans hx
  have hy1 : 1 ≤ y := (Real.one_le_rpow (by linarith : 1 ≤ x) hε.le).trans hy
  exact (hb x y P Q (by linarith) hy1 hP).trans
    (mul_le_mul_of_nonneg_left (ha x y hx hy) hC.le)

/-- Page 14 display 51 for j equal to three, assembled by splitting the norm square.
CONDITIONAL on diagonal_bound and off_diagonal_power_bound. -/
theorem tail_mean_square_input (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y, ‖tail3 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) := by
  obtain ⟨Cd, xd, hCd, hxd, hd⟩ := diagonal_bound
  obtain ⟨Co, xo, hCo, hxo, ho⟩ := off_diagonal_bound A ε hA hε
  refine ⟨Cd + Co, max xd xo, by positivity, hxd.trans (le_max_left _ _), ?_⟩
  intro x y P Q hx hy hyx hP hPQ hQ
  have hxd' : xd ≤ x := (le_max_left _ _).trans hx
  have hxo' : xo ≤ x := (le_max_right _ _).trans hx
  have hx2 : 2 ≤ x := hxd.trans hxd'
  have hy1 : 1 ≤ y := (Real.one_le_rpow (by linarith : 1 ≤ x) hε.le).trans hy
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hd' := hd x y P Q hxd' hy1 hyx hP
  have ho' := ho x y P Q hxo' hy hyx hP hPQ hQ
  have heq : (∑ n ∈ intervalNumbers x y, ‖tail3 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) =
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ‖-(smoothWeight q Q : ℂ) * A3 n q‖ ^ 2) +
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ((-(smoothWeight q Q : ℂ) * A3 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * A3 n r)).re) := by
    simp only [tail3, Task271b.norm_sum_sq_split, Finset.sum_add_distrib]
  rw [heq]
  have hm : 0 ≤ y / P * Real.log x := by positivity
  have he : 0 ≤ y / Real.log x ^ A := by positivity
  calc
    _ ≤ Cd * (y / P * Real.log x) + Co * (y / Real.log x ^ A) := add_le_add hd' ho'
    _ ≤ (Cd + Co) * (y / P * Real.log x + y / Real.log x ^ A) := by nlinarith

/-- Page 14 display 49, Lemma 3.8 for j equal to three.
The statement uses complex norms for the real coefficients.
CONDITIONAL on the three OPEN analytic leaves in this file. -/
theorem lemma38_three :
  ∀ A ε : ℝ, 2 ≤ A → 0 < ε → ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧
    ∀ x y P Q : ℝ, x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y, ‖series3 n P - product3 n Q‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) := by
  intro A ε hA hε
  obtain ⟨Ce, Xe, hCe, hXe, he⟩ := truncation_input A ε hA hε
  obtain ⟨Ct, Xt, hCt, hXt, ht⟩ := tail_mean_square_input A ε hA hε
  refine ⟨2 * (Ce + Ct), max Xe Xt, by positivity,
    le_trans hXe (le_max_left _ _), ?_⟩
  intro x y P Q hx hy hyx hP hPQ hQ
  have hxe : Xe ≤ x := le_trans (le_max_left _ _) hx
  have hxt : Xt ≤ x := le_trans (le_max_right _ _) hx
  have hx2 : 2 ≤ x := hXe.trans hxe
  have hxp : 0 < x := by linarith
  have hyp : 0 < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hy
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have he' := he x y P Q hxe hy hyx hP hPQ hQ
  have ht' := ht x y P Q hxt hy hyx hP hPQ hQ
  have hs := mean_square_add (intervalNumbers x y)
    (fun n => tail3 n P (y ^ (1 / 3 : ℝ)) Q)
    (fun n => (series3 n P - product3 n Q) - tail3 n P (y ^ (1 / 3 : ℝ)) Q)
  simp only [add_sub_cancel] at hs
  have hmain : 0 ≤ y / P * Real.log x := by positivity
  have herr : Ce * (y / Real.log x ^ A) ≤
      Ce * (y / P * Real.log x + y / Real.log x ^ A) := by
    nlinarith
  calc _ ≤ 2 * (∑ n ∈ intervalNumbers x y, ‖tail3 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) +
      2 * (∑ n ∈ intervalNumbers x y,
        ‖(series3 n P - product3 n Q) - tail3 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) := hs
    _ ≤ 2 * (Ct * (y / P * Real.log x + y / Real.log x ^ A)) +
      2 * (Ce * (y / Real.log x ^ A)) := by linarith
    _ ≤ 2 * (Ce + Ct) * (y / P * Real.log x + y / Real.log x ^ A) := by nlinarith

end LeanLab.KumchevLiu2007.Task403c
