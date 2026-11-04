/-
Diagonal and off diagonal leaves for Lemma 3.8, pages 14 and 15.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp271a

namespace LeanLab.KumchevLiu2007.Task271b

open Real Complex Task129 Task129b
open scoped BigOperators

/-- Page 14 display 51. The squared norm of a finite complex sum splits
into its diagonal and ordered off diagonal terms. -/
theorem norm_sum_sq_split {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 =
      (∑ i ∈ s, ‖f i‖ ^ 2) +
      ∑ i ∈ s, ∑ j ∈ s.erase i, (f i * (starRingEnd ℂ) (f j)).re := by
  classical
  have full : ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, (f i * (starRingEnd ℂ) (f j)).re := by
    rw [Complex.sq_norm]
    have h := congrArg Complex.re (Complex.mul_conj (∑ i ∈ s, f i))
    simp only [Complex.ofReal_re] at h
    rw [← h]
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
  rw [full, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_erase_add _ _ hi]
  have h : (f i * (starRingEnd ℂ) (f i)).re = ‖f i‖ ^ 2 := by
    simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using
      congrArg Complex.re (Complex.mul_conj (f i))
  rw [h, add_comm]

/-- The smooth indicator on page 4 display 11 is either zero or one. -/
theorem smoothWeight_norm_le_one (q : ℕ) (Q : ℝ) :
    ‖(smoothWeight q Q : ℂ)‖ ≤ 1 := by
  classical
  unfold smoothWeight
  split <;> simp

/-- The reciprocal square tail over a natural interval telescopes. -/
theorem sum_inv_sq_Ioc_le (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    (∑ q ∈ Finset.Ioc a b, (1 / (q : ℝ) ^ 2)) ≤
      1 / (a : ℝ) - 1 / (b : ℝ) := by
  induction b generalizing a with
  | zero =>
      omega
  | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · simp only [Finset.Ioc_eq_empty_of_le (Nat.le_refl _), Finset.sum_empty]
        norm_num
      · have hab' : a ≤ b := by omega
        have hnot : b + 1 ∉ Finset.Ioc a b := by
          simp only [Finset.mem_Ioc]
          omega
        have heq : insert (b + 1) (Finset.Ioc a b) = Finset.Ioc a (b + 1) := by
          simpa using Finset.insert_Ioc_right_eq_Ioc_succ hab'
        rw [← heq, Finset.sum_insert hnot]
        have hi := ih a ha hab'
        push_cast at hi ⊢
        have hterm : 1 / (b + 1 : ℝ) ^ 2 ≤ 1 / (b : ℝ) - 1 / (b + 1 : ℝ) := by
          have hb_nat : 1 ≤ b := by omega
          have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb_nat
          field_simp
          nlinarith
        calc
          1 / (b + 1 : ℝ) ^ 2 + (∑ q ∈ Finset.Ioc a b, (1 / (q : ℝ) ^ 2))
              ≤ 1 / (b + 1 : ℝ) ^ 2 + (1 / (a : ℝ) - 1 / (b : ℝ)) := by
                simpa only [add_comm] using
                  add_le_add_right hi (1 / (b + 1 : ℝ) ^ 2)
          _ ≤ (1 / (b : ℝ) - 1 / (b + 1 : ℝ)) + (1 / (a : ℝ) - 1 / (b : ℝ)) := by
                gcongr
          _ = 1 / (a : ℝ) - 1 / (b + 1 : ℝ) := by ring

/-- LEAF. Page 15 first display, using the coefficient bound in display 47.
Only equal moduli occur in this diagonal sum. The smooth weights have
absolute value at most one. The coefficient summation remains OPEN. -/
theorem diagonal_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → 1 ≤ y → y ≤ x → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ‖-(smoothWeight q Q : ℂ) * U1534.A2 n q‖ ^ 2) ≤
        C * (y / P * Real.log x) := by
  sorry

/-- Page 15 after the third display. A fixed positive power of y absorbs
any fixed logarithmic loss when y is at least x to a positive epsilon. -/
theorem quarter_power_absorption (A ε : ℝ) (hε : 0 < ε) :
    ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x y : ℝ, x0 ≤ x → x ^ ε ≤ y →
      y ^ (3 / 4 : ℝ) ≤ y / Real.log x ^ A := by
  obtain ⟨x0, hb⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop A (show 0 < ε / 4 by linarith)).bound zero_lt_one)
  refine ⟨max x0 2, le_max_right _ _, ?_⟩
  intro x y hx hy
  have hx2 : 2 ≤ x := (le_max_right _ _).trans hx
  have hxp : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hyp : 0 < y := (Real.rpow_pos_of_pos hxp ε).trans_le hy
  have hl : Real.log x ^ A ≤ x ^ (ε / 4) := by
    have h := hb x ((le_max_left _ _).trans hx)
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hlog A),
      abs_of_pos (Real.rpow_pos_of_pos hxp (ε / 4)), one_mul] using h
  have hp : x ^ (ε / 4) ≤ y ^ (1 / 4 : ℝ) := by
    calc
      _ = (x ^ ε) ^ (1 / 4 : ℝ) := by rw [← Real.rpow_mul hxp.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hxp.le _) hy (by norm_num)
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hlog A)]
  calc
    _ ≤ y ^ (3 / 4 : ℝ) * y ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left (hl.trans hp) (Real.rpow_nonneg hyp.le _)
    _ = y := by rw [← Real.rpow_add hyp]; norm_num

/-- LEAF. Page 15 second and third displays in the proof of display 51.
Only distinct moduli occur. Display 47 and the incomplete period estimate
give a uniform y to the three quarters bound. This analytic summation
remains OPEN. The fixed constant absorbs the ordered pair factor two. -/
theorem off_diagonal_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x y P Q : ℝ,
      0 ≤ x → 1 ≤ y → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ((-(smoothWeight q Q : ℂ) * U1534.A2 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * U1534.A2 n r)).re) ≤
        C * y ^ (3 / 4 : ℝ) := by
  sorry

/-- Page 15 third display. The off diagonal logarithmic estimate follows
from the power saving leaf and elementary absorption.
CONDITIONAL on off_diagonal_power_bound. -/
theorem off_diagonal_bound (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ( (-(smoothWeight q Q : ℂ) * U1534.A2 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * U1534.A2 n r)).re) ≤
        C * (y / Real.log x ^ A) := by
  obtain ⟨C, hC, hb⟩ := off_diagonal_power_bound
  obtain ⟨x0, hx0, ha⟩ := quarter_power_absorption A ε hε
  refine ⟨C, x0, hC, hx0, ?_⟩
  intro x y P Q hx hy _hyx hP _hPQ _hQ
  have hx2 : 2 ≤ x := hx0.trans hx
  have hy1 : 1 ≤ y := (Real.one_le_rpow (by linarith : 1 ≤ x) hε.le).trans hy
  exact (hb x y P Q (by linarith) hy1 hP).trans
    (mul_le_mul_of_nonneg_left (ha x y hx hy) hC.le)

/-- Pages 14 and 15 display 51. This is exactly tail_mean_square_input,
assembled from separate diagonal and off diagonal leaves.
CONDITIONAL on the two OPEN analytic leaves. -/
theorem tail_mean_square_from_parts (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y, ‖tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
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
  have heq : (∑ n ∈ intervalNumbers x y, ‖tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) =
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ‖-(smoothWeight q Q : ℂ) * U1534.A2 n q‖ ^ 2) +
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ((-(smoothWeight q Q : ℂ) * U1534.A2 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * U1534.A2 n r)).re) := by
    simp only [tail2, norm_sum_sq_split, Finset.sum_add_distrib]
  rw [heq]
  have hm : 0 ≤ y / P * Real.log x := by positivity
  have he : 0 ≤ y / Real.log x ^ A := by positivity
  calc
    _ ≤ Cd * (y / P * Real.log x) + Co * (y / Real.log x ^ A) := add_le_add hd' ho'
    _ ≤ (Cd + Co) * (y / P * Real.log x + y / Real.log x ^ A) := by nlinarith

/-- Page 14 display 49. Lemma 3.8 for j equals two follows from the
three new analytic leaves. This assembly does not invoke either old
truncation_input or old tail_mean_square_input.
CONDITIONAL on the three OPEN analytic leaves. -/
theorem lemma38_from_decomposed_leaves : lemma38_two := by
  intro A ε hA hε
  obtain ⟨Ce, Xe, hCe, hXe, he⟩ := Task271a.truncation_from_pointwise A ε hA hε
  obtain ⟨Ct, Xt, hCt, hXt, ht⟩ := tail_mean_square_from_parts A ε hA hε
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
    (fun n => tail2 n P (y ^ (1 / 3 : ℝ)) Q)
    (fun n => (series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q)
  simp only [add_sub_cancel] at hs
  have hmain : 0 ≤ y / P * Real.log x := by positivity
  have herr : Ce * (y / Real.log x ^ A) ≤
      Ce * (y / P * Real.log x + y / Real.log x ^ A) := by
    nlinarith
  calc _ ≤ 2 * (∑ n ∈ intervalNumbers x y, ‖tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) +
      2 * (∑ n ∈ intervalNumbers x y,
        ‖(series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) := hs
    _ ≤ 2 * (Ct * (y / P * Real.log x + y / Real.log x ^ A)) +
      2 * (Ce * (y / Real.log x ^ A)) := by linarith
    _ ≤ 2 * (Ce + Ct) * (y / P * Real.log x + y / Real.log x ^ A) := by nlinarith

end LeanLab.KumchevLiu2007.Task271b

