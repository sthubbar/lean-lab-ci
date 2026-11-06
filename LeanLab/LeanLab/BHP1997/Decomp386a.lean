/-
P0069, page 25, displays 4.3 to 4.5. CODEX task386.
The original Perron leaf stays sealed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp312c

namespace LeanLab.BHP1997.Decomp386a
open Classical Complex Decomp312c
open scoped BigOperators

/-- Page 25, the number of integer terms differs from a suffix width by at most one. -/
theorem suffix_card_error {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    |((Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊).card : ℝ) - y| ≤ 1 := by
  have hx : 0 ≤ x := hy.trans hyx
  have hxy : 0 ≤ x - y := sub_nonneg.mpr hyx
  have hfloor : ⌊x - y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (by linarith)
  rw [Nat.card_Ioc, Nat.cast_sub hfloor, abs_le]
  have h1 := Nat.floor_le hx
  have h2 := Nat.floor_le hxy
  have h3 := Nat.lt_floor_add_one x
  have h4 := Nat.lt_floor_add_one (x - y)
  constructor <;> linarith

/-- Page 25, the reference average is bounded by twice a bound on its coefficients.
The extra factor accounts for integer endpoint rounding. -/
theorem suffix_average_bound (f : ℕ → ℂ) {x w M : ℝ}
    (hw : 1 ≤ w) (hwx : w ≤ x) (hM : 0 ≤ M)
    (hf : ∀ k ∈ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊, ‖f k‖ ≤ M) :
    ‖(∑ k ∈ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊, f k) / (w : ℂ)‖ ≤ 2 * M := by
  have hw0 : 0 < w := by linarith
  have hc := (abs_le.mp (suffix_card_error (by linarith : 0 ≤ w) hwx)).2
  have hs : ‖∑ k ∈ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊, f k‖ ≤
      ((Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊).card : ℝ) * M := by
    exact (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum hf)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
  apply (div_le_iff₀ hw0).mpr
  nlinarith

/-- Page 25, separate finite centering from the comparison with a continuous width. -/
theorem finite_centering_bound (S : Finset ℕ) (f : ℕ → ℂ) (r E : ℂ) (y : ℝ) (hy : 0 ≤ y) :
    ‖∑ k ∈ S, (f k - r)‖ ≤
      ‖(∑ k ∈ S, f k) - (y : ℂ) * E‖ +
        y * ‖E - r‖ + |(S.card : ℝ) - y| * ‖r‖ := by
  have he : (∑ k ∈ S, (f k - r)) =
      ((∑ k ∈ S, f k) - (y : ℂ) * E) +
        (y : ℂ) * (E - r) + ((y : ℂ) - S.card) * r := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ ‖((∑ k ∈ S, f k) - (y : ℂ) * E) + (y : ℂ) * (E - r)‖ +
        ‖((y : ℂ) - S.card) * r‖ := norm_add_le _ _
    _ ≤ (‖(∑ k ∈ S, f k) - (y : ℂ) * E‖ + ‖(y : ℂ) * (E - r)‖) +
        ‖((y : ℂ) - S.card) * r‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by
      rw [norm_mul, norm_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [show ((y : ℂ) - S.card) = ((y - (S.card : ℝ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      rw [abs_of_nonneg hy]

/-- Page 25, display 4.5 at y and the reference width implies finite centering.
Widths below two use only the coefficient bound. -/
theorem center_from_continuous_comparison (f : ℕ → ℂ) (E : ℂ)
    {x w C L P M : ℝ} (hw : 2 ≤ w) (hwx : w ≤ x)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hP : 0 ≤ P) (hM : 0 ≤ M)
    (hf : ∀ k ∈ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊, ‖f k‖ ≤ M)
    (hcomp : ∀ z : ℝ, 2 ≤ z → z ≤ w →
      ‖(∑ k ∈ Finset.Ioc ⌊x - z⌋₊ ⌊x⌋₊, f k) - (z : ℂ) * E‖ ≤
        C * (z * L + P))
    {y : ℝ} (hy : 0 ≤ y) (hyw : y ≤ w) :
    ‖∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊,
      (f k - (∑ j ∈ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊, f j) / (w : ℂ))‖ ≤
        2 * C * (y * L + P) + 9 * M := by
  let r : ℂ := (∑ j ∈ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊, f j) / (w : ℂ)
  have hw0 : 0 < w := by linarith
  have hr : ‖r‖ ≤ 2 * M := suffix_average_bound f (by linarith) hwx hM hf
  have hyx : y ≤ x := hyw.trans hwx
  have hsub : Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊ ⊆ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊ := by
    intro k hk
    obtain ⟨hkl, hku⟩ := Finset.mem_Ioc.mp hk
    exact Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.floor_mono (by linarith)) hkl, hku⟩
  have hc := suffix_card_error hy hyx
  by_cases hy2 : 2 ≤ y
  · have hdist : ‖E - r‖ ≤ C * (w * L + P) / w := by
      have he : E - r = -((∑ j ∈ Finset.Ioc ⌊x - w⌋₊ ⌊x⌋₊, f j) - (w : ℂ) * E) / (w : ℂ) := by
        dsimp [r]
        field_simp [show (w : ℂ) ≠ 0 by exact_mod_cast ne_of_gt hw0]
        ring
      rw [he, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
      exact div_le_div_of_nonneg_right (hcomp w hw le_rfl) hw0.le
    have hydiv : y / w ≤ 1 := (div_le_one hw0).mpr hyw
    have hrem : y * ‖E - r‖ ≤ C * (y * L + P) := by
      calc
        _ ≤ y * (C * (w * L + P) / w) := mul_le_mul_of_nonneg_left hdist hy
        _ = C * (y * L + y / w * P) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_of_le_one_left hP hydiv)) hC
    have hround : |((Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊).card : ℝ) - y| * ‖r‖ ≤ 2 * M := by
      calc
        _ ≤ 1 * ‖r‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
        _ ≤ _ := by simpa using hr
    have hfin := finite_centering_bound (Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊) f r E y hy
    have hwin := hcomp y hy2 hyw
    change ‖∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊, (f k - r)‖ ≤ _
    linarith
  · have hc3 : ((Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊).card : ℝ) ≤ 3 := by
      have := (abs_le.mp hc).2
      linarith
    have hs : ‖∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊, (f k - r)‖ ≤
        ((Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊).card : ℝ) * (3 * M) := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ _k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊, 3 * M := by
          apply Finset.sum_le_sum
          intro k hk
          have hkM := hf k (hsub hk)
          have ht := norm_sub_le (f k) r
          linarith
        _ = _ := by simp
    have hp : 0 ≤ 2 * C * (y * L + P) := by positivity
    have hm : ((Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊).card : ℝ) * (3 * M) ≤ 9 * M := by
      nlinarith
    exact hs.trans (by linarith)

end LeanLab.BHP1997.Decomp386a
