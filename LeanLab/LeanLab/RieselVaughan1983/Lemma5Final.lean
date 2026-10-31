import LeanLab.RieselVaughan1983.Lemma5Rows
import LeanLab.RieselVaughan1983.Lemma9

/-!
# P0032 Lemma 5 from (3.20): the last step of the paper's proof, p. 55

Session 20261020T2113Z-cloud51, unit U-6740, paper P0032 Riesel-Vaughan 1983, track T1.
AI wrote this Lean code. Binary Goldbach is OPEN; nothing here bears on it directly.

`Eq320Used L B` and `Eq320Neg L B` are the paper's (3.20), `R ≤ (8Cx/((log x)(B + log x)) + 2x^{1/2}) w`,
for `x ≥ e^L`, in the two shapes the lab uses. They are CITED: they rest on Montgomery-Vaughan
1973 Corollary 1 and on Lemma 4 with λ = 3/2, `F(x) > B`, neither in the lab.
Proved here: (3.20) at B together with (3.21) gives Lemma 5 at A, so the rows
`Lemma5Used 24 0`, `42 8`, `278 8.43`, `396 8.44` and `Lemma5Neg` are each CONDITIONAL ON
(3.20) at the matching B of the table, p. 54.
-/

namespace LeanLab.RieselVaughan1983

open Real Finset

/-- (3.21) in the form the paper uses: `8Cx/((log x)(B+log x)) + 102 x^{1/2} < 8Cx/((log x)(A+log x))`. -/
lemma key_102 (L A B x : ℝ) (h : Eq321 L A B) (hL : 6 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : Real.exp L ≤ x) :
    8 * Ctw * x / (Real.log x * (B + Real.log x)) + 102 * Real.sqrt x <
      8 * Ctw * x / (Real.log x * (A + Real.log x)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos L) hx
  set t := Real.log x with htdef
  have ht : L ≤ t := by rw [htdef, Real.le_log_iff_exp_le hx0]; exact hx
  have h' := eq321_mono L A B t h hL hA hB ht
  unfold Eq321 at h'
  set s := Real.exp (t / 2) with hs
  have hs0 : 0 < s := Real.exp_pos _
  have hxs : x = s ^ 2 := by
    rw [hs, ← Real.exp_nat_mul, htdef]; push_cast
    rw [show (2 : ℝ) * (Real.log x / 2) = Real.log x by ring, Real.exp_log hx0]
  have hsq : Real.sqrt x = s := by rw [hxs, Real.sqrt_sq hs0.le]
  rw [hsq, hxs]
  have ht0 : 0 < t := by linarith
  have hAt : 0 < t * (A + t) := by positivity
  have hBt : 0 < t * (B + t) := by positivity
  have hm := mul_lt_mul_of_pos_left h' (mul_pos ht0 hs0)
  rw [div_add' _ _ _ hBt.ne', div_lt_div_iff₀ hBt hAt]
  nlinarith [hm]

/-- (3.20), CITED, in the shape of `Lemma5Used`. -/
def Eq320Used (L B : ℝ) : Prop :=
  ∀ x : ℝ, Real.exp L ≤ x → ∀ h : ℕ, 0 < h →
    (#((Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + h).Prime)) : ℝ) ≤
      (8 * Ctw * x / (Real.log x * (B + Real.log x)) + 2 * Real.sqrt x) * wt h

/-- (3.20), CITED, in the shape of `Lemma5Neg`. -/
def Eq320Neg (L B : ℝ) : Prop :=
  ∀ ℓ : ℝ, Real.exp L ≤ ℓ → ∀ (c : ℝ) (n : ℕ), 0 < n →
    (#((range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime ∧ c ≤ p ∧ (p : ℝ) ≤ c + ℓ)) : ℝ) ≤
      (8 * Ctw * ℓ / (Real.log ℓ * (B + Real.log ℓ)) + 2 * Real.sqrt ℓ) * wt n

theorem lemma5Used_of (L A B : ℝ) (h : Eq321 L A B) (hL : 6 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (H : Eq320Used L B) : Lemma5Used L A := by
  intro x hx h0 hh
  have k := key_102 L A B x h hL hA hB hx
  have hs := Real.sqrt_nonneg x
  refine (H x hx h0 hh).trans (mul_le_mul_of_nonneg_right ?_ (wt_nonneg h0))
  linarith

lemma wt_pos (n : ℕ) : 0 < wt n := by
  rcases (wt_nonneg n).lt_or_eq with h | h
  · exact h
  · have := wt_mul_wn n; rw [← h, zero_mul] at this; norm_num at this

theorem lemma5Neg_of (h : Eq321 60 (83 / 10) (8302 / 1000)) (H : Eq320Neg 60 (8302 / 1000)) :
    Lemma5Neg := by
  intro ℓ hℓ c n hn
  have k := key_102 60 (83 / 10) (8302 / 1000) ℓ h (by norm_num) (by norm_num) (by norm_num)
    (le_trans (Real.exp_le_exp.mpr (by norm_num)) hℓ)
  refine lt_of_le_of_lt (H ℓ (le_trans (Real.exp_le_exp.mpr (by norm_num)) hℓ) c n hn) ?_
  exact mul_lt_mul_of_pos_right (by linarith) (wt_pos n)

theorem lemma5Used_24 (H : Eq320Used 24 (97 / 100)) : Lemma5Used 24 0 :=
  lemma5Used_of _ _ _ eq321_24 (by norm_num) le_rfl (by norm_num) H

theorem lemma5Used_42 (H : Eq320Used 42 (804 / 100)) : Lemma5Used 42 8 :=
  lemma5Used_of _ _ _ eq321_42 (by norm_num) (by norm_num) (by norm_num) H

theorem lemma5Used_278 (H : Eq320Used 278 (84301 / 10000)) : Lemma5Used 278 (843 / 100) :=
  lemma5Used_of _ _ _ eq321_278 (by norm_num) (by norm_num) (by norm_num) H

theorem lemma5Used_396 (H : Eq320Used 396 (844004 / 100000)) : Lemma5Used 396 (844 / 100) :=
  lemma5Used_of _ _ _ eq321_396 (by norm_num) (by norm_num) (by norm_num) H

theorem lemma5Neg_60 (H : Eq320Neg 60 (8302 / 1000)) : Lemma5Neg :=
  lemma5Neg_of eq321_60 H

end LeanLab.RieselVaughan1983
