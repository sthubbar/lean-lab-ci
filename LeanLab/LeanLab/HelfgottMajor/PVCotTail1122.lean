import Mathlib
import LeanLab.HelfgottMajor.PVEvenTrunc1122
import LeanLab.HelfgottMajor.PVTailAbel1122

/-!
Route burst S75, burst-20261122, tag cot-tail. Split of the HARD LEAF
`PVEvenTrunc1122.cot_tail` along Pomerance 2011, Integers 11A Article 19, Section 3, the bound
for B_n on page 8 and the choice of n, with the cotangent tail of Frolenkov display 12 in place
of Pomerance's Fourier tail. The assembly `cot_tail` has exactly the statement of the LEAF,
checked by `type_of%`.

Route. For 5 ≤ q ≤ 80 take H = (q-1)/2: the tail is empty for q odd and is the single term
h = q/2 with cot(π/2) = 0 for q even, so only budget ≥ 1/2 is needed. For q ≥ 81 take
H = ⌊√q log q⌋, Pomerance's n = ⌊2 √q log q⌋ up to the factor 2 that the cotangent form saves:
display 7 duality `PVTailAbel1122.dual_bound`, sin = (e - e⁻¹)/(2i), the Abel bound of Lemma 4
and the cosecant sum of display 5 give the tail over 2√q at most 2q/(π²(H+1)) (log q + log(4/π)
+ π²/(12q²)), and the closing inequality is a numerical check. q ∈ {2, 3, 4} has no even primitive
character.

Numerical screen, Python, double precision: the closing inequality for H = ⌊√q log q⌋ holds for
every q from 81 to 200000 with slack above 0.26 √q from q = 1000 on, and budget ≥ 1/2 at
H = (q-1)/2 holds for every q from 5 to 80. The Abel and duality steps were checked on Legendre
characters for q up to 1013, worst ratio to the bound 0.56.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVCotTail1122Aux.Easy
open Real Finset
open Real Finset

lemma units_pm (q : ℕ) (hq2 : 2 ≤ q) (hq4 : q ≤ 4) :
    ∀ u : (ZMod q)ˣ, u = 1 ∨ u = -1 := by
  interval_cases q <;> decide

theorem even_primitive_ge_five_proof {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) : 5 ≤ q := by
  by_contra hlt
  have hq0 : q ≠ 0 := NeZero.ne q
  have h1 : χ = 1 := by
    apply MulChar.ext
    intro u
    rcases units_pm q (by omega) (by omega) u with h | h
    · subst h; simp
    · subst h
      simp only [Units.val_neg, Units.val_one]
      rw [heven]; exact (MulChar.one_apply isUnit_one.neg).symm
  have := hχ
  rw [DirichletCharacter.IsPrimitive, h1, DirichletCharacter.conductor_one] at this
  exact hq this.symm
theorem tail_empty_proof {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (K : ℕ) :
    ∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ (q - 1) / 2 ∨ q - (q - 1) / 2 ≤ h.val)),
        χ⁻¹ h * ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ) = 0 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  refine sum_eq_zero fun h hh => ?_
  simp only [mem_filter, mem_univ, true_and] at hh
  have h2 : 2 * h.val = q := by omega
  have h2r : (2 : ℝ) * h.val = q := by exact_mod_cast h2
  have : π * (h.val : ℝ) / q = π / 2 := by
    have hq0 := Nat.pos_of_ne_zero (NeZero.ne q)
    have hv0 : (h.val : ℝ) ≠ 0 := by
      have : 0 < h.val := by omega
      exact_mod_cast this.ne'
    rw [← h2r]; field_simp
  rw [this, Real.cot_eq_cos_div_sin, cos_pi_div_two]
  simp
end LeanLab.HelfgottMajor.PVCotTail1122Aux.Easy

namespace LeanLab.HelfgottMajor.PVCotTail1122Aux.Dual
open Real Finset
open Real Finset

theorem sin_char {q : ℕ} [NeZero q] (h : ZMod q) (K : ℕ) :
    ((sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ) =
      (ZMod.stdAddChar ((K : ZMod q) * h) - ZMod.stdAddChar (-((K : ZMod q) * h))) /
        (2 * Complex.I) := by
  rw [AddChar.map_neg_eq_inv, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, ZMod.stdAddChar_apply,
    ZMod.toCircle_apply, ← Complex.exp_nat_mul, ← Complex.exp_neg, Complex.ofReal_sin,
    Complex.sin]
  have hA : (K : ℂ) * (2 * π * Complex.I * h.val / q) =
      ((2 * π * K * (h.val : ℝ) / q : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hA]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem even_tail_dual_proof {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (H K : ℕ) :
    ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        χ⁻¹ h * ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ ≤
      1 / sqrt q * ∑ b : ZMod q, ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        (cot (π * h.val / q) : ℂ) * ZMod.stdAddChar (b * h)‖ := by
  set S := univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)) with hS
  set V : ZMod q → ℂ := fun b => ∑ h ∈ S, (cot (π * h.val / q) : ℂ) * ZMod.stdAddChar (b * h)
    with hV
  refine (LeanLab.HelfgottMajor.PVTailAbel1122.dual_bound hχ S _).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have key : ∀ a : ZMod q, ∑ h ∈ S,
      ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ) *
        ZMod.stdAddChar (a * h) = (V (a + K) - V (a - K)) / (2 * Complex.I) := by
    intro a
    simp only [hV]
    rw [← sum_sub_distrib, sum_div]
    refine sum_congr rfl fun h _ => ?_
    have e1 : ZMod.stdAddChar ((a + (K : ZMod q)) * h) =
        ZMod.stdAddChar ((K : ZMod q) * h) * ZMod.stdAddChar (a * h) := by
      rw [add_mul, AddChar.map_add_eq_mul, mul_comm]
    have e2 : ZMod.stdAddChar ((a - (K : ZMod q)) * h) =
        ZMod.stdAddChar (-((K : ZMod q) * h)) * ZMod.stdAddChar (a * h) := by
      rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, mul_comm]
    rw [e1, e2, Complex.ofReal_mul, sin_char h K]
    ring
  have hb : ∀ a : ZMod q, ‖(V (a + K) - V (a - K)) / (2 * Complex.I)‖ ≤
      (‖V (a + K)‖ + ‖V (a - K)‖) / 2 := by
    intro a
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
  calc ∑ a : ZMod q, ‖∑ h ∈ S,
      ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ) *
        ZMod.stdAddChar (a * h)‖
      ≤ ∑ a : ZMod q, (‖V (a + K)‖ + ‖V (a - K)‖) / 2 :=
        sum_le_sum fun a _ => by rw [key a]; exact hb a
    _ = (∑ a : ZMod q, ‖V (a + K)‖ + ∑ a : ZMod q, ‖V (a + -(K : ZMod q))‖) / 2 := by
        rw [← sum_div, sum_add_distrib]; simp only [sub_eq_add_neg]
    _ = ∑ b : ZMod q, ‖V b‖ := by
        have r1 : ∑ a : ZMod q, ‖V (a + K)‖ = ∑ b : ZMod q, ‖V b‖ :=
          Equiv.sum_comp (Equiv.addRight (K : ZMod q)) (fun b => ‖V b‖)
        have r2 : ∑ a : ZMod q, ‖V (a + -(K : ZMod q))‖ = ∑ b : ZMod q, ‖V b‖ :=
          Equiv.sum_comp (Equiv.addRight (-(K : ZMod q))) (fun b => ‖V b‖)
        rw [r1, r2]
        ring
end LeanLab.HelfgottMajor.PVCotTail1122Aux.Dual

open Real Finset

namespace LeanLab.HelfgottMajor.PVCotTail1122Aux.Small

lemma fin_step (s Y P y0 s0 : ℝ) (hY : y0 ≤ Y) (hy0 : y0 ≤ 0) (hP : 9.8596 ≤ P)
    (hs : s0 ≤ s) (hs0 : 0 ≤ s0) (hc : 0 ≤ 3 / 4 + y0 / 9.8596)
    (h : 1 / 2 ≤ s0 * (3 / 4 + y0 / 9.8596)) : 1 / 2 ≤ s * (3 / 4 + Y / P) := by
  have hPpos : 0 < P := by linarith
  have h1 : y0 / P ≤ Y / P := div_le_div_of_nonneg_right hY hPpos.le
  have h2 : y0 / 9.8596 ≤ y0 / P := by
    rw [div_le_div_iff₀ (by norm_num) hPpos]; nlinarith
  have hC : 3 / 4 + y0 / 9.8596 ≤ 3 / 4 + Y / P := by linarith
  calc (1:ℝ) / 2 ≤ s0 * (3 / 4 + y0 / 9.8596) := h
    _ ≤ s * (3 / 4 + Y / P) := mul_le_mul hs hC hc (hs0.trans hs)

lemma pi_sq_ge : (9.8596 : ℝ) ≤ π ^ 2 := by
  have := pi_gt_d2
  nlinarith

lemma log4 : log (4:ℝ) = 2 * log 2 := by
  rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

lemma log5_ge : (1.586 : ℝ) ≤ log 5 := by
  have h : log (5:ℝ) = log 4 + log (5/4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 5/4 by norm_num)
  rw [h, log4]
  have := log_two_gt_d9
  norm_num at h2
  linarith

lemma log3_le : log (3:ℝ) ≤ 1.13630 := by
  have h : log (3:ℝ) = log 4 + log (3/4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3/4 by norm_num)
  rw [h, log4]
  have := log_two_lt_d9
  linarith

lemma log12_le : log (12:ℝ) ≤ 2.5226 := by
  have h : log (12:ℝ) = log (2^4) + log (3/4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3/4 by norm_num)
  rw [h, Real.log_pow]
  have := log_two_lt_d9
  push_cast
  linarith

lemma log32_le : log (32:ℝ) ≤ 3.4658 := by
  rw [show (32:ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
  have := log_two_lt_d9
  push_cast
  linarith

lemma log80_le : log (80:ℝ) ≤ 4.409 := by
  have h : log (80:ℝ) = log (2^6) + log (5/4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 5/4 by norm_num)
  rw [h, Real.log_pow]
  have := log_two_lt_d9
  push_cast
  linarith

lemma rewrite_expr (s L LL LH g l2 H P : ℝ) (hP : 0 < P) (hH : 0 < H) :
    (1 / P * s * L + 2 / P * s * LL + 3 / 4 * s - 2 / P * s * (LH + g + l2 + 3 / H)) =
      s * (3 / 4 + (L + 2 * LL - 2 * LH - 2 * g - 2 * l2 - 6 / H) / P) := by
  field_simp
  ring

theorem budget_small_proof {q : ℕ} (hq5 : 5 ≤ q) (hq80 : q ≤ 80) :
    1 / 2 ≤ (1 / π ^ 2 * sqrt (q:ℝ) * log (q:ℝ) + 2 / π ^ 2 * sqrt (q:ℝ) * log (log (q:ℝ)) + 3 / 4 * sqrt (q:ℝ) -
          2 / π ^ 2 * sqrt (q:ℝ) * (log (((q - 1) / 2 : ℕ) : ℝ) + eulerMascheroniConstant + log 2 + 3 / (((q - 1) / 2 : ℕ) : ℝ))) := by
  set H : ℕ := (q - 1) / 2 with hHdef
  have hH2 : 2 ≤ H := by omega
  have hHq : 2 * H ≤ q := by omega
  have hHq' : q ≤ 2 * H + 2 := by omega
  have hHr : (2:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH2
  have hHqr : 2 * (H:ℝ) ≤ (q:ℝ) := by exact_mod_cast hHq
  have hHqr' : (q:ℝ) ≤ 2 * (H:ℝ) + 2 := by exact_mod_cast hHq'
  have hHpos : (0:ℝ) < H := by linarith
  have hqr5 : (5:ℝ) ≤ q := by exact_mod_cast hq5
  have hqr80 : (q:ℝ) ≤ 80 := by exact_mod_cast hq80
  have hqpos : (0:ℝ) < q := by linarith
  have hPpos : (0:ℝ) < π ^ 2 := by positivity
  rw [rewrite_expr _ _ _ _ _ _ _ _ hPpos hHpos]
  have hP := pi_sq_ge
  have hg := Real.eulerMascheroniConstant_lt_two_thirds
  have hl2 := log_two_lt_d9
  have hl2' := log_two_gt_d9
  have hlq5 : log (5:ℝ) ≤ log q := Real.log_le_log (by norm_num) hqr5
  have hl5 := log5_ge
  have hlqpos : (0:ℝ) < log q := by linarith
  have hLL : 1 - (log q)⁻¹ ≤ log (log q) := Real.one_sub_inv_le_log_of_pos hlqpos
  have hinv : (log q)⁻¹ ≤ 1 / 1.586 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hLL' : (0.369:ℝ) ≤ log (log q) := by
    have : (1:ℝ) / 1.586 ≤ 0.631 := by norm_num
    linarith
  -- log(2H) ≤ log q
  have hlogH : log (H:ℝ) + log 2 ≤ log q := by
    rw [← Real.log_mul hHpos.ne' (by norm_num)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hsq0 : 0 ≤ sqrt (q:ℝ) := Real.sqrt_nonneg _
  rcases (show q ≤ 6 ∨ (7 ≤ q ∧ q ≤ 8) ∨ (9 ≤ q ∧ q ≤ 12) ∨ (13 ≤ q ∧ q ≤ 32) ∨ 33 ≤ q by omega) with
    h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
  · -- H = 2
    have hHe : H = 2 := by omega
    have hHe' : (H:ℝ) = 2 := by rw [hHe]; norm_num
    rw [hHe']
    have hs : (2.236:ℝ) ≤ sqrt q :=
      Real.le_sqrt_of_sq_le (by nlinarith)
    refine fin_step _ _ _ (-4.782) 2.236 ?_ (by norm_num) hP hs (by norm_num) (by norm_num)
      (by norm_num)
    linarith
  · have hHe : H = 3 := by omega
    have hHe' : (H:ℝ) = 3 := by rw [hHe]; norm_num
    rw [hHe']
    have h3 := log3_le
    have hs : (2.645:ℝ) ≤ sqrt q :=
      Real.le_sqrt_of_sq_le (by have : (7:ℝ) ≤ q := by exact_mod_cast h1
                                nlinarith)
    refine fin_step _ _ _ (-4.669) 2.645 ?_ (by norm_num) hP hs (by norm_num) (by norm_num)
      (by norm_num)
    linarith
  · have ha : (9:ℝ) ≤ q := by exact_mod_cast h1
    have hb : (q:ℝ) ≤ 12 := by exact_mod_cast h2
    have hLb : log (q:ℝ) ≤ 2.5226 := (Real.log_le_log hqpos hb).trans log12_le
    have hHa : (3.5:ℝ) ≤ H := by linarith
    have h6 : 6 / (H:ℝ) ≤ 6 / 3.5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hHa
    have hs : (3:ℝ) ≤ sqrt q := Real.le_sqrt_of_sq_le (by nlinarith)
    refine fin_step _ _ _ (-5.5703) 3 ?_ (by norm_num) hP hs (by norm_num) (by norm_num)
      (by norm_num)
    have : (6:ℝ) / 3.5 ≤ 1.71429 := by norm_num
    linarith
  · have ha : (13:ℝ) ≤ q := by exact_mod_cast h1
    have hb : (q:ℝ) ≤ 32 := by exact_mod_cast h2
    have hLb : log (q:ℝ) ≤ 3.4658 := (Real.log_le_log hqpos hb).trans log32_le
    have hHa : (5.5:ℝ) ≤ H := by linarith
    have h6 : 6 / (H:ℝ) ≤ 6 / 5.5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hHa
    have hs : (3.6:ℝ) ≤ sqrt q := Real.le_sqrt_of_sq_le (by nlinarith)
    refine fin_step _ _ _ (-5.8901) 3.6 ?_ (by norm_num) hP hs (by norm_num) (by norm_num)
      (by norm_num)
    have : (6:ℝ) / 5.5 ≤ 1.09091 := by norm_num
    linarith
  · have ha : (33:ℝ) ≤ q := by exact_mod_cast h1
    have hLb : log (q:ℝ) ≤ 4.409 := (Real.log_le_log hqpos hqr80).trans log80_le
    have hHa : (15.5:ℝ) ≤ H := by linarith
    have h6 : 6 / (H:ℝ) ≤ 6 / 15.5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hHa
    have hs : (5.7:ℝ) ≤ sqrt q := Real.le_sqrt_of_sq_le (by nlinarith)
    refine fin_step _ _ _ (-6.1295) 5.7 ?_ (by norm_num) hP hs (by norm_num) (by norm_num)
      (by norm_num)
    have : (6:ℝ) / 15.5 ≤ 0.38710 := by norm_num
    linarith

end LeanLab.HelfgottMajor.PVCotTail1122Aux.Small

open Real Finset

namespace LeanLab.HelfgottMajor.PVCotTail1122Aux.Close

lemma log82_le : log (82:ℝ) ≤ 19 * 0.6931471808 / 3 + (551368 / 524288 - 1) / 3 := by
  have h1 : log ((82:ℝ)^3) = 3 * log 82 := by rw [log_pow]; norm_num
  have h2 : ((82:ℝ)^3) = 2^19 * (551368 / 524288) := by norm_num
  have h3 : log ((2:ℝ)^19 * (551368 / 524288)) = 19 * log 2 + log (551368 / 524288) := by
    rw [log_mul (by norm_num) (by norm_num), log_pow]; norm_num
  have h4 := log_le_sub_one_of_pos (show (0:ℝ) < 551368 / 524288 by norm_num)
  have h5 := log_two_lt_d9
  rw [h2, h3] at h1
  linarith

lemma exp4_le : exp (4:ℝ) ≤ 81 := by
  have : exp (4:ℝ) = exp 1 ^ 4 := by rw [← exp_nat_mul]; norm_num
  rw [this]
  have h := exp_one_lt_d9
  calc exp 1 ^ 4 ≤ (2.72:ℝ) ^ 4 := pow_le_pow_left₀ (exp_pos 1).le (by linarith) 4
    _ ≤ 81 := by norm_num

theorem even_one {q : ℕ} (hq : 81 ≤ q) :
    1 ≤ ⌊sqrt q * log q⌋₊ := by
  have hqR : (81:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hss : sqrt (q:ℝ) * sqrt (q:ℝ) = q := mul_self_sqrt hq0.le
  have hs9 : 9 ≤ sqrt (q:ℝ) := by
    rw [show (9:ℝ) = sqrt 81 by rw [show (81:ℝ) = 9^2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt hqR
  have hL4 : 4 ≤ log (q:ℝ) := by
    rw [le_log_iff_exp_le hq0]; linarith [exp4_le]
  have hLs : log (q:ℝ) = 2 * log (sqrt (q:ℝ)) := by rw [log_sqrt hq0.le]; ring
  set s := sqrt (q:ℝ) with hs
  set L := log (q:ℝ) with hLdef
  have hs0 : 0 < s := by linarith
  have hlogs : log s ≤ s / 16 - 1 + 4 * log 2 := by
    have h := log_le_sub_one_of_pos (show 0 < s / 16 by positivity)
    rw [log_div hs0.ne' (by norm_num), show (16:ℝ) = 2 ^ 4 by norm_num, log_pow] at h
    push_cast at h; linarith
  set x := s * L with hx
  set H := ⌊x⌋₊ with hH
  have hx0 : 0 ≤ x := by positivity
  have hHx : (H:ℝ) ≤ x := Nat.floor_le hx0
  have hxH : x < H + 1 := Nat.lt_floor_add_one x
  have hx36 : 36 ≤ x := by nlinarith
  have hH35 : (35:ℝ) < H := by linarith
  have hH1 : 1 ≤ H := by
    have : (1:ℝ) ≤ H := by linarith
    exact_mod_cast this
  have hl2 := log_two_lt_d9
  have hl2' := log_two_gt_d9
  exact hH1

theorem even_two {q : ℕ} (hq : 81 ≤ q) :
    2 * (⌊sqrt q * log q⌋₊ + 1) < q := by
  have hqR : (81:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hss : sqrt (q:ℝ) * sqrt (q:ℝ) = q := mul_self_sqrt hq0.le
  have hs9 : 9 ≤ sqrt (q:ℝ) := by
    rw [show (9:ℝ) = sqrt 81 by rw [show (81:ℝ) = 9^2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt hqR
  have hL4 : 4 ≤ log (q:ℝ) := by
    rw [le_log_iff_exp_le hq0]; linarith [exp4_le]
  have hLs : log (q:ℝ) = 2 * log (sqrt (q:ℝ)) := by rw [log_sqrt hq0.le]; ring
  set s := sqrt (q:ℝ) with hs
  set L := log (q:ℝ) with hLdef
  have hs0 : 0 < s := by linarith
  have hlogs : log s ≤ s / 16 - 1 + 4 * log 2 := by
    have h := log_le_sub_one_of_pos (show 0 < s / 16 by positivity)
    rw [log_div hs0.ne' (by norm_num), show (16:ℝ) = 2 ^ 4 by norm_num, log_pow] at h
    push_cast at h; linarith
  set x := s * L with hx
  set H := ⌊x⌋₊ with hH
  have hx0 : 0 ≤ x := by positivity
  have hHx : (H:ℝ) ≤ x := Nat.floor_le hx0
  have hxH : x < H + 1 := Nat.lt_floor_add_one x
  have hx36 : 36 ≤ x := by nlinarith
  have hH35 : (35:ℝ) < H := by linarith
  have hH1 : 1 ≤ H := by
    have : (1:ℝ) ≤ H := by linarith
    exact_mod_cast this
  have hl2 := log_two_lt_d9
  have hl2' := log_two_gt_d9
  rcases le_or_gt 100 q with h100 | h100
  · have h100R : (100:ℝ) ≤ q := by exact_mod_cast h100
    have hs10 : 10 ≤ s := by nlinarith
    have hLb : L ≤ s / 8 + 3.5453 := by linarith
    have hxb : x ≤ s * (s / 8 + 3.5453) := mul_le_mul_of_nonneg_left hLb hs0.le
    have : (2:ℝ) * (H + 1) < q := by nlinarith
    exact_mod_cast this
  · have hq99 : (q:ℝ) ≤ 99 := by exact_mod_cast (show q ≤ 99 by omega)
    have ht := log_le_sub_one_of_pos (show (0:ℝ) < q / 82 by positivity)
    rw [log_div hq0.ne' (by norm_num)] at ht
    have h82 := log82_le
    have hLB : L ≤ 19 * 0.6931471808 / 3 + (551368 / 524288 - 1) / 3 + (q - 82) / 82 := by
      linarith
    have hx2 : x * x = q * (L * L) := by rw [hx, ← hss]; ring
    have hL0 : 0 ≤ L := by linarith
    have hLL : L * L ≤ (19 * 0.6931471808 / 3 + (551368 / 524288 - 1) / 3 + (q - 82) / 82) ^ 2 := by
      nlinarith
    rcases eq_or_lt_of_le hq with h81 | h82'
    · have hq81 : (q:ℝ) = 81 := by rw [← h81]; norm_num
      rw [hq81] at hx2 hLL
      have hx40 : x < 40 := by nlinarith
      have : (H:ℝ) < 40 := by linarith
      have : H < 40 := by exact_mod_cast this
      omega
    · have h82R : (82:ℝ) ≤ q := by exact_mod_cast h82'
      have hm : x * x < ((q - 2) / 2) ^ 2 := by
        rw [hx2]
        calc (q:ℝ) * (L * L) ≤ q * (19 * 0.6931471808 / 3 + (551368 / 524288 - 1) / 3 + (q - 82) / 82) ^ 2 :=
              mul_le_mul_of_nonneg_left hLL hq0.le
          _ < ((q - 2) / 2) ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.2 h82R) (sub_nonneg.2 hq99)]
      have hxm : x < (q - 2) / 2 := by nlinarith
      have : (2:ℝ) * (H + 1) < q := by linarith
      exact_mod_cast this

theorem even_main {q : ℕ} (hq : 81 ≤ q) :
      1 / 2 + 2 * q / (π ^ 2 * (⌊sqrt q * log q⌋₊ + 1)) *
          (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2)) ≤
        (1 / π ^ 2 * sqrt (q:ℝ) * log (q:ℝ) + 2 / π ^ 2 * sqrt (q:ℝ) * log (log (q:ℝ)) + 3 / 4 * sqrt (q:ℝ) -
          2 / π ^ 2 * sqrt (q:ℝ) * (log (⌊sqrt q * log q⌋₊ : ℝ) + eulerMascheroniConstant + log 2 + 3 / (⌊sqrt q * log q⌋₊ : ℝ))) := by
  have hqR : (81:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hss : sqrt (q:ℝ) * sqrt (q:ℝ) = q := mul_self_sqrt hq0.le
  have hs9 : 9 ≤ sqrt (q:ℝ) := by
    rw [show (9:ℝ) = sqrt 81 by rw [show (81:ℝ) = 9^2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt hqR
  have hL4 : 4 ≤ log (q:ℝ) := by
    rw [le_log_iff_exp_le hq0]; linarith [exp4_le]
  have hLs : log (q:ℝ) = 2 * log (sqrt (q:ℝ)) := by rw [log_sqrt hq0.le]; ring
  set s := sqrt (q:ℝ) with hs
  set L := log (q:ℝ) with hLdef
  have hs0 : 0 < s := by linarith
  have hlogs : log s ≤ s / 16 - 1 + 4 * log 2 := by
    have h := log_le_sub_one_of_pos (show 0 < s / 16 by positivity)
    rw [log_div hs0.ne' (by norm_num), show (16:ℝ) = 2 ^ 4 by norm_num, log_pow] at h
    push_cast at h; linarith
  set x := s * L with hx
  set H := ⌊x⌋₊ with hH
  have hx0 : 0 ≤ x := by positivity
  have hHx : (H:ℝ) ≤ x := Nat.floor_le hx0
  have hxH : x < H + 1 := Nat.lt_floor_add_one x
  have hx36 : 36 ≤ x := by nlinarith
  have hH35 : (35:ℝ) < H := by linarith
  have hH1 : 1 ≤ H := by
    have : (1:ℝ) ≤ H := by linarith
    exact_mod_cast this
  have hl2 := log_two_lt_d9
  have hl2' := log_two_gt_d9
  have hpi := pi_gt_d2
  have hpi2 : (9.8596:ℝ) ≤ π ^ 2 := by nlinarith
  have hγ := eulerMascheroniConstant_lt_two_thirds
  have hl4 : log (4 / π) ≤ 0.2739 := by
    have h := log_le_sub_one_of_pos (show 0 < 4 / π by positivity)
    have : 4 / π ≤ 4 / 3.14 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi.le
    linarith [show (4:ℝ) / 3.14 ≤ 1.2739 by norm_num]
  have hl4' : 0 ≤ log (4 / π) := log_nonneg (by rw [le_div_iff₀ pi_pos]; linarith [pi_lt_four])
  have htiny : π ^ 2 / (12 * (q:ℝ) ^ 2) ≤ 0.001 := by
    have hp16 : π ^ 2 ≤ 16 := by nlinarith [pi_lt_four, pi_pos]
    have hq2 : (6561:ℝ) ≤ (q:ℝ) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]; linarith
  have htiny' : 0 ≤ π ^ 2 / (12 * (q:ℝ) ^ 2) := by positivity
  set Lq := L + log (4 / π) + π ^ 2 / (12 * (q:ℝ) ^ 2) with hLq
  set K := 2 / π ^ 2 * s with hK
  have hK0 : 0 < K := by positivity
  have hKs : K ≤ 0.2029 * s := by
    rw [hK, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  have hA : 2 * (q:ℝ) / (π ^ 2 * (H + 1)) ≤ K / L := by
    rw [hK, div_le_div_iff₀ (by positivity) (by positivity), ← hss]
    have : 0 < π ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_left hxH.le (show 0 ≤ 2 * s * π ^ 2 by positivity)
    rw [hx] at h
    field_simp
    nlinarith
  have hLq0 : 0 ≤ Lq := by positivity
  have hALq : 2 * (q:ℝ) / (π ^ 2 * (H + 1)) * Lq ≤ K * 1.0688 := by
    calc _ ≤ K / L * Lq := mul_le_mul_of_nonneg_right hA hLq0
      _ = K * (Lq / L) := by ring
      _ ≤ K * 1.0688 := by
        apply mul_le_mul_of_nonneg_left _ hK0.le
        rw [div_le_iff₀ (by linarith)]; linarith
  have hlogH : log (H:ℝ) ≤ L / 2 + log L := by
    have h := log_le_log (by linarith) hHx
    rw [hx, log_mul hs0.ne' (by linarith)] at h
    linarith
  have h1 : K * log (H:ℝ) ≤ K * (L / 2 + log L) := mul_le_mul_of_nonneg_left hlogH hK0.le
  have h2 : K * eulerMascheroniConstant ≤ K * (2 / 3) := mul_le_mul_of_nonneg_left hγ.le hK0.le
  have h3 : K * log 2 ≤ K * 0.6932 := mul_le_mul_of_nonneg_left (by linarith) hK0.le
  have h4 : K * (3 / (H:ℝ)) ≤ K * (3 / 35) := by
    apply mul_le_mul_of_nonneg_left _ hK0.le
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hH35.le
  have hKL : 1 / π ^ 2 * s * L = K * L / 2 := by rw [hK]; ring
  rw [hKL]
  have e : K * (log (H:ℝ) + eulerMascheroniConstant + log 2 + 3 / (H:ℝ)) =
    K * log (H:ℝ) + K * eulerMascheroniConstant + K * log 2 + K * (3 / (H:ℝ)) := by ring
  rw [e]
  have e2 : K * (L / 2 + log L) = K * L / 2 + K * log L := by ring
  linarith

theorem close_large_proof {q : ℕ} (hq : 81 ≤ q) :
    1 ≤ ⌊sqrt q * log q⌋₊ ∧ 2 * (⌊sqrt q * log q⌋₊ + 1) < q ∧
      1 / 2 + 2 * q / (π ^ 2 * (⌊sqrt q * log q⌋₊ + 1)) *
          (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2)) ≤
        (1 / π ^ 2 * sqrt (q:ℝ) * log (q:ℝ) + 2 / π ^ 2 * sqrt (q:ℝ) * log (log (q:ℝ)) + 3 / 4 * sqrt (q:ℝ) -
          2 / π ^ 2 * sqrt (q:ℝ) * (log (⌊sqrt q * log q⌋₊ : ℝ) + eulerMascheroniConstant + log 2 + 3 / (⌊sqrt q * log q⌋₊ : ℝ))) := ⟨even_one hq, even_two hq, even_main hq⟩

end LeanLab.HelfgottMajor.PVCotTail1122Aux.Close

namespace LeanLab.HelfgottMajor.PVCotTail1122

open Real Finset

/-- PROVED in S75, formerly LEAF: Pomerance 2011 Section 3 first line, an even primitive character has modulus q ≥ 5:
for q ∈ {2, 3, 4} every unit is ±1, so χ(-1) = 1 forces χ = 1, which is not primitive for
q ≠ 1. Class EASY. -/
theorem even_primitive_ge_five {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) : 5 ≤ q := by
  apply LeanLab.HelfgottMajor.PVCotTail1122Aux.Easy.even_primitive_ge_five_proof <;> assumption

/-- PROVED in S75, formerly LEAF: Pomerance 2011 Section 3, the case of the largest n, empty tail: at H = (q-1)/2 the
tail H < h < q - H is empty for q odd and is {q/2} with cot(π/2) = 0 for q even, so the tail sum
vanishes. Class EASY. -/
theorem tail_empty {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (K : ℕ) :
    ∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ (q - 1) / 2 ∨ q - (q - 1) / 2 ≤ h.val)),
        χ⁻¹ h * ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ) = 0 := by
  apply LeanLab.HelfgottMajor.PVCotTail1122Aux.Easy.tail_empty_proof <;> assumption

/-- PROVED in S75, formerly LEAF: Pomerance 2011 Section 3, page 7, small moduli: the budget at H = (q-1)/2 is at least
1/2 for 5 ≤ q ≤ 80, a finite numerical check with log bounds, smallest slack 0.19 at q = 5.
Class MEDIUM. -/
theorem budget_small {q : ℕ} (hq5 : 5 ≤ q) (hq80 : q ≤ 80) :
    1 / 2 ≤ (1 / π ^ 2 * sqrt (q:ℝ) * log (q:ℝ) + 2 / π ^ 2 * sqrt (q:ℝ) * log (log (q:ℝ)) + 3 / 4 * sqrt (q:ℝ) -
          2 / π ^ 2 * sqrt (q:ℝ) * (log (((q - 1) / 2 : ℕ) : ℝ) + eulerMascheroniConstant + log 2 + 3 / (((q - 1) / 2 : ℕ) : ℝ))) := by
  apply LeanLab.HelfgottMajor.PVCotTail1122Aux.Small.budget_small_proof <;> assumption

/-- PROVED in S75, formerly LEAF: Pomerance 2011 Section 3, page 8, the entry of Lemma 4 into B_n for the cotangent tail:
by `PVTailAbel1122.dual_bound` with w(h) = cot(πh/q) sin(2πKh/q) and
sin(2πKh/q) = (e(Kh/q) - e(-Kh/q))/(2i), the shifts a ↦ a ± K turn the sum over a into the sum
over b of the tail norms. Class MEDIUM. -/
theorem even_tail_dual {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (H K : ℕ) :
    ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        χ⁻¹ h * ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ ≤
      1 / sqrt q * ∑ b : ZMod q, ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        (cot (π * h.val / q) : ℂ) * ZMod.stdAddChar (b * h)‖ := by
  apply LeanLab.HelfgottMajor.PVCotTail1122Aux.Dual.even_tail_dual_proof <;> assumption

/-- PROVED in S75, formerly LEAF: Pomerance 2011 Section 3, page 8, the choice of n and the final inequality, in the
cotangent form: for q ≥ 81 and H = ⌊√q log q⌋, 2(H+1) < q and
1/2 + 2q/(π²(H+1)) (log q + log(4/π) + π²/(12q²)) ≤ budget(H). Uses log H ≤ log √q + log log q,
H + 1 ≥ √q log q and γ < 0.5773. Class MEDIUM. -/
theorem close_large {q : ℕ} (hq : 81 ≤ q) :
    1 ≤ ⌊sqrt q * log q⌋₊ ∧ 2 * (⌊sqrt q * log q⌋₊ + 1) < q ∧
      1 / 2 + 2 * q / (π ^ 2 * (⌊sqrt q * log q⌋₊ + 1)) *
          (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2)) ≤
        (1 / π ^ 2 * sqrt (q:ℝ) * log (q:ℝ) + 2 / π ^ 2 * sqrt (q:ℝ) * log (log (q:ℝ)) + 3 / 4 * sqrt (q:ℝ) -
          2 / π ^ 2 * sqrt (q:ℝ) * (log (⌊sqrt q * log q⌋₊ : ℝ) + eulerMascheroniConstant + log 2 + 3 / (⌊sqrt q * log q⌋₊ : ℝ))) := by
  apply LeanLab.HelfgottMajor.PVCotTail1122Aux.Close.close_large_proof <;> assumption

/-- The tail bound for any H with 2(H+1) < q: the tail over 2√q is at most
2q/(π²(H+1)) (log q + log(4/π) + π²/(12q²)), Pomerance's bound for |B_n| in cotangent form.
PROVED from the LEAFs `even_tail_dual`, `PVTailAbel1122.abel_tail`,
`PVTailAbel1122.tail_cot_sum_zero` and `PVTailAbel1122.csc_sum_integral`. -/
theorem tail_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (H : ℕ) (hHq : 2 * (H + 1) < q) (K : ℕ) :
    ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        χ⁻¹ h * ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ /
        (2 * sqrt q) ≤
      2 * q / (π ^ 2 * (H + 1)) * (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2)) := by
  have hq1 : 1 < q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hs : 0 < sqrt (q : ℝ) := sqrt_pos.mpr hq0
  have hd := even_tail_dual χ hχ H K
  have hV := LeanLab.HelfgottMajor.PVTailAbel1122.tail_V_sum (q := q) H hHq
  have hC := LeanLab.HelfgottMajor.PVTailAbel1122.csc_sum hq1
  have hH1 : (1 : ℝ) ≤ (H : ℝ) + 1 := by have : (0:ℝ) ≤ H := Nat.cast_nonneg H; linarith
  have hy0 : 0 < π * ((H : ℝ) + 1) / q := by positivity
  have hy1 : π * ((H : ℝ) + 1) / q < π / 2 := by
    have : (2 : ℝ) * ((H : ℝ) + 1) < q := by exact_mod_cast hHq
    rw [div_lt_div_iff₀ hq0 two_pos]; nlinarith [pi_pos]
  obtain ⟨hcp, hcl⟩ := LeanLab.HelfgottMajor.PVEvenTrunc1122.cot_pos_le_inv hy0 hy1
  have hcl' : cot (π * ((H : ℝ) + 1) / q) ≤ q / (π * ((H : ℝ) + 1)) := by
    rw [one_div_div] at hcl; exact hcl
  set Lq := log q + log (4 / π) + π ^ 2 / (12 * q ^ 2)
  set C := ∑ a ∈ Icc 1 (q - 1), 1 / sin (π * a / q)
  have hC0 : 0 ≤ C := by
    refine sum_nonneg fun a ha => ?_
    rw [mem_Icc] at ha
    have : 0 < sin (π * a / q) := by
      apply sin_pos_of_pos_of_lt_pi
      · have : (1:ℝ) ≤ a := by exact_mod_cast ha.1
        positivity
      · have : (a : ℝ) < q := by exact_mod_cast (show a < q by omega)
        rw [div_lt_iff₀ hq0]; nlinarith [pi_pos]
    positivity
  set T := ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        χ⁻¹ h * ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖
  have h1 : T ≤ 1 / sqrt q * (2 * (q / (π * ((H : ℝ) + 1))) * (2 * q / π * Lq)) := by
    refine hd.trans (mul_le_mul_of_nonneg_left (hV.trans ?_) (by positivity))
    have : 2 * cot (π * ((H : ℝ) + 1) / q) * C ≤ 2 * (q / (π * ((H : ℝ) + 1))) * C :=
      mul_le_mul_of_nonneg_right (by linarith) hC0
    refine this.trans (mul_le_mul_of_nonneg_left hC.le (by positivity))
  rw [div_le_iff₀ (by positivity)]
  have hqs : (q : ℝ) = sqrt q * sqrt q := (mul_self_sqrt hq0.le).symm
  calc T ≤ 1 / sqrt q * (2 * (q / (π * ((H : ℝ) + 1))) * (2 * q / π * Lq)) := h1
    _ = 2 * q / (π ^ 2 * ((H : ℝ) + 1)) * Lq * (2 * sqrt q) := by
      field_simp
      rw [sq_sqrt hq0.le]

/-- Assembly: exactly the LEAF `PVEvenTrunc1122.cot_tail`. PROVED from the LEAFs above and
those of `PVTailAbel1122`. -/
theorem cot_tail {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) :
    ∃ H : ℕ, 1 ≤ H ∧ 2 * H < q ∧ ∀ K : ℕ,
      ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)), χ⁻¹ h *
          ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ /
          (2 * sqrt q) + 1 / 2 ≤
        1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q -
          2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H) := by
  have h5 := even_primitive_ge_five χ hχ hq heven
  by_cases hsmall : q ≤ 80
  · refine ⟨(q - 1) / 2, by omega, by omega, fun K => ?_⟩
    rw [tail_empty χ K, norm_zero, zero_div, zero_add]
    exact budget_small h5 hsmall
  · obtain ⟨hH1, hHq, hcl⟩ := close_large (q := q) (by omega)
    refine ⟨⌊sqrt q * log q⌋₊, hH1, by omega, fun K => ?_⟩
    have ht := tail_bound χ hχ ⌊sqrt q * log q⌋₊ hHq K
    linarith

example : type_of% @cot_tail = type_of% @LeanLab.HelfgottMajor.PVEvenTrunc1122.cot_tail := rfl

end LeanLab.HelfgottMajor.PVCotTail1122

#print axioms LeanLab.HelfgottMajor.PVCotTail1122.even_primitive_ge_five
#print axioms LeanLab.HelfgottMajor.PVCotTail1122.tail_empty
#print axioms LeanLab.HelfgottMajor.PVCotTail1122.budget_small
#print axioms LeanLab.HelfgottMajor.PVCotTail1122.even_tail_dual
#print axioms LeanLab.HelfgottMajor.PVCotTail1122.close_large
#print axioms LeanLab.HelfgottMajor.PVCotTail1122.tail_bound
#print axioms LeanLab.HelfgottMajor.PVCotTail1122.cot_tail
