/-
Route burst burst-20261122, session S72, BHP1997, LEAF `S64LowExcCharNP.leaf_perron_window`.

P0069 Baker Harman Pintz 1997, proof of Lemma 29, pages 43 and 44: "by [29] Lemma 3.19" the
window sum `Σ_{y ≤ m ≤ y+yz} b(m) χ(m)` equals the Perron integral at `Re s = 1/2`, height
`T = Y`, plus `O(Y^ε)`. The proof of Titchmarsh Lemma 3.19 for a finite Dirichlet polynomial
splits into
* `leaf_perron_sum_identity`: the integral of the finite sum is the sum of the per term
  Perron integrals `perronI ((y+yz)/m) (1/2) Y - perronI (y/m) (1/2) Y`; LEAF MEDIUM;
* `perron_term_bound`: PROVED here from the DERZ1997 port `Perron136`, Davenport chapter 17:
  `|H - perronI w c T| ≤ 2 w^c / (1 + T |log w|)` for the step `H`, including `w = 1`;
* `leaf_log_sum`: `Σ_{m ∈ J} (w/m)^(1/2) / (1 + Y |log(w/m)|) ≪ log Y ≪ Y^(1/200)` for
  `w ≍ Y`; LEAF MEDIUM;
* `leaf_coeff_divisor`: `|b(m)| ≤ C d(m)^B ≪ Y^(1/200)` on J by the divisor bound; LEAF EASY.
`leaf_perron_window_of_leaves` is PROVED from these, with exactly the statement of
`S64LowExcCharNP.leaf_perron_window`, checked by `leaf_perron_window_split_twin`.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.S64LowExcCharNonprincipal
import LeanLab.BHP1997.S72PerronElementary697
import LeanLab.DERZ1997.Perron136

namespace LeanLab.BHP1997.S72PerronWindow
open Classical Complex DecompC165b
open LeanLab.DERZ1997.Decomp1529b LeanLab.DERZ1997.Perron136
open scoped BigOperators
open MeasureTheory

/-- Davenport chapter 17, page 105, as in Titchmarsh Lemma 3.19: the truncated Perron
integral `perronI w c T = (1/2π) ∫_{-T}^{T} w^(c+it)/(c+it) dt` differs from the step
`H = [w > 1]`, with any value at `w = 1`, by at most `2 w^c / (1 + T |log w|)`.
PROVED from the DERZ1997 port. -/
theorem perron_term_bound {w c T : ℝ} (hw : 0 < w) (hc : 0 < c) (hT : 0 < T)
    (H : Prop) [Decidable H] (hH1 : 1 < w → H) (hH2 : w < 1 → ¬H) :
    ‖(if H then (1 : ℂ) else 0) - perronI w c T‖ ≤ 2 * (w ^ c / (1 + T * |Real.log w|)) := by
  have hwc : 0 < w ^ c := Real.rpow_pos_of_pos hw c
  have hd : 0 < 1 + T * |Real.log w| :=
    add_pos_of_pos_of_nonneg one_pos (mul_nonneg hT.le (abs_nonneg _))
  rcases lt_trichotomy w 1 with h | h | h
  · rw [if_neg (hH2 h), zero_sub, norm_neg]
    by_cases ha : T * |Real.log w| ≤ 1
    · calc ‖perronI w c T‖ ≤ w ^ c := perron_norm_small hw hc hT ha
        _ ≤ _ := by
          rw [mul_div_assoc', le_div_iff₀ hd]; nlinarith
    · push_neg at ha
      have hrem := perron_remainder_bound (c := c) (T := T) hw h.ne hc hT
      simp only [not_lt_of_gt h, if_false, sub_zero] at hrem
      have hp : 1 + T * |Real.log w| ≤ 2 * (Real.pi * T * |Real.log w|) := by
        nlinarith [Real.pi_gt_three]
      calc ‖perronI w c T‖ ≤ _ := hrem
        _ ≤ _ := by
          rw [mul_div_assoc', div_le_div_iff₀ (mul_pos (mul_pos Real.pi_pos hT) (abs_pos.2 (Real.log_ne_zero_of_pos_of_ne_one hw h.ne))) hd]
          nlinarith [mul_le_mul_of_nonneg_left hp hwc.le]
  · subst h
    have hP : ‖perronI 1 c T‖ ≤ 1 := by
      have := perron_norm_small (y := 1) (c := c) (T := T) one_pos hc hT (by simp)
      simpa using this
    have hH : ‖(if H then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
    calc _ ≤ ‖(if H then (1 : ℂ) else 0)‖ + ‖perronI 1 c T‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
      _ = _ := by simp
  · rw [if_pos (hH1 h), norm_sub_rev]
    have hl : 0 < Real.log w := Real.log_pos h
    rw [abs_of_pos hl] at hd ⊢
    by_cases ha : T * Real.log w ≤ 1
    · calc ‖perronI w c T - 1‖ ≤ w ^ c := perron_gt_one_small h hc hT ha
        _ ≤ _ := by
          rw [mul_div_assoc', le_div_iff₀ hd]; nlinarith
    · push_neg at ha
      have hrem := perron_remainder_bound (c := c) (T := T) hw h.ne' hc hT
      simp only [h, if_true, abs_of_pos hl] at hrem
      have hp : 1 + T * Real.log w ≤ 2 * (Real.pi * T * Real.log w) := by
        nlinarith [Real.pi_gt_three]
      calc ‖perronI w c T - 1‖ ≤ _ := hrem
        _ ≤ _ := by
          rw [mul_div_assoc', div_le_div_iff₀ (mul_pos (mul_pos Real.pi_pos hT) hl) hd]
          nlinarith [mul_le_mul_of_nonneg_left hp hwc.le]




/-- Page 43 to 44, the window as a difference of steps: for `m > 0` and `y ≤ w`,
`[y ≤ m ≤ w] = [w/m ≥ 1] - [y/m > 1]`. -/
theorem window_step {y w : ℝ} (hyw : y ≤ w) {m : ℝ} (hm : 0 < m) (a : ℂ) :
    (if y ≤ m ∧ m ≤ w then a else 0) =
      a * ((if 1 ≤ w / m then (1 : ℂ) else 0) - (if 1 < y / m then (1 : ℂ) else 0)) := by
  by_cases h1 : m ≤ w <;> by_cases h2 : m < y
  · have e1 : 1 ≤ w / m := (one_le_div hm).2 h1
    have e2 : 1 < y / m := (one_lt_div hm).2 h2
    simp [e1, e2, not_le.2 h2]
  · have e1 : 1 ≤ w / m := (one_le_div hm).2 h1
    have e2 : ¬ 1 < y / m := fun h => h2 ((one_lt_div hm).1 h)
    simp [e1, e2, not_lt.1 h2, h1]
  · exfalso; push_neg at h1; linarith
  · have e1 : ¬ 1 ≤ w / m := fun h => h1 ((one_le_div hm).1 h)
    have e2 : ¬ 1 < y / m := fun h => h2 ((one_lt_div hm).1 h)
    simp [e1, e2, h1]

/-- PROVED from the LEAFs: exactly the statement of `S64LowExcCharNP.leaf_perron_window`,
P0069 pages 43 to 44, the truncated Perron formula of [29] Lemma 3.19 with error
`O(Y^(1/100))`. -/
theorem leaf_perron_window_of_leaves (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q, ∀ y : ℝ, x ^ (11 / 20 + ε) / 2 ≤ y →
          y ≤ 3 * x ^ (11 / 20 + ε) →
          ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m : ℂ) * χ (m : ZMod q)) -
            ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
              ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                  ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                    (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
            K * (x ^ (11 / 20 + ε)) ^ (1 / 100 : ℝ) := by
  obtain ⟨K2, hK2, C2, h2⟩ := leaf_log_sum hε
  obtain ⟨K3, hK3, C3, h3⟩ := leaf_coeff_divisor b hε hb
  refine ⟨4 * K3 * K2, by positivity,
    max (max C2 C3) (max ((6 ^ 16 : ℝ) ^ ((11 / 20 + ε)⁻¹)) 1),
    fun x hx q hq hqQ z hz1 hz2 χ y hy1 hy2 => ?_⟩
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx3 : C3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx6 : (6 ^ 16 : ℝ) ^ ((11 / 20 + ε)⁻¹) ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have ha : 0 < 11 / 20 + ε := by linarith
  have hY6 : (6 : ℝ) ^ 16 ≤ x ^ (11 / 20 + ε) := by
    have h := Real.rpow_le_rpow (by positivity) hx6 ha.le
    rwa [Real.rpow_inv_rpow (by positivity) ha.ne'] at h
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) hY6
  have hY1 : 1 ≤ Y := le_trans (by norm_num) hY6
  have hQ := S64LowExcCharNP.sieveQ_le_sixteenth hY1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqQr : (q : ℝ) ≤ sieveQ ε x := by exact_mod_cast hqQ
  have hz0 : 0 ≤ z := le_trans (div_nonneg (by positivity) (by positivity)) hz1
  have h16 : Y ^ (1 / 16 : ℝ) * Y ^ (1 / 16 : ℝ) = Y ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_add hY]; norm_num
  have h6qQ : 6 * q * (sieveQ ε x : ℝ) ≤ Y := by
    have hQ0 : (0 : ℝ) ≤ sieveQ ε x := by positivity
    calc 6 * q * (sieveQ ε x : ℝ) ≤ 6 * (Y ^ (1 / 16 : ℝ) * Y ^ (1 / 16 : ℝ)) := by
          have := mul_le_mul (hqQr.trans hQ) hQ hQ0 (Real.rpow_nonneg hY.le _)
          nlinarith
      _ = 6 * Y ^ (1 / 8 : ℝ) := by rw [h16]
      _ ≤ _ := S64LowExcCharNP.six_mul_eighth_le hY6
  have hz1' : z ≤ 1 := hz2.trans ((div_le_one hY).2 h6qQ)
  have hy0 : 0 < y := by linarith
  have hw1 : 0 < y + y * z := by nlinarith
  have hw1a : Y / 2 ≤ y + y * z := by nlinarith
  have hw1b : y + y * z ≤ 6 * Y := by nlinarith
  have hyw : y ≤ y + y * z := by nlinarith
  set J := rightInterval ε x with hJdef
  have hJ : ∀ m ∈ J, 1 ≤ m := fun m hm => rightInterval_pos hm
  set a : ℕ → ℂ := fun m => (b x m : ℂ) * χ (m : ZMod q) with hadef
  -- the window sum as steps
  have hW : (∑ m ∈ J.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), a m) =
      ∑ m ∈ J, a m * ((if 1 ≤ (y + y * z) / m then (1 : ℂ) else 0) -
        (if 1 < y / m then (1 : ℂ) else 0)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hJ m hm
    exact window_step hyw hm0 (a m)
  have hP := leaf_perron_sum_identity J hJ a Y (y + y * z) y hw1 hy0
  have hS : ∀ m ∈ J, ‖a m‖ ≤ K3 * Y ^ (1 / 200 : ℝ) := by
    intro m hm
    simp only [hadef, norm_mul]
    have hχ : ‖χ (m : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hbm : ‖(b x m : ℂ)‖ = |b x m| := Complex.norm_real _
    rw [hbm]
    calc |b x m| * ‖χ (m : ZMod q)‖ ≤ |b x m| * 1 :=
          mul_le_mul_of_nonneg_left hχ (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact h3 x hx3 m hm
  set f : ℝ → ℕ → ℝ := fun w m => (w / m) ^ (1 / 2 : ℝ) / (1 + Y * |Real.log (w / m)|)
    with hfdef
  have hterm : ∀ (w : ℝ), 0 < w → ∀ m ∈ J, ∀ (H : Prop) [Decidable H],
      (1 < w / m → H) → (w / m < 1 → ¬H) →
      ‖(if H then (1 : ℂ) else 0) - perronI (w / m) (1 / 2) Y‖ ≤ 2 * f w m := by
    intro w hw m hm H _ hH1 hH2
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hJ m hm
    exact perron_term_bound (div_pos hw hm0) (by norm_num) hY H hH1 hH2
  have hsum1 := h2 x hx2 (y + y * z) hw1a hw1b
  have hsum2 := h2 x hx2 y (by linarith) (by linarith)
  have hR0 : 0 ≤ Y ^ (1 / 200 : ℝ) := Real.rpow_nonneg hY.le _
  have hR2 : Y ^ (1 / 200 : ℝ) * Y ^ (1 / 200 : ℝ) = Y ^ (1 / 100 : ℝ) := by
    rw [← Real.rpow_add hY]; norm_num
  rw [hW, hP, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ m ∈ J, ‖a m * (((if 1 ≤ (y + y * z) / m then (1 : ℂ) else 0) -
          (if 1 < y / m then (1 : ℂ) else 0)) -
          (perronI ((y + y * z) / m) (1 / 2) Y - perronI (y / m) (1 / 2) Y))‖ := by
        refine le_of_eq_of_le ?_ (norm_sum_le _ _)
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        ring
    _ ≤ ∑ m ∈ J, (K3 * Y ^ (1 / 200 : ℝ)) *
          (2 * f (y + y * z) m + 2 * f y m) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hJ m hm
        rw [norm_mul]
        have e1 := hterm (y + y * z) hw1 m hm (1 ≤ (y + y * z) / m) (fun h => h.le)
          (fun h h' => absurd h' (not_le.2 h))
        have e2 := hterm y hy0 m hm (1 < y / m) id (fun h h' => absurd h' (not_lt.2 h.le))
        have hsplit : ‖((if 1 ≤ (y + y * z) / m then (1 : ℂ) else 0) -
            (if 1 < y / m then (1 : ℂ) else 0)) -
            (perronI ((y + y * z) / m) (1 / 2) Y - perronI (y / m) (1 / 2) Y)‖ ≤
            2 * f (y + y * z) m + 2 * f y m := by
          calc _ = ‖((if 1 ≤ (y + y * z) / m then (1 : ℂ) else 0) -
                perronI ((y + y * z) / m) (1 / 2) Y) -
              ((if 1 < y / m then (1 : ℂ) else 0) - perronI (y / m) (1 / 2) Y)‖ := by
                congr 1; ring
            _ ≤ _ := norm_sub_le _ _
            _ ≤ _ := add_le_add e1 e2
        exact mul_le_mul (hS m hm) hsplit (norm_nonneg _) (by positivity)
    _ = (K3 * Y ^ (1 / 200 : ℝ)) * 2 * ((∑ m ∈ J, f (y + y * z) m) + ∑ m ∈ J, f y m) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        ring
    _ ≤ (K3 * Y ^ (1 / 200 : ℝ)) * 2 * (K2 * Y ^ (1 / 200 : ℝ) + K2 * Y ^ (1 / 200 : ℝ)) := by
        gcongr
    _ = 4 * K3 * K2 * (Y ^ (1 / 200 : ℝ) * Y ^ (1 / 200 : ℝ)) := by ring
    _ = _ := by rw [hR2]


end LeanLab.BHP1997.S72PerronWindow

#print axioms LeanLab.BHP1997.S72PerronWindow.perron_term_bound
#print axioms LeanLab.BHP1997.S72PerronWindow.window_step
#print axioms LeanLab.BHP1997.S72PerronWindow.rightInterval_pos
#print axioms LeanLab.BHP1997.S72PerronWindow.leaf_perron_window_of_leaves

namespace LeanLab.BHP1997.S72PerronWindow

/-- Twin check: the assembly has exactly the type of the open LEAF. -/
theorem leaf_perron_window_split_twin :
    type_of% @S64LowExcCharNP.leaf_perron_window :=
  @leaf_perron_window_of_leaves

end LeanLab.BHP1997.S72PerronWindow
