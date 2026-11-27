/-
P0069 pages 43 and 44. Elementary finite Perron steps.
The three declarations moved here with their sealed statements unchanged.
Only the Perron kernel definition is needed for the finite sum identity.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.S64PerronBase
import LeanLab.DERZ1997.Kernel136
import LeanLab.PerelliPintz1992.DivisorBound
import LeanLab.BHP1997.Spacing132

namespace LeanLab.BHP1997.S72PerronWindow
open Classical Complex DecompC165b
open LeanLab.DERZ1997.Decomp1529b
open scoped BigOperators
open MeasureTheory

/-- LEAF: page 43 to 44, proof of Lemma 29 via [29] Lemma 3.19, the step that writes the
Perron integral of the Dirichlet polynomial `G(s) = Σ_{m ∈ J} a(m) m^(-s)` as the sum over
m of the per term Perron integrals of `((y+yz)/m)^s / s` and `(y/m)^s / s`: linearity of
the integral over the finite sum and `w^s / m^s = (w/m)^s` for positive reals. Class MEDIUM.
CITED [29] Titchmarsh Lemma 3.19, proof. -/
theorem leaf_perron_sum_identity (J : Finset ℕ) (hJ : ∀ m ∈ J, 1 ≤ m) (a : ℕ → ℂ)
    (T w1 w2 : ℝ) (hw1 : 0 < w1) (hw2 : 0 < w2) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t in (-T)..T,
          (∑ m ∈ J, a m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
            ((w1 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
              (w2 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I) =
      ∑ m ∈ J, a m * (perronI (w1 / m) (1 / 2) T - perronI (w2 / m) (1 / 2) T) := by
  let s : ℝ → ℂ := fun t => (1 / 2 : ℂ) + (t : ℂ) * I
  have hs : Continuous s := by unfold s; fun_prop
  have hs0 : ∀ t, s t ≠ 0 := by
    intro t h
    have hh := congrArg Complex.re h
    simp [s] at hh
  have hc (w : ℝ) (hw : 0 < w) :
      Continuous (fun t : ℝ => (w : ℂ) ^ s t / s t) :=
    ((continuous_const_cpow' (Complex.ofReal_ne_zero.mpr hw.ne')).comp hs).div hs hs0
  have hInt (w : ℝ) (hw : 0 < w) :
      IntervalIntegrable (fun t : ℝ => (w : ℂ) ^ s t / s t) volume (-T) T :=
    (hc w hw).intervalIntegrable _ _
  have hi (m : ℕ) (hm : m ∈ J) :
      IntervalIntegrable (fun t : ℝ => a m *
        (((w1 / m : ℝ) : ℂ) ^ s t / s t - ((w2 / m : ℝ) : ℂ) ^ s t / s t)) volume (-T) T := by
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast hJ m hm
    exact ((hInt (w1 / m) (div_pos hw1 hm0)).sub
      (hInt (w2 / m) (div_pos hw2 hm0))).const_mul _
  have heq (t : ℝ) :
      (∑ m ∈ J, a m / (m : ℂ) ^ s t) *
          ((w1 : ℂ) ^ s t - (w2 : ℂ) ^ s t) / s t =
        ∑ m ∈ J, a m *
          (((w1 / m : ℝ) : ℂ) ^ s t / s t - ((w2 / m : ℝ) : ℂ) ^ s t / s t) := by
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    rw [Complex.ofReal_div, Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg hw1.le hm0,
      Complex.div_cpow_ofReal_nonneg hw2.le hm0]
    norm_cast
    ring
  change ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t in (-T)..T, (∑ m ∈ J, a m / (m : ℂ) ^ s t) *
        ((w1 : ℂ) ^ s t - (w2 : ℂ) ^ s t) / s t) = _
  simp_rw [heq]
  rw [intervalIntegral.integral_finsetSum hi, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hJ m hm
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hInt (w1 / m) (div_pos hw1 hm0))
      (hInt (w2 / m) (div_pos hw2 hm0))]
  unfold perronI
  dsimp only [s]
  push_cast
  ring


/-- LEAF: page 43 to 44, proof of Lemma 29 via [29] Lemma 3.19, the summed remainder:
for `w ≍ Y`, `Σ_{m ∈ J} (w/m)^(1/2) min(1, 1/(Y |log(w/m)|)) ≪ log Y`, since
`|log(w/m)| ≫ |w - m|/Y` on `J ⊆ (Y, 2Y]`, and `log Y ≪ Y^(1/200)`. Class MEDIUM.
CITED [29] Titchmarsh Lemma 3.19. -/
theorem leaf_log_sum {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ w : ℝ, x ^ (11 / 20 + ε) / 2 ≤ w →
      w ≤ 6 * x ^ (11 / 20 + ε) →
        ∑ m ∈ rightInterval ε x, (w / m) ^ (1 / 2 : ℝ) /
            (1 + x ^ (11 / 20 + ε) * |Real.log (w / m)|) ≤
          K * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) := by
  refine ⟨180 * (Real.log 8 + 200), by positivity, 1, fun x hx w hw1 hw2 => ?_⟩
  set Y := x ^ (11 / 20 + ε) with hY
  have hY1 : 1 ≤ Y := Real.one_le_rpow hx (by linarith)
  have hY0 : 0 < Y := by linarith
  have hw : 0 < w := by linarith
  have hmJ (m : ℕ) (hm : m ∈ rightInterval ε x) : Y < (m : ℝ) ∧ (m : ℝ) ≤ 2 * Y := by
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ioc.mp hm
    have h1 : (⌊Y⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast hm1
    have h2 : (m : ℝ) ≤ ⌊2 * Y⌋₊ := by exact_mod_cast hm2
    exact ⟨by linarith [Nat.lt_floor_add_one Y],
      h2.trans (Nat.floor_le (by positivity))⟩
  have hpoint (m : ℕ) (hm : m ∈ rightInterval ε x) :
      (w / m) ^ (1 / 2 : ℝ) / (1 + Y * |Real.log (w / m)|) ≤
        18 * (1 / (1 + |(m : ℝ) - w|)) := by
    obtain ⟨hmY, hm2Y⟩ := hmJ m hm
    have hm0 : 0 < (m : ℝ) := by linarith
    have hr0 : 0 < w / m := div_pos hw hm0
    have hr6 : w / m ≤ 6 := (div_le_iff₀ hm0).mpr (by linarith)
    have hroot : (w / m) ^ (1 / 2 : ℝ) ≤ 3 := by
      rw [← Real.sqrt_eq_rpow]
      exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith⟩
    have hdist : |(m : ℝ) - w| ≤ 6 * Y * |Real.log (w / m)| := by
      rcases le_total (m : ℝ) w with hmw | hwm
      · have hlog : 0 ≤ Real.log (w / m) := Real.log_nonneg ((one_le_div hm0).mpr hmw)
        have h := Real.one_sub_inv_le_log_of_pos hr0
        rw [inv_div] at h
        have hh := mul_le_mul_of_nonneg_left h hw.le
        have hid : w * (1 - (m : ℝ) / w) = w - m := by field_simp
        rw [hid] at hh
        rw [abs_of_nonpos (by linarith), abs_of_nonneg hlog]
        nlinarith [mul_le_mul_of_nonneg_right hw2 hlog]
      · have hlog : Real.log (w / m) ≤ 0 :=
          Real.log_nonpos hr0.le ((div_le_one hm0).mpr hwm)
        have h := Real.one_sub_inv_le_log_of_pos (div_pos hm0 hw)
        rw [inv_div] at h
        have hlogeq : Real.log ((m : ℝ) / w) = -Real.log (w / m) := by
          rw [Real.log_div hm0.ne' hw.ne', Real.log_div hw.ne' hm0.ne']; ring
        rw [hlogeq] at h
        have hh := mul_le_mul_of_nonneg_left h hm0.le
        have hid : (m : ℝ) * (1 - w / m) = m - w := by field_simp
        rw [hid] at hh
        rw [abs_of_nonneg (by linarith), abs_of_nonpos hlog]
        nlinarith [mul_le_mul_of_nonneg_right (show (m : ℝ) ≤ 6 * Y by linarith)
          (neg_nonneg.mpr hlog)]
    have hd1 : 0 < 1 + Y * |Real.log (w / m)| := by positivity
    have hd2 : 0 < 1 + |(m : ℝ) - w| := by positivity
    rw [mul_one_div, div_le_div_iff₀ hd1 hd2]
    nlinarith [mul_le_mul_of_nonneg_right hroot hd2.le]
  let S : Finset ℝ := (rightInterval ε x).image (fun m : ℕ => (m : ℝ))
  have hspace : ∀ t ∈ S, ∀ v ∈ S, t ≠ v → 1 ≤ |t - v| := by
    intro t ht v hv hne
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
    have hmn : m ≠ n := by intro h; subst n; exact hne rfl
    rcases lt_or_gt_of_ne hmn with h | h
    · have hmnR : (m : ℝ) ≤ n := by exact_mod_cast h.le
      rw [abs_of_nonpos (sub_nonpos.mpr hmnR)]
      have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
      linarith
    · have hnmR : (n : ℝ) ≤ m := by exact_mod_cast h.le
      rw [abs_of_nonneg (sub_nonneg.mpr hnmR)]
      have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
      linarith
  have hS : ∀ t ∈ S, |t| ≤ 3 * Y := by
    intro t ht
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ht
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    linarith [(hmJ m hm).2]
  have hk := Spacing132.kernel_le_ten_log S (x := 8 * Y) (T := 3 * Y) (u := w)
    (by linarith) (by positivity) (by linarith) hspace hS
    (by rw [abs_of_pos hw]; linarith)
  have hsum : (∑ m ∈ rightInterval ε x, 1 / (1 + |(m : ℝ) - w|)) =
      ∑ t ∈ S, 1 / (1 + |t - w|) := by
    rw [Finset.sum_image]
    intro m hm n hn h
    exact Nat.cast_injective h
  have hlog : Real.log (8 * Y) ≤ (Real.log 8 + 200) * Y ^ (1 / 200 : ℝ) := by
    rw [Real.log_mul (by norm_num) hY0.ne']
    have hL := Real.log_le_rpow_div hY0.le (by norm_num : (0 : ℝ) < 1 / 200)
    have hp : 1 ≤ Y ^ (1 / 200 : ℝ) := Real.one_le_rpow hY1 (by norm_num)
    have h8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hp h8]
  calc _ ≤ ∑ m ∈ rightInterval ε x, 18 * (1 / (1 + |(m : ℝ) - w|)) :=
      Finset.sum_le_sum hpoint
    _ = 18 * ∑ t ∈ S, 1 / (1 + |t - w|) := by rw [← Finset.mul_sum, hsum]
    _ ≤ 180 * Real.log (8 * Y) := by linarith
    _ ≤ 180 * ((Real.log 8 + 200) * Y ^ (1 / 200 : ℝ)) := by linarith
    _ = _ := by ring


/-- LEAF: page 11, display 3.1, `|b(m)| ≪ d(m)^B`, with the divisor bound `d(m) ≪ m^δ`,
gives `|b(m)| ≪ Y^(1/200)` on `J ⊆ (Y, 2Y]`, as used on page 44 for the error `O(Y^ε)`.
Class EASY. CITED the divisor bound, lab port `HeathBrown1985.card_divisors_le_rpow`. -/
theorem leaf_coeff_divisor (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m ∈ rightInterval ε x,
      |b x m| ≤ K * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) := by
  obtain ⟨Cb, hCb⟩ := hb
  by_cases hB : B ≤ 0
  · refine ⟨|Cb|, abs_nonneg _, 1, fun x hx m hm => ?_⟩
    have hm1 : 1 ≤ m := by
      have := (Finset.mem_Ioc.mp hm).1
      omega
    have hd1 : (1 : ℝ) ≤ m.divisors.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd m, by omega⟩⟩
    have hdB : (m.divisors.card : ℝ) ^ B ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hd1 hB
    have hY1 : 1 ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx (by linarith)
    have hYp : 1 ≤ (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) :=
      Real.one_le_rpow hY1 (by norm_num)
    calc |b x m| ≤ Cb * (m.divisors.card : ℝ) ^ B := hCb x m
      _ ≤ |Cb| * (m.divisors.card : ℝ) ^ B :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |Cb| * 1 := mul_le_mul_of_nonneg_left hdB (abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hYp (abs_nonneg _)
  · have hBpos : 0 < B := lt_of_not_ge hB
    obtain ⟨Cd, hCd, hdiv⟩ := LeanLab.PerelliPintz1992.Section6.divisors_card_le_rpow
      (1 / (200 * B)) (by positivity)
    refine ⟨|Cb| * Cd ^ B * (2 : ℝ) ^ (1 / 200 : ℝ), by positivity,
      1, fun x hx m hm => ?_⟩
    have hmJ := Finset.mem_Ioc.mp hm
    have hm1 : 1 ≤ m := by omega
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm1
    have hx0 : 0 < x := by linarith
    have hY0 : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
    have hmY : (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
      (by exact_mod_cast hmJ.2 : (m : ℝ) ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊).trans
        (Nat.floor_le (by positivity))
    have hd := Real.rpow_le_rpow (by positivity) (hdiv m (by omega)) hBpos.le
    have hexp : 1 / (200 * B) * B = (1 / 200 : ℝ) := by field_simp [hBpos.ne']
    rw [Real.mul_rpow hCd.le (by positivity), ← Real.rpow_mul hm0.le, hexp] at hd
    have hmP := Real.rpow_le_rpow hm0.le hmY (show (0 : ℝ) ≤ 1 / 200 by norm_num)
    rw [Real.mul_rpow (by norm_num) hY0.le] at hmP
    calc |b x m| ≤ Cb * (m.divisors.card : ℝ) ^ B := hCb x m
      _ ≤ |Cb| * (m.divisors.card : ℝ) ^ B :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |Cb| * (Cd ^ B * (m : ℝ) ^ (1 / 200 : ℝ)) :=
        mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ ≤ |Cb| * (Cd ^ B * ((2 : ℝ) ^ (1 / 200 : ℝ) *
          (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ))) := by gcongr
      _ = _ := by ring

theorem rightInterval_pos {ε x : ℝ} {m : ℕ} (hm : m ∈ rightInterval ε x) : 1 ≤ m := by
  unfold rightInterval at hm
  rw [Finset.mem_Ioc] at hm
  omega


end LeanLab.BHP1997.S72PerronWindow
