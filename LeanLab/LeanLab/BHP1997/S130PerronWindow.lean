/-
Burst burst-20261122, CLOUD S130, BHP1997: split of the LEAF
`S64LowExcCharNP.leaf_perron_window` of branch claude/BHP1997-leaf_mellin_mean_value, by S64.
P0069 Baker Harman Pintz 1997, proof of Lemma 29 on pages 43 to 44, the case of a non principal
character: "by [29] Lemma 3.19" the window sum `Σ_{y ≤ m ≤ y+yz} b(m) χ(m)` equals the Perron
integral at height `Y` plus `O(Y^ε)`.

The proof of Titchmarsh [29] Lemma 3.19 for a finite Dirichlet polynomial has three parts:
* `perron_window_identity`, PROVED: the integral is `Σ_m a_m (I(w/m) - I(y/m))`, `I` the
  truncated Perron kernel `perronI` of the lab at abscissa `1/2`;
* `leaf_perron_kernel_half`, LEAF EASY: `|I(u) - δ(u)| ≤ u^(1/2) min(1, 1/(T |log u|))`,
  already PROVED in the lab as `DERZ1997.Perron136.perron_remainder_bound` and companions, kept as
  a LEAF only for the import cone;
* `leaf_perron_error_count`, PROVED: the kernel errors over J sum to `≤ 504 log Y`.
`leaf_perron_window_of_s130` is PROVED from these, so from the one EASY LEAF, with exactly the statement of
`S64LowExcCharNP.leaf_perron_window`, restated verbatim since that file is not on main yet.

No new definition. AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.SieveConditionsC165
import LeanLab.DERZ1997.Kernel136
import LeanLab.BHP1997.Decomp312c
import LeanLab.BHP1997.PerronHalfSmall

namespace LeanLab.BHP1997.S130PerronWindow
open Classical Complex DecompC165b
open LeanLab.DERZ1997.Decomp1529b
open LeanLab.BHP1997.PerronHalfSmall
open scoped BigOperators

/-- Page 43 to 44, the change `(y+yz)^s m^(-s) = ((y+yz)/m)^s` inside the Perron integral, for
positive reals, PROVED. -/
theorem ofReal_div_cpow' {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (s : ℂ) :
    ((p / q : ℝ) : ℂ) ^ s = (p : ℂ) ^ s / (q : ℂ) ^ s := by
  rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hp (inv_nonneg.mpr hq.le),
    Complex.ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hq.le]; exact Real.pi_pos.ne),
    div_eq_mul_inv]

/-- Page 43 to 44, proof of Lemma 29, the Perron integral of the window, termwise, PROVED: the
integral `(1/2π) ∫_{-T}^{T} G(1/2+it) ((y+yz)^s - y^s)/s dt` of a finite Dirichlet polynomial
`G(s) = Σ a_m m^(-s)` is `Σ a_m (I((y+yz)/m) - I(y/m))`, with `I(u) = perronI u (1/2) T` the
truncated Perron kernel of Davenport chapter 17 at abscissa `1/2`. Titchmarsh [29] Lemma 3.19,
first step. -/
theorem perron_window_identity (S : Finset ℕ) (hS : ∀ m ∈ S, 1 ≤ m) (a : ℕ → ℂ)
    {y w : ℝ} (hy : 0 < y) (hw : 0 < w) (T : ℝ) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t in (-T)..T, (∑ m ∈ S, a m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
          ((w : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) /
            ((1 / 2 : ℂ) + (t : ℂ) * I) =
      ∑ m ∈ S, a m * (perronI (w / m) (1 / 2) T - perronI (y / m) (1 / 2) T) := by
  have hs0 : ∀ t : ℝ, (1 / 2 : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
  have hcont : ∀ u : ℝ, 0 < u → Continuous fun t : ℝ =>
      (u : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) / ((1 / 2 : ℂ) + (t : ℂ) * I) := by
    intro u hu
    refine Continuous.div ?_ (by fun_prop) hs0
    exact continuous_const.cpow (by fun_prop) (fun _ => Or.inl (by simpa using hu))
  have hpt : ∀ t : ℝ, (∑ m ∈ S, a m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
      (((w : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) /
        ((1 / 2 : ℂ) + (t : ℂ) * I)) =
      ∑ m ∈ S, a m * ((((w / m : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) /
          ((1 / 2 : ℂ) + (t : ℂ) * I)) -
        (((y / m : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) / ((1 / 2 : ℂ) + (t : ℂ) * I))) := by
    intro t
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hS m hm
    rw [ofReal_div_cpow' hw.le hm0, ofReal_div_cpow' hy.le hm0, Complex.ofReal_natCast]
    have hmc : (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h (by exact_mod_cast hm0.ne')
    field_simp
  simp_rw [mul_div_assoc, hpt]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hS m hm
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      ((hcont _ (div_pos hw hm0)).intervalIntegrable _ _)
      ((hcont _ (div_pos hy hm0)).intervalIntegrable _ _)]
    simp only [perronI]
    push_cast
    ring
  · intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hS m hm
    exact (continuous_const.mul ((hcont _ (div_pos hw hm0)).sub
      (hcont _ (div_pos hy hm0)))).intervalIntegrable _ _

/-- LEAF: page 43 to 44, proof of Lemma 29, the step "by [29] Lemma 3.19", the truncated Perron
kernel at abscissa `1/2`, class EASY. Davenport chapter 17 page 105 and Titchmarsh [29]
Lemma 3.19: for `u > 0`, `u ≠ 1`, `|I(u,T) - δ(u)| ≤ u^(1/2) min(1, 1/(T |log u|))`, and
`|I(1,T)| ≤ 1`. The lab has this PROVED for every abscissa `c > 0` as
`LeanLab.DERZ1997.Perron136.perron_remainder_bound`, `perron_norm_small` and
`perron_gt_one_small`; it is left as a LEAF here only because that file imports
`LeanLab.Routes.Decomp1551a`, whose import closure is not built in the BHP1997 cone. Closing it
is an import plus a case split on `T |log u| ≤ 1`. -/
theorem leaf_perron_kernel_half (u : ℝ) (hu : 0 < u) (T : ℝ) (hT : 1 ≤ T) :
    ‖perronI u (1 / 2) T - (if 1 < u then 1 else 0)‖ ≤
      if u = 1 then 1 else u ^ (1 / 2 : ℝ) * min 1 (1 / (T * |Real.log u|)) := by
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  by_cases hu1 : u = 1
  · subst u
    have hnorm := perron_norm_small (y := (1 : ℝ)) (c := (1 / 2 : ℝ)) (T := T)
      (by norm_num) (by norm_num) hT0 (by simp)
    simpa using hnorm
  · by_cases hsmall : T * |Real.log u| ≤ 1
    · by_cases hu12 : 1 < u
      · have hlogpos : 0 < Real.log u := Real.log_pos hu12
        have hDpos : 0 < T * |Real.log u| := mul_pos hT0 (abs_pos.mpr hlogpos)
        have hmin : min 1 (1 / (T * |Real.log u|)) = 1 := by
          apply min_eq_left
          exact (le_div_iff₀ hDpos).2 (by simpa using hsmall)
        have hgt := perron_gt_one_small (y := u) (c := (1 / 2 : ℝ)) (T := T)
          hu12 (by norm_num) hT0 (by simpa [abs_of_pos hlogpos] using hsmall)
        simpa [hu1, hu12, hmin] using hgt
      · have hlogne : Real.log u ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hu hu1
        have hDpos : 0 < T * |Real.log u| := mul_pos hT0 (abs_pos.mpr hlogne)
        have hmin : min 1 (1 / (T * |Real.log u|)) = 1 := by
          apply min_eq_left
          exact (le_div_iff₀ hDpos).2 (by simpa using hsmall)
        have hnorm := perron_norm_small (y := u) (c := (1 / 2 : ℝ)) (T := T)
          hu (by norm_num) hT0 hsmall
        simpa [hu1, hu12, hmin] using hnorm
    · have hlogne : Real.log u ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hu hu1
      have hDpos : 0 < T * |Real.log u| := mul_pos hT0 (abs_pos.mpr hlogne)
      have hrem := LeanLab.BHP1997.Decomp312c.perron_remainder_bound490
        (y := u) (c := (1 / 2 : ℝ)) (T := T) hu hu1 (by norm_num) hT0
      have hpi : 1 ≤ Real.pi := by
        have := Real.pi_gt_d9
        linarith
      have hpiD : T * |Real.log u| ≤ Real.pi * T * |Real.log u| := by
        calc
          T * |Real.log u| ≤ Real.pi * (T * |Real.log u|) :=
            mul_le_mul_of_nonneg_right hpi (le_of_lt hDpos)
          _ = Real.pi * T * |Real.log u| := by ring
      have hinv : 1 / (Real.pi * T * |Real.log u|) ≤ 1 / (T * |Real.log u|) :=
        one_div_le_one_div_of_le (by positivity) hpiD
      have hfactor : u ^ (1 / 2 : ℝ) / (Real.pi * T * |Real.log u|) ≤
          u ^ (1 / 2 : ℝ) * (1 / (T * |Real.log u|)) :=
        mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hu.le _)
      have hmin : min 1 (1 / (T * |Real.log u|)) = 1 / (T * |Real.log u|) := by
        apply min_eq_right
        exact (div_le_one hDpos).2 hpiD
      rw [show min 1 (1 / (T * |Real.log u|)) = 1 / (T * |Real.log u|) from hmin]
      simpa [hu1, perronI] using hrem.trans hfactor

/-- Page 43 to 44, Lemma 3.19 error sum, the harmonic sum in real form, from Mathlib
`harmonic_le_one_add_log`. PROVED. -/
theorem harmonic_real_le (N : ℕ) :
    ∑ j ∈ Finset.range N, (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add,
    Nat.cast_one] at h
  simpa [one_div] using h

/-- Page 43 to 44, Lemma 3.19 error sum, reindexing along a map injective on the index set into
`range N`. PROVED. -/
theorem sum_comp_le_range {S : Finset ℕ} {g : ℕ → ℕ} {N : ℕ} (φ : ℕ → ℝ)
    (hφ : ∀ j, 0 ≤ φ j) (hinj : Set.InjOn g S) (hg : ∀ m ∈ S, g m < N) :
    ∑ m ∈ S, φ (g m) ≤ ∑ j ∈ Finset.range N, φ j := by
  rw [← Finset.sum_image (f := φ) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨m, hm, rfl⟩ := hj
    exact Finset.mem_range.mpr (hg m hm)
  · intro j _ _; exact hφ j

/-- Page 43 to 44, Lemma 3.19 error sum, `|log (w/m)| ≥ |w - m| / M` when `0 < w, m ≤ M`.
PROVED. -/
theorem abs_log_div_ge {w m M : ℝ} (hw : 0 < w) (hm : 0 < m) (hwM : w ≤ M) (hmM : m ≤ M) :
    |w - m| / M ≤ |Real.log (w / m)| := by
  have hM : 0 < M := lt_of_lt_of_le hw hwM
  rcases le_total m w with h | h
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hw hm)
    rw [inv_div] at h1
    have h2 : (w - m) / M ≤ 1 - m / w := by
      rw [show 1 - m / w = (w - m) / w by field_simp]
      exact div_le_div_of_nonneg_left (by linarith) hw hwM
    rw [abs_of_nonneg (by linarith : 0 ≤ w - m)]
    exact h2.trans (h1.trans (le_abs_self _))
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hm hw)
    rw [inv_div] at h1
    have h2 : (m - w) / M ≤ 1 - w / m := by
      rw [show 1 - w / m = (m - w) / m by field_simp]
      exact div_le_div_of_nonneg_left (by linarith) hm hmM
    have h3 : Real.log (m / w) = -Real.log (w / m) := by
      rw [← Real.log_inv, inv_div]
    rw [abs_of_nonpos (by linarith : w - m ≤ 0), neg_sub]
    calc (m - w) / M ≤ Real.log (m / w) := h2.trans h1
      _ = -Real.log (w / m) := h3
      _ ≤ |Real.log (w / m)| := neg_le_abs _

/-- Page 43 to 44, Lemma 3.19 error sum, one term: with `j(m)` the distance from `m` to `⌊w⌋`,
minus one on the right, the kernel error at `w/m` is at most `36/(j(m)+1)`. PROVED. -/
theorem term_le {Y w : ℝ} (hY : 2 ≤ Y) (hw1 : Y / 2 ≤ w) (hw2 : w ≤ 6 * Y) {m : ℕ}
    (hm1 : Y < m) (hm2 : (m : ℝ) ≤ 2 * Y) :
    (if w / m = 1 then 1 else (w / m) ^ (1 / 2 : ℝ) * min 1 (1 / (Y * |Real.log (w / m)|))) ≤
      36 / ((if m ≤ ⌊w⌋₊ then ⌊w⌋₊ - m else m - ⌊w⌋₊ - 1 : ℕ) + 1 : ℝ) := by
  set n0 := ⌊w⌋₊ with hn0
  have hw0 : 0 < w := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  set j : ℕ := if m ≤ n0 then n0 - m else m - n0 - 1 with hj
  have hjd : (j : ℝ) ≤ |w - m| := by
    by_cases h : m ≤ n0
    · have hn : (n0 : ℝ) ≤ w := Nat.floor_le hw0.le
      have : (j : ℝ) = n0 - m := by rw [hj, if_pos h, Nat.cast_sub h]
      rw [this, abs_of_nonneg (by linarith [(Nat.cast_le (α := ℝ)).mpr h])]
      linarith
    · have hlt : w < n0 + 1 := Nat.lt_floor_add_one w
      have h' : n0 + 1 ≤ m := by omega
      have : (j : ℝ) = m - n0 - 1 := by
        rw [hj, if_neg h, Nat.sub_sub, Nat.cast_sub h']; push_cast; ring
      have hc : ((n0 + 1 : ℕ) : ℝ) ≤ m := Nat.cast_le.mpr h'
      push_cast at hc
      rw [this, abs_of_nonpos (by linarith)]
      linarith
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  split_ifs with h1
  · have : w = m := (div_eq_one_iff_eq hm0.ne').mp h1
    have : (j : ℝ) ≤ 0 := by rw [this, sub_self, abs_zero] at hjd; exact hjd
    rw [le_div_iff₀ (by linarith)]; linarith
  · have hsq : (w / m) ^ (1 / 2 : ℝ) ≤ 3 := by
      have h6 : w / m ≤ 6 := by
        rw [div_le_iff₀ hm0]; nlinarith
      calc (w / m) ^ (1 / 2 : ℝ) ≤ 6 ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) h6 (by norm_num)
        _ = Real.sqrt 6 := (Real.sqrt_eq_rpow 6).symm
        _ ≤ 3 := by
            rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hL : |w - m| / (6 * Y) ≤ |Real.log (w / m)| :=
      abs_log_div_ge hw0 hm0 hw2 (by linarith)
    have hmin : min 1 (1 / (Y * |Real.log (w / m)|)) ≤ 12 / ((j : ℝ) + 1) := by
      by_cases hj1 : (j : ℝ) < 1
      · refine (min_le_left _ _).trans ?_
        rw [le_div_iff₀ (by linarith)]; linarith
      · push Not at hj1
        have hd : 1 ≤ |w - m| := hj1.trans hjd
        have hYL : |w - m| / 6 ≤ Y * |Real.log (w / m)| := by
          have := mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ Y)
          calc |w - m| / 6 = Y * (|w - m| / (6 * Y)) := by field_simp
            _ ≤ _ := this
        refine (min_le_right _ _).trans ?_
        have hpos : 0 < |w - m| / 6 := by positivity
        calc 1 / (Y * |Real.log (w / m)|) ≤ 1 / (|w - m| / 6) :=
              one_div_le_one_div_of_le hpos hYL
          _ = 6 / |w - m| := by field_simp
          _ ≤ 6 / j := div_le_div_of_nonneg_left (by norm_num) (by linarith) hjd
          _ ≤ 12 / ((j : ℝ) + 1) := by
              rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
    have hm' : 0 ≤ min 1 (1 / (Y * |Real.log (w / m)|)) :=
      le_min zero_le_one (by positivity)
    calc (w / m) ^ (1 / 2 : ℝ) * min 1 (1 / (Y * |Real.log (w / m)|))
        ≤ 3 * (12 / ((j : ℝ) + 1)) := mul_le_mul hsq hmin hm' (by norm_num)
      _ = 36 / ((j : ℝ) + 1) := by ring

/-- Page 43 to 44, proof of Lemma 29, the error sum of Titchmarsh [29] Lemma 3.19 over the
interval J, PROVED with constant 504. For `Y/2 ≤ w ≤ 6Y` and `m` in `J = (⌊Y⌋, ⌊2Y⌋]`,
`(w/m)^(1/2) ≤ 6^(1/2)` and `|log (w/m)| ≥ |w - m| / (6Y)`, so the kernel errors sum to
`≪ Σ_{k ≤ 2Y} min(1, 6/k) ≪ log Y`; the one `m` with `m = w`, if any, adds `1`. This is the
`O(max |b(m)| log Y)` of the Perron error, which the paper absorbs in `O(Y^ε)`. -/
theorem leaf_perron_error_count :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 2 ≤ Y → ∀ w : ℝ, Y / 2 ≤ w → w ≤ 6 * Y →
      ∑ m ∈ Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊,
          (if w / m = 1 then 1 else (w / m) ^ (1 / 2 : ℝ) * min 1 (1 / (Y * |Real.log (w / m)|))) ≤
        C * Real.log Y := by
  refine ⟨504, by norm_num, fun Y hY w hw1 hw2 => ?_⟩
  set n0 := ⌊w⌋₊ with hn0
  set B := ⌊2 * Y⌋₊ with hB
  set S := Finset.Ioc ⌊Y⌋₊ B with hS
  set N := B + n0 + 1 with hN
  set φ : ℕ → ℝ := fun j => 36 / ((j : ℝ) + 1) with hφ
  have hφ0 : ∀ j, 0 ≤ φ j := fun j => by simp only [hφ]; positivity
  have hmem : ∀ m ∈ S, Y < m ∧ (m : ℝ) ≤ 2 * Y := by
    intro m hm
    rw [hS, Finset.mem_Ioc] at hm
    refine ⟨?_, ?_⟩
    · have := Nat.lt_floor_add_one Y
      have h2 : ((⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ m := Nat.cast_le.mpr hm.1
      push_cast at h2; linarith
    · exact (Nat.cast_le.mpr hm.2).trans (Nat.floor_le (by linarith))
  -- termwise
  have h1 : ∑ m ∈ S, (if w / m = 1 then 1 else
        (w / m) ^ (1 / 2 : ℝ) * min 1 (1 / (Y * |Real.log (w / m)|))) ≤
      ∑ m ∈ S, φ (if m ≤ n0 then n0 - m else m - n0 - 1) :=
    Finset.sum_le_sum fun m hm => term_le hY hw1 hw2 (hmem m hm).1 (hmem m hm).2
  -- split and reindex
  have h2 : ∑ m ∈ S, φ (if m ≤ n0 then n0 - m else m - n0 - 1) ≤
      2 * ∑ j ∈ Finset.range N, φ j := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun m => m ≤ n0)]
    have ha : ∑ m ∈ S.filter (fun m => m ≤ n0), φ (if m ≤ n0 then n0 - m else m - n0 - 1) =
        ∑ m ∈ S.filter (fun m => m ≤ n0), φ (n0 - m) :=
      Finset.sum_congr rfl fun m hm => by rw [if_pos (Finset.mem_filter.mp hm).2]
    have hb : ∑ m ∈ S.filter (fun m => ¬ m ≤ n0), φ (if m ≤ n0 then n0 - m else m - n0 - 1) =
        ∑ m ∈ S.filter (fun m => ¬ m ≤ n0), φ (m - n0 - 1) :=
      Finset.sum_congr rfl fun m hm => by rw [if_neg (Finset.mem_filter.mp hm).2]
    rw [ha, hb, two_mul]
    refine add_le_add (sum_comp_le_range φ hφ0 ?_ ?_) (sum_comp_le_range φ hφ0 ?_ ?_)
    · intro a ha b hb hab
      have := (Finset.mem_filter.mp ha).2; have := (Finset.mem_filter.mp hb).2
      have hab' : n0 - a = n0 - b := hab
      omega
    · intro m hm; omega
    · intro a ha b hb hab
      have := (Finset.mem_filter.mp ha).2; have := (Finset.mem_filter.mp hb).2
      have hab' : a - n0 - 1 = b - n0 - 1 := hab
      omega
    · intro m hm
      have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).2
      omega
  -- harmonic bound
  have h3 : ∑ j ∈ Finset.range N, φ j ≤ 36 * (1 + Real.log N) := by
    have := harmonic_real_le N
    calc ∑ j ∈ Finset.range N, φ j = 36 * ∑ j ∈ Finset.range N, (1 : ℝ) / ((j : ℝ) + 1) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
          simp only [hφ]; ring
      _ ≤ _ := by linarith
  -- N ≤ Y^5 and 1 ≤ 2 log Y
  have hY0 : 0 < Y := by linarith
  have hNle : (N : ℝ) ≤ Y ^ 5 := by
    have hBr : (B : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
    have hnr : (n0 : ℝ) ≤ 6 * Y := (Nat.floor_le (by linarith)).trans hw2
    have : (N : ℝ) = B + n0 + 1 := by rw [hN]; push_cast; ring
    rw [this]
    have hY4 : 16 ≤ Y ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) hY 4; norm_num at this; linarith
    nlinarith
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hlogN : Real.log N ≤ 5 * Real.log Y := by
    calc Real.log N ≤ Real.log (Y ^ 5) := Real.log_le_log (by linarith) hNle
      _ = 5 * Real.log Y := by rw [Real.log_pow]; norm_num
  have hlog2 : 1 ≤ 2 * Real.log Y := by
    have h := Real.log_le_log (by norm_num) hY
    have := Real.log_two_gt_d9
    linarith
  calc _ ≤ ∑ m ∈ S, φ (if m ≤ n0 then n0 - m else m - n0 - 1) := h1
    _ ≤ 2 * ∑ j ∈ Finset.range N, φ j := h2
    _ ≤ 2 * (36 * (1 + Real.log N)) := by linarith
    _ ≤ 504 * Real.log Y := by linarith


/-- Page 43, hypothesis 3.1 on the coefficients, `|b(m)| ≪ d(m)^B`, turned into a power bound
`|b(m) χ(m)| ≤ A0 m^(1/400)` by the divisor bound `d(m) ≪ m^δ`, PROVED. -/
theorem coeff_le_rpow (b : ℝ → ℕ → ℝ) {B : ℝ}
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ A0 : ℝ, 0 ≤ A0 ∧ ∀ x : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q,
      ‖(b x m : ℂ) * χ (m : ZMod q)‖ ≤ A0 * (m : ℝ) ^ (1 / 400 : ℝ) := by
  obtain ⟨C0, hC0⟩ := hb
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  set δ0 : ℝ := 1 / (400 * (B' + 1)) with hδ0
  have hδ0p : 0 < δ0 := by rw [hδ0]; positivity
  obtain ⟨Kd, hKd, hdiv⟩ :=
    LeanLab.BHP1997.PerronHalfSmall.card_divisors_le_rpow_real δ0 hδ0p
  refine ⟨max C0 0 * Kd ^ B', by positivity, fun x m hm q χ => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd1 : (1 : ℝ) ≤ (m.divisors.card : ℝ) := by
    have : 1 ≤ m.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, by omega⟩⟩
    exact_mod_cast this
  have hnorm : ‖(b x m : ℂ) * χ (m : ZMod q)‖ ≤ |b x m| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have h1 : |b x m| ≤ max C0 0 * (m.divisors.card : ℝ) ^ B' := by
    refine (hC0 x m).trans ?_
    have hdB : ((m.divisors.card : ℕ) : ℝ) ^ B ≤ (m.divisors.card : ℝ) ^ B' :=
      Real.rpow_le_rpow_of_exponent_le hd1 (le_max_left _ _)
    calc C0 * ((m.divisors.card : ℕ) : ℝ) ^ B ≤ max C0 0 * ((m.divisors.card : ℕ) : ℝ) ^ B :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
      _ ≤ max C0 0 * (m.divisors.card : ℝ) ^ B' :=
          mul_le_mul_of_nonneg_left hdB (le_max_right _ _)
  have h2 : (m.divisors.card : ℝ) ^ B' ≤ Kd ^ B' * (m : ℝ) ^ (1 / 400 : ℝ) := by
    have hm0 : (0 : ℝ) ≤ m := by positivity
    calc (m.divisors.card : ℝ) ^ B' ≤ (Kd * (m : ℝ) ^ δ0) ^ B' :=
          Real.rpow_le_rpow (by positivity) (hdiv m hm) hB'0
      _ = Kd ^ B' * (m : ℝ) ^ (δ0 * B') := by
          rw [Real.mul_rpow hKd.le (Real.rpow_nonneg hm0 _), ← Real.rpow_mul hm0]
      _ ≤ Kd ^ B' * (m : ℝ) ^ (1 / 400 : ℝ) := by
          refine mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hm1 ?_) (by positivity)
          rw [hδ0, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  calc ‖(b x m : ℂ) * χ (m : ZMod q)‖ ≤ max C0 0 * (m.divisors.card : ℝ) ^ B' := hnorm.trans h1
    _ ≤ max C0 0 * (Kd ^ B' * (m : ℝ) ^ (1 / 400 : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ = _ := by ring

/-- Page 3, the definition of Q: `Q ≤ Y^(1/16)` when `Y ≥ 1`. PROVED, as in S64. -/
theorem sieveQ_le_sixteenth' {ε x : ℝ} (hY : 1 ≤ x ^ (11 / 20 + ε)) :
    (sieveQ ε x : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) := by
  have hY0 : 0 ≤ x ^ (11 / 20 + ε) := by linarith
  unfold sieveQ
  calc
    _ ≤ ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) / 2 :=
      Nat.floor_le (by positivity)
    _ ≤ ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) :=
      div_le_self (by positivity) (by norm_num)
    _ = (x ^ (11 / 20 + ε)) ^ ((1 / 16 : ℝ) - 1 / 10 ^ 5) := by
      rw [← Real.rpow_mul hY0]
      congr 1
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY (by norm_num)

/-- For `Y ≥ 6^16`, `6 Y^(1/8) ≤ Y`. PROVED, as in S64. -/
theorem six_mul_eighth_le' {Y : ℝ} (hY : (6 : ℝ) ^ 16 ≤ Y) :
    6 * Y ^ (1 / 8 : ℝ) ≤ Y := by
  have hY0 : 0 ≤ Y := le_trans (by positivity) hY
  have hY1 : 1 ≤ Y := le_trans (by norm_num) hY
  have e : (1 / 16 : ℝ) = ((16 : ℕ) : ℝ)⁻¹ := by norm_num
  have h1 : (6 : ℝ) ≤ Y ^ (1 / 16 : ℝ) := by
    have := Real.rpow_le_rpow (by positivity) hY (by norm_num : (0:ℝ) ≤ 1 / 16)
    rw [e, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)] at this
    rw [e]; exact this
  have h2 : Y ^ (1 / 16 : ℝ) ≤ Y ^ (7 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
  have h3 : Y = Y ^ (7 / 8 : ℝ) * Y ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have h4 : 0 ≤ Y ^ (1 / 8 : ℝ) := Real.rpow_nonneg hY0 _
  calc 6 * Y ^ (1 / 8 : ℝ) ≤ Y ^ (7 / 8 : ℝ) * Y ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) h4
    _ = Y := h3.symm

/-- Page 43 to 44, proof of Lemma 29: the indicator of the window `y ≤ m ≤ w` is
`δ(w/m) - δ(y/m) + [m = w]` with `δ(u) = [u > 1]`, for `0 < y ≤ w`, `m > 0`. PROVED. -/
theorem window_indicator {y w : ℝ} (_hy : 0 < y) (hyw : y ≤ w) {m : ℝ} (hm : 0 < m) :
    (if y ≤ m ∧ m ≤ w then (1 : ℂ) else 0) =
      ((if 1 < w / m then 1 else 0) - (if 1 < y / m then 1 else 0)) +
        (if w / m = 1 then 1 else 0) := by
  have e1 : (1 < w / m) ↔ m < w := by rw [one_lt_div hm]
  have e2 : (1 < y / m) ↔ m < y := by rw [one_lt_div hm]
  have e3 : (w / m = 1) ↔ w = m := div_eq_one_iff_eq hm.ne'
  by_cases h1 : m < y
  · have : m < w := lt_of_lt_of_le h1 hyw
    simp [e1, e2, e3, h1, this, not_le.mpr h1, this.ne']
  · by_cases h2 : m < w
    · simp [e1, e2, e3, h1, h2, not_lt.mp h1, h2.le, h2.ne']
    · by_cases h3 : w = m
      · subst h3; simp [e1, e2, e3, h1, not_lt.mp h1]
      · have h4 : w < m := lt_of_le_of_ne (not_lt.mp h2) h3
        simp [e1, e2, e3, h1, h2, h3, not_le.mpr h4]

/-- Page 43 to 44, proof of Lemma 29, "by [29] Lemma 3.19": the exact statement of
`S64LowExcCharNP.leaf_perron_window`, PROVED from the two LEAFs `leaf_perron_kernel_half` and
`leaf_perron_error_count`, with the termwise identity `perron_window_identity`, the window
indicator, the coefficient bound `coeff_le_rpow`, `z ≤ 1` from `Q ≤ Y^(1/16)`, and
`log Y ≤ 400 Y^(1/400)`. The constant is `K = 2400 C A0`, with `ε` of the error `1/100`. -/
theorem leaf_perron_window_of_s130 (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
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
  obtain ⟨A0, hA0, hcoef⟩ := coeff_le_rpow b hb
  obtain ⟨Cc, hCc, hcount⟩ := leaf_perron_error_count
  refine ⟨2400 * Cc * A0, by positivity, (6 : ℝ) ^ 32, fun x hx q hq hqQ z hz1 hz2 χ y hy1 hy2 => ?_⟩
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hY16 : (6 : ℝ) ^ 16 ≤ Y := by
    have h1 : ((6 : ℝ) ^ 32) ^ (1 / 2 : ℝ) ≤ x ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hx (by norm_num)
    have h2 : ((6 : ℝ) ^ 32) ^ (1 / 2 : ℝ) = 6 ^ 16 := by
      rw [show (6 : ℝ) ^ 32 = (6 ^ 16) ^ 2 by norm_num, ← Real.sqrt_eq_rpow,
        Real.sqrt_sq (by positivity)]
    have h3 : x ^ (1 / 2 : ℝ) ≤ Y := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    linarith
  have hY1 : (1 : ℝ) ≤ Y := le_trans (by norm_num) hY16
  have hY2 : (2 : ℝ) ≤ Y := le_trans (by norm_num) hY16
  have hY0 : 0 < Y := by linarith
  have hy0 : 0 < y := by linarith
  -- z ≥ 0 and z ≤ 1
  have hQ : (sieveQ ε x : ℝ) ≤ Y ^ (1 / 16 : ℝ) := sieveQ_le_sixteenth' hY1
  have hz0 : 0 ≤ z := le_trans (by positivity) hz1
  have hzle : z ≤ 1 := by
    have hqQ' : (q : ℝ) ≤ sieveQ ε x := by exact_mod_cast hqQ
    have hQ0 : (0 : ℝ) ≤ sieveQ ε x := by positivity
    have hsq : (q : ℝ) * sieveQ ε x ≤ Y ^ (1 / 8 : ℝ) := by
      have h16 : 0 ≤ Y ^ (1 / 16 : ℝ) := Real.rpow_nonneg hY0.le _
      calc (q : ℝ) * sieveQ ε x ≤ Y ^ (1 / 16 : ℝ) * Y ^ (1 / 16 : ℝ) :=
            mul_le_mul (hqQ'.trans hQ) hQ (by positivity) h16
        _ = Y ^ (1 / 8 : ℝ) := by rw [← Real.rpow_add hY0]; norm_num
    have h6 := six_mul_eighth_le' hY16
    calc z ≤ 6 * q * sieveQ ε x / Y := hz2
      _ ≤ 6 * Y ^ (1 / 8 : ℝ) / Y := by
          apply div_le_div_of_nonneg_right _ hY0.le
          nlinarith
      _ ≤ 1 := by rw [div_le_one hY0]; exact h6
  set w := y + y * z with hw
  have hyw : y ≤ w := by rw [hw]; nlinarith
  have hw0 : 0 < w := by linarith
  have hw6 : w ≤ 6 * Y := by rw [hw]; nlinarith
  have hwlo : Y / 2 ≤ w := by linarith
  -- the Perron identity
  set a : ℕ → ℂ := fun m => (b x m : ℂ) * χ (m : ZMod q) with ha
  have hJ : ∀ m ∈ rightInterval ε x, 1 ≤ m := by
    intro m hm; unfold rightInterval at hm; rw [Finset.mem_Ioc] at hm; omega
  have hid := perron_window_identity (rightInterval ε x) hJ a hy0 hw0 Y
  simp only [ha] at hid
  rw [hid, Finset.sum_filter, ← Finset.sum_sub_distrib]
  -- termwise bound
  set G : ℝ → ℝ := fun u =>
    if u = 1 then 1 else u ^ (1 / 2 : ℝ) * min 1 (1 / (Y * |Real.log u|)) with hG
  have hG0 : ∀ u, 0 < u → 0 ≤ G u := by
    intro u hu; simp only [hG]; split_ifs
    · norm_num
    · exact mul_nonneg (Real.rpow_nonneg hu.le _) (le_min zero_le_one (by positivity))
  have hcoefJ : ∀ m ∈ rightInterval ε x, ‖a m‖ ≤ A0 * (2 * Y) ^ (1 / 400 : ℝ) := by
    intro m hm
    have hm1 := hJ m hm
    refine (hcoef x m hm1 q χ).trans (mul_le_mul_of_nonneg_left ?_ hA0)
    have : (m : ℝ) ≤ 2 * Y := by
      unfold rightInterval at hm; rw [Finset.mem_Ioc] at hm
      exact (Nat.cast_le.mpr hm.2).trans (Nat.floor_le (by positivity))
    exact Real.rpow_le_rpow (by positivity) this (by norm_num)
  have hterm : ∀ m ∈ rightInterval ε x,
      ‖(if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ w then a m else 0) -
          a m * (perronI (w / m) (1 / 2) Y - perronI (y / m) (1 / 2) Y)‖ ≤
        A0 * (2 * Y) ^ (1 / 400 : ℝ) * (2 * G (w / m) + G (y / m)) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hJ m hm
    have hind := window_indicator hy0 hyw hm0
    have e : (if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ w then a m else 0) =
        a m * (if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ w then (1 : ℂ) else 0) := by
      split_ifs <;> simp
    rw [e, hind]
    have e2 : a m * ((((if 1 < w / m then 1 else 0) - (if 1 < y / m then 1 else 0)) +
          (if w / m = 1 then 1 else 0)) : ℂ) -
        a m * (perronI (w / m) (1 / 2) Y - perronI (y / m) (1 / 2) Y) =
        a m * ((if w / m = 1 then 1 else 0) -
          (perronI (w / m) (1 / 2) Y - (if 1 < w / m then 1 else 0)) +
          (perronI (y / m) (1 / 2) Y - (if 1 < y / m then 1 else 0))) := by ring
    rw [e2, norm_mul]
    have k1 := leaf_perron_kernel_half (w / m) (div_pos hw0 hm0) Y hY1
    have k2 := leaf_perron_kernel_half (y / m) (div_pos hy0 hm0) Y hY1
    have hind1 : ‖(if w / m = 1 then (1 : ℂ) else 0)‖ ≤ G (w / m) := by
      have := hG0 (w / m) (div_pos hw0 hm0)
      split_ifs with hh
      · simp only [hG, hh, ite_true]; simp
      · simpa using this
    have hsum : ‖((if w / m = 1 then 1 else 0) -
          (perronI (w / m) (1 / 2) Y - (if 1 < w / m then 1 else 0)) +
          (perronI (y / m) (1 / 2) Y - (if 1 < y / m then 1 else 0)) : ℂ)‖ ≤
        2 * G (w / m) + G (y / m) := by
      refine (norm_add_le _ _).trans ?_
      refine le_trans (add_le_add (norm_sub_le _ _) le_rfl) ?_
      have : ‖perronI (w / m) (1 / 2) Y - (if 1 < w / m then 1 else 0)‖ ≤ G (w / m) := k1
      have : ‖perronI (y / m) (1 / 2) Y - (if 1 < y / m then 1 else 0)‖ ≤ G (y / m) := k2
      linarith
    exact mul_le_mul (hcoefJ m hm) hsum (norm_nonneg _) (by positivity)
  -- sum the bounds
  have hcw := hcount Y hY2 w hwlo hw6
  have hcy := hcount Y hY2 y hy1 (by linarith)
  have hJdef : rightInterval ε x = Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊ := rfl
  have hsumG : ∑ m ∈ rightInterval ε x, (2 * G (w / m) + G (y / m)) ≤ 3 * Cc * Real.log Y := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hJdef]
    simp only [hG]
    linarith
  have hlog : Real.log Y ≤ 400 * Y ^ (1 / 400 : ℝ) := by
    have := Real.log_le_rpow_div hY0.le (by norm_num : (0 : ℝ) < 1 / 400)
    linarith [show Y ^ (1 / 400 : ℝ) / (1 / 400) = 400 * Y ^ (1 / 400 : ℝ) by ring]
  have h2Y : (2 * Y) ^ (1 / 400 : ℝ) ≤ 2 * Y ^ (1 / 400 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hY0.le]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hY0.le _)
    calc (2 : ℝ) ^ (1 / 400 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hYpow : Y ^ (1 / 400 : ℝ) * Y ^ (1 / 400 : ℝ) ≤ Y ^ (1 / 100 : ℝ) := by
    rw [← Real.rpow_add hY0]
    exact Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
  have hlog0 : 0 ≤ Real.log Y := Real.log_nonneg hY1
  have hP0 : 0 ≤ Y ^ (1 / 400 : ℝ) := Real.rpow_nonneg hY0.le _
  calc ‖∑ m ∈ rightInterval ε x, ((if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ w then a m else 0) -
          a m * (perronI (w / m) (1 / 2) Y - perronI (y / m) (1 / 2) Y))‖
      ≤ ∑ m ∈ rightInterval ε x, A0 * (2 * Y) ^ (1 / 400 : ℝ) * (2 * G (w / m) + G (y / m)) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = A0 * (2 * Y) ^ (1 / 400 : ℝ) * ∑ m ∈ rightInterval ε x, (2 * G (w / m) + G (y / m)) := by
        rw [Finset.mul_sum]
    _ ≤ A0 * (2 * Y ^ (1 / 400 : ℝ)) * (3 * Cc * (400 * Y ^ (1 / 400 : ℝ))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h2Y hA0) _ (Finset.sum_nonneg fun m hm => by
          have hm0 : (0 : ℝ) < m := by exact_mod_cast hJ m hm
          have := hG0 (w / m) (div_pos hw0 hm0); have := hG0 (y / m) (div_pos hy0 hm0)
          positivity) (by positivity)
        exact hsumG.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
    _ = 2400 * Cc * A0 * (Y ^ (1 / 400 : ℝ) * Y ^ (1 / 400 : ℝ)) := by ring
    _ ≤ 2400 * Cc * A0 * Y ^ (1 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left hYpow (by positivity)

end LeanLab.BHP1997.S130PerronWindow
