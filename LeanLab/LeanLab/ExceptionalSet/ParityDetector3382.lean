import LeanLab.ExceptionalSet.Selberg524
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Analysis.Complex.Trigonometric

/-!
Symmetrization of Selberg's interval majorant for P0082 page 370 display 40.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.ParityDetector3382

open Real Finset

theorem symmetric_sum {E : Type*} [AddCommGroup E] (f : ℤ → E) (H : ℕ) :
    (∑ h ∈ Icc (-(H : ℤ)) H, f h) =
      f 0 + ∑ h ∈ Icc 1 H, (f (h : ℤ) + f (-(h : ℤ))) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Nat.cast_succ, Finset.sum_Icc_succ_eq_add_endpoints f, ih,
      Finset.sum_Icc_succ_top (by omega)]
    push_cast
    abel

theorem cosine_integer_shift (h : ℕ) (x : ℝ) (z : ℤ) :
    cos (2 * π * ((h : ℝ) * (x - z))) = cos (2 * π * ((h : ℝ) * x)) := by
  have he : 2 * π * ((h : ℝ) * (x - z)) =
      2 * π * ((h : ℝ) * x) - (((h : ℤ) * z : ℤ) : ℝ) * (2 * π) := by
    push_cast
    ring
  rw [he, Real.cos_sub_int_mul_two_pi]

theorem parity_cosine_majorant (H : ℕ) (hH : 8 ≤ H) :
    ∃ (c₀ : ℝ) (g : ℕ → ℝ),
      c₀ ≤ 1 / 2 + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, |g h| ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ,
        |(if Even ⌊x⌋ then (1 : ℝ) else 0) -
            (1 / 2 + ∑ h ∈ Icc 1 H,
              g h * sin (π * h / 2) * sin (π * h * x))| ≤
          max (c₀ - 1 / 2) 0 +
            ∑ h ∈ Icc 1 H, g h * cos (π * h / 2) * cos (π * h * x) := by
  classical
  have hHr : (8 : ℝ) ≤ H := by exact_mod_cast hH
  obtain ⟨c₀, g, hc₀, hg, hm⟩ :=
    Selberg524.selberg_cosine_majorant524 (1 / 2) H (by norm_num)
      (by have := (div_lt_iff₀ (show (0 : ℝ) < H + 1 by positivity)).mpr
                    (show (4 : ℝ) < (1 / 2) * (H + 1) by linarith)
          linarith)
  refine ⟨c₀, g, hc₀, hg, fun x => ?_⟩
  let A := ∑ h ∈ Icc 1 H, g h * cos (2 * π * ((h : ℝ) * (x / 2 - 1 / 4)))
  let B := ∑ h ∈ Icc 1 H, g h * cos (2 * π * ((h : ℝ) * (x / 2 + 1 / 4)))
  have hA : 0 ≤ c₀ + A := by
    have ht := hm (x / 2 - 1 / 4)
    split_ifs at ht <;> dsimp [A] <;> linarith
  have hB : 0 ≤ c₀ + B := by
    have ht := hm (x / 2 + 1 / 4)
    split_ifs at ht <;> dsimp [B] <;> linarith
  have hA1 (hx : Even ⌊x⌋) : 1 ≤ c₀ + A := by
    obtain ⟨z, hz⟩ := hx
    have hxl := Int.floor_le x
    have hxu := Int.lt_floor_add_one x
    have hfl : (⌊x⌋ : ℝ) = 2 * (z : ℝ) := by
      exact_mod_cast (show ⌊x⌋ = 2 * z by omega)
    have ht := hm (x / 2 - 1 / 4 - z)
    have ha : |x / 2 - 1 / 4 - z| ≤ (1 / 2 : ℝ) / 2 := by
      rw [abs_le]
      constructor <;> linarith
    rw [if_pos ha] at ht
    simpa only [cosine_integer_shift] using ht
  have hB1 (hx : ¬ Even ⌊x⌋) : 1 ≤ c₀ + B := by
    obtain ⟨z, hz⟩ := (Int.not_even_iff_odd.mp hx).exists_bit1
    have hxl := Int.floor_le x
    have hxu := Int.lt_floor_add_one x
    have hfl : (⌊x⌋ : ℝ) = 2 * (z : ℝ) + 1 := by exact_mod_cast hz
    have ht := hm (x / 2 + 1 / 4 - (z + 1 : ℤ))
    have ha : |x / 2 + 1 / 4 - (z + 1 : ℤ)| ≤ (1 / 2 : ℝ) / 2 := by
      push_cast
      rw [abs_le]
      constructor <;> linarith
    rw [if_pos ha] at ht
    simpa only [cosine_integer_shift] using ht
  have hAc :
      A = (∑ h ∈ Icc 1 H, g h * cos (π * h / 2) * cos (π * h * x)) +
        ∑ h ∈ Icc 1 H, g h * sin (π * h / 2) * sin (π * h * x) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro h _
    rw [show 2 * π * ((h : ℝ) * (x / 2 - 1 / 4)) =
      π * h * x - π * h / 2 by ring, Real.cos_sub]
    ring
  have hBc :
      B = (∑ h ∈ Icc 1 H, g h * cos (π * h / 2) * cos (π * h * x)) -
        ∑ h ∈ Icc 1 H, g h * sin (π * h / 2) * sin (π * h * x) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro h _
    rw [show 2 * π * ((h : ℝ) * (x / 2 + 1 / 4)) =
      π * h * x + π * h / 2 by ring, Real.cos_add]
    ring
  have hmax := le_max_left (c₀ - 1 / 2) 0
  rw [abs_le]
  by_cases hx : Even ⌊x⌋
  · have := hA1 hx
    rw [if_pos hx]
    constructor <;> linarith
  · have := hB1 hx
    rw [if_neg hx]
    constructor <;> linarith

theorem even_cosine_sum (H : ℕ) (g : ℕ → ℝ) (x : ℝ) :
    (∑ h ∈ Icc 1 H, g h * cos (π * h / 2) * cos (π * h * x)) =
      ∑ k ∈ Icc 1 H,
        (if 2 * k ≤ H then g (2 * k) * (-1) ^ k else 0) *
          cos (2 * π * k * x) := by
  classical
  have hfilter :
      (∑ h ∈ Icc 1 H, g h * cos (π * h / 2) * cos (π * h * x)) =
        ∑ h ∈ (Icc 1 H).filter Even, g h * cos (π * h / 2) * cos (π * h * x) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro h _
    by_cases hh : Even h
    · simp [hh]
    · obtain ⟨k, hk⟩ := (Nat.not_even_iff_odd.mp hh).exists_bit1
      have he : π * (h : ℝ) / 2 = (k : ℝ) * π + π / 2 := by
        rw [hk]
        push_cast
        ring
      simp [hh, he, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]
  rw [hfilter]
  calc
    _ = ∑ k ∈ (Icc 1 H).filter (fun k => 2 * k ≤ H),
        g (2 * k) * (-1) ^ k * cos (2 * π * k * x) := by
      apply sum_bij (fun h _ => h / 2)
      · intro h hh
        obtain ⟨hh, ⟨k, hk⟩⟩ := mem_filter.mp hh
        obtain ⟨hh1, hhH⟩ := mem_Icc.mp hh
        simp only [mem_filter, mem_Icc]
        omega
      · intro h hh j hj he
        obtain ⟨_, ⟨k, hk⟩⟩ := mem_filter.mp hh
        obtain ⟨_, ⟨l, hl⟩⟩ := mem_filter.mp hj
        omega
      · intro k hk
        obtain ⟨hk, hkH⟩ := mem_filter.mp hk
        have hk1 := (mem_Icc.mp hk).1
        refine ⟨2 * k, mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hkH⟩,
          ⟨k, by omega⟩⟩, by omega⟩
      · intro h hh
        obtain ⟨_, ⟨k, hk⟩⟩ := mem_filter.mp hh
        have he : h = 2 * (h / 2) := by omega
        have hc : cos (π * (h : ℝ) / 2) = (-1 : ℝ) ^ (h / 2) := by
          conv_lhs => rw [he]
          rw [show π * ((2 * (h / 2) : ℕ) : ℝ) / 2 = (h / 2 : ℕ) * π by
            push_cast; ring]
          exact Real.cos_nat_mul_pi _
        rw [hc, ← he]
        congr 2
        congr 1
        have he' : (h : ℝ) = 2 * (h / 2 : ℕ) := by exact_mod_cast he
        rw [he']
        ring
    _ = _ := by
      rw [sum_filter]
      apply sum_congr rfl
      intro k _
      split_ifs <;> simp_all

theorem sine_exponentials (r t : ℝ) :
    (r : ℂ) * Complex.I / 2 * Complex.exp (-(t : ℂ) * Complex.I) +
      (-((r : ℂ) * Complex.I / 2)) * Complex.exp ((t : ℂ) * Complex.I) =
        (r * sin t : ℝ) := by
  apply Complex.ext <;>
    simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im,
      Complex.sin_ofReal_re] <;> ring

theorem sine_coefficients (H : ℕ) (r : ℕ → ℝ) (hr : ∀ h, |r h| ≤ 4) :
    ∃ a : ℤ → ℂ, (∀ h, ‖a h‖ ≤ 4) ∧ ∀ x : ℝ,
      (∑ h ∈ Icc (-(H : ℤ)) H,
        a h * Complex.exp (2 * π * Complex.I * ((-((h : ℝ) / 2) * x : ℝ) : ℂ))) =
          ((1 / 2 + ∑ h ∈ Icc 1 H, r h * sin (π * h * x) : ℝ) : ℂ) := by
  classical
  let a : ℤ → ℂ := fun h =>
    if h = 0 then 1 / 2 else
      if h < 0 then -((r h.natAbs : ℂ) * Complex.I / 2)
      else (r h.natAbs : ℂ) * Complex.I / 2
  refine ⟨a, ?_, fun x => ?_⟩
  · intro h
    dsimp [a]
    split_ifs <;>
      norm_num [norm_neg, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs] <;>
      linarith [hr h.natAbs]
  · rw [symmetric_sum]
    rw [show a 0 = (1 / 2 : ℂ) by simp [a]]
    push_cast
    simp only [zero_div, neg_zero, zero_mul, mul_zero, Complex.exp_zero, mul_one]
    congr 1
    apply sum_congr rfl
    intro h hh
    have hhpos : (0 : ℤ) < h := by have := (mem_Icc.mp hh).1; omega
    have hh0 : h ≠ 0 := by omega
    have hp : a h = (r h : ℂ) * Complex.I / 2 := by
      simp [a, hh0, not_lt.mpr hhpos.le]
    have hn : a (-(h : ℤ)) = -((r h : ℂ) * Complex.I / 2) := by
      simp [a, hh0, neg_lt_zero.mpr hhpos]
    rw [hp, hn]
    convert sine_exponentials (r h) (π * h * x) using 1 <;> push_cast <;> ring

theorem detector :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 1 ≤ H →
      ∃ (a : ℤ → ℂ) (q₀ : ℝ) (b : ℕ → ℂ),
        (∀ h, ‖a h‖ ≤ C) ∧ 0 ≤ q₀ ∧ q₀ ≤ C / H ∧ (∀ k, ‖b k‖ ≤ C) ∧
        ∀ x : ℝ,
          ‖(if Even ⌊x⌋ then (1 : ℂ) else 0) -
              ∑ h ∈ Icc (-(H : ℤ)) H,
                a h * Complex.exp (2 * π * Complex.I *
                  ((-((h : ℝ) / 2) * x : ℝ) : ℂ))‖ ≤
            q₀ + (∑ k ∈ Icc (1 : ℕ) H,
              b k * Complex.exp (2 * π * Complex.I * (((k : ℝ) * x : ℝ) : ℂ))).re := by
  classical
  refine ⟨8, by norm_num, fun H hH => ?_⟩
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHp : (0 : ℝ) < H := by linarith
  by_cases hsmall : H < 8
  · refine ⟨fun h => if h = 0 then 1 / 2 else 0, 1 / 2, fun _ => 0,
      ?_, by norm_num, ?_, by simp, fun x => ?_⟩
    · intro h
      dsimp
      split_ifs <;> norm_num
    · rw [le_div_iff₀ hHp]
      have : (H : ℝ) < 8 := by exact_mod_cast hsmall
      linarith
    · have hsum :
          (∑ h ∈ Icc (-(H : ℤ)) H,
            (if h = 0 then (1 / 2 : ℂ) else 0) *
              Complex.exp (2 * π * Complex.I *
                ((-((h : ℝ) / 2) * x : ℝ) : ℂ))) = 1 / 2 := by
        rw [sum_eq_single 0]
        · simp
        · intro h _ hh
          simp [hh]
        · simp
      rw [hsum]
      simp only [zero_mul, sum_const_zero, Complex.zero_re, add_zero]
      split_ifs <;> norm_num
  · obtain ⟨c₀, g, hc₀, hg, hm⟩ := parity_cosine_majorant H (by omega)
    let r : ℕ → ℝ := fun h =>
      if h ∈ Icc 1 H then g h * sin (π * h / 2) else 0
    have hg4 (h : ℕ) (hh : h ∈ Icc 1 H) : |g h| ≤ 4 := by
      have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (mem_Icc.mp hh).1
      exact (hg h hh).trans ((div_le_iff₀ (by linarith)).mpr (by linarith))
    have hr : ∀ h, |r h| ≤ 4 := by
      intro h
      dsimp [r]
      split_ifs with hh
      · rw [abs_mul]
        have := mul_le_mul (hg4 h hh) (Real.abs_sin_le_one (π * h / 2))
          (abs_nonneg (sin (π * h / 2))) (by norm_num : (0 : ℝ) ≤ 4)
        simpa using this
      · norm_num
    obtain ⟨a, ha, hp⟩ := sine_coefficients H r hr
    let b : ℕ → ℂ := fun k =>
      if k ∈ Icc 1 H ∧ 2 * k ≤ H then (g (2 * k) * (-1) ^ k : ℝ) else 0
    have hq : max (c₀ - 1 / 2) 0 ≤ 8 / (H : ℝ) := by
      apply max_le
      · have hd : (4 : ℝ) / (H + 1) ≤ 8 / H := by
          apply (div_le_div_iff₀ (by positivity) hHp).mpr
          linarith
        linarith
      · positivity
    refine ⟨a, max (c₀ - 1 / 2) 0, b, fun h => (ha h).trans (by norm_num),
      le_max_right _ _, hq, ?_, fun x => ?_⟩
    · intro k
      dsimp [b]
      split_ifs with hk
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow]
        norm_num only [abs_neg, abs_one, one_pow, mul_one]
        have hk' : 2 * k ∈ Icc 1 H := mem_Icc.mpr ⟨by have := (mem_Icc.mp hk.1).1; omega, hk.2⟩
        exact (hg4 _ hk').trans (by norm_num)
      · norm_num
    · have hp' :
          (∑ h ∈ Icc (-(H : ℤ)) H,
            a h * Complex.exp (2 * π * Complex.I *
              ((-((h : ℝ) / 2) * x : ℝ) : ℂ))) =
            ((1 / 2 + ∑ h ∈ Icc 1 H,
              g h * sin (π * h / 2) * sin (π * h * x) : ℝ) : ℂ) := by
        convert hp x using 1
        congr 2
        apply sum_congr rfl
        intro h hh
        simp only [r, if_pos hh]
      have hb' :
          (∑ k ∈ Icc 1 H, b k *
            Complex.exp (2 * π * Complex.I * (((k : ℝ) * x : ℝ) : ℂ))).re =
            ∑ h ∈ Icc 1 H, g h * cos (π * h / 2) * cos (π * h * x) := by
        rw [even_cosine_sum, Complex.re_sum]
        apply sum_congr rfl
        intro k hk
        dsimp [b]
        simp only [hk, true_and]
        split_ifs
        · rw [Complex.re_ofReal_mul]
          simp only [Complex.exp_re, Complex.mul_re, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            mul_zero, zero_mul, sub_zero, add_zero, zero_add, Real.exp_zero,
            one_mul, mul_one]
          congr 2
          norm_num
          ring
        · simp
      rw [hp', hb']
      have hi : (if Even ⌊x⌋ then (1 : ℂ) else 0) =
          Complex.ofReal (if Even ⌊x⌋ then (1 : ℝ) else 0) := by
        split_ifs <;> rfl
      rw [hi, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hm x

end LeanLab.ExceptionalSet.ParityDetector3382
