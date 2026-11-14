import LeanLab.ExceptionalSet.Fejer467

/-!
P0082 page 359 Lemma 4, auxiliary finite kernel construction.
Source: https://doi.org/10.5802/aif.1621
The paper omits the discrepancy argument. These are derived finite identities.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp550a

open Real Finset
open LeanLab.ExceptionalSet.U1539 (eC)
open LeanLab.ExceptionalSet.Fejer467

/-- P0082 page 359 Lemma 4, derived local phase estimate for the finite
kernel construction. A phase in the first sixth of a turn has real part at least one half. -/
theorem phase_re_lower (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1 / 6) :
    (1 / 2 : ℝ) ≤ (eC x).re := by
  have he : (eC x).re = Real.cos (2 * Real.pi * x) := by
    simp [eC, Complex.exp_re]
  rw [he, ← Real.cos_pi_div_three]
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · positivity
  · linarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-- P0082 page 359 Lemma 4, derived local lower bound for the squared
geometric kernel. Grid spacing one over eight times H plus one suffices. -/
theorem geometric_kernel_local (H : ℕ) (x : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1 / (8 * ((H : ℝ) + 1))) :
    (((H : ℝ) + 1) / 2) ^ 2 ≤
      ‖∑ h ∈ range (H + 1), eC ((h : ℝ) * x)‖ ^ 2 := by
  have hre : ((H : ℝ) + 1) / 2 ≤
      (∑ h ∈ range (H + 1), eC ((h : ℝ) * x)).re := by
    rw [Complex.re_sum]
    calc
      _ = ∑ _h ∈ range (H + 1), (1 / 2 : ℝ) := by simp; ring
      _ ≤ _ := by
        apply sum_le_sum
        intro h hh
        apply phase_re_lower _ (mul_nonneg (Nat.cast_nonneg _) hx)
        have hhH : (h : ℝ) ≤ H := by exact_mod_cast (by have := mem_range.mp hh; omega : h ≤ H)
        have hmul : x * (8 * ((H : ℝ) + 1)) ≤ 1 :=
          (le_div_iff₀ (by positivity)).mp hx1
        nlinarith [mul_nonneg (sub_nonneg.mpr hhH) hx]
  have hn := Complex.re_le_norm (∑ h ∈ range (H + 1), eC ((h : ℝ) * x))
  nlinarith [Nat.cast_nonneg (α := ℝ) H,
    norm_nonneg (∑ h ∈ range (H + 1), eC ((h : ℝ) * x))]

/-- P0082 page 359 Lemma 4, derived real phase symmetry. -/
theorem phase_re_neg (x : ℝ) : (eC (-x)).re = (eC x).re := by
  rw [LeanLab.ExceptionalSet.U1539.eC_neg]
  rfl

/-- P0082 page 359 Lemma 4, derived recurrence for a squared geometric sum. -/
theorem geometric_kernel_step (H : ℕ) (x : ℝ) :
    ‖∑ h ∈ range (H + 1 + 1), eC ((h : ℝ) * x)‖ ^ 2 =
      ‖∑ h ∈ range (H + 1), eC ((h : ℝ) * x)‖ ^ 2 + 1 +
        2 * ∑ h ∈ range (H + 1), (eC (((h : ℝ) + 1) * x)).re := by
  rw [sum_range_succ, ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
  simp only [Complex.normSq_eq_norm_sq, LeanLab.ExceptionalSet.U1539.norm_eC,
    one_pow]
  congr 2
  rw [sum_mul, Complex.re_sum]
  calc
    _ = ∑ h ∈ range (H + 1), (eC ((((H : ℝ) + 1) - h) * x)).re := by
      apply sum_congr rfl
      intro h hh
      rw [← phase_sub, show (h : ℝ) * x - (H + 1 : ℕ) * x =
        -((((H : ℝ) + 1) - h) * x) by push_cast; ring, phase_re_neg]
    _ = _ := by
      rw [← sum_range_reflect (fun h : ℕ => (eC (((h : ℝ) + 1) * x)).re) (H + 1)]
      apply sum_congr rfl
      intro h hh
      have hhH : h ≤ H := by have := mem_range.mp hh; omega
      simp only [Nat.add_sub_cancel, Nat.cast_sub hhH]
      congr 2
      ring

/-- P0082 page 359 Lemma 4, derived finite Fourier expansion of the positive
geometric kernel. Its degree is H and its constant coefficient is H plus one. -/
theorem geometric_kernel_expansion (H : ℕ) (x : ℝ) :
    ‖∑ h ∈ range (H + 1), eC ((h : ℝ) * x)‖ ^ 2 =
      (H : ℝ) + 1 + 2 * ∑ h ∈ range H,
        ((H : ℝ) - h) * (eC (((h : ℝ) + 1) * x)).re := by
  induction H with
  | zero => simp [eC]
  | succ H ih =>
    rw [geometric_kernel_step, ih]
    have hs : (∑ h ∈ range (H + 1),
        (((H + 1 : ℕ) : ℝ) - h) * (eC (((h : ℝ) + 1) * x)).re) =
        (∑ h ∈ range H, ((H : ℝ) - h) * (eC (((h : ℝ) + 1) * x)).re) +
        ∑ h ∈ range (H + 1), (eC (((h : ℝ) + 1) * x)).re := by
      rw [sum_range_succ, sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      have he : (∑ h ∈ range H,
          (((H : ℝ) + 1) - h) * (eC (((h : ℝ) + 1) * x)).re) =
          (∑ h ∈ range H, ((H : ℝ) - h) * (eC (((h : ℝ) + 1) * x)).re) +
          ∑ h ∈ range H, (eC (((h : ℝ) + 1) * x)).re := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro h hh
        ring
      rw [he]
      ring
    rw [hs]
    push_cast
    ring

/-- P0082 page 359 Lemma 4, derived covering mesh for an interval.
The last mesh point is retained so endpoints require no special convention. -/
theorem mesh_cover (a b y T : ℝ) (hT : 0 < T) (hay : a ≤ y) (hyb : y ≤ b) :
    ∃ j ∈ range (⌈T * (b - a)⌉₊ + 1),
      0 ≤ y - (a + (j : ℝ) / T) ∧ y - (a + (j : ℝ) / T) ≤ 1 / T := by
  let j := ⌊T * (y - a)⌋₊
  have hy0 : 0 ≤ T * (y - a) := mul_nonneg hT.le (sub_nonneg.mpr hay)
  have hl : (j : ℝ) ≤ T * (y - a) := Nat.floor_le hy0
  have hu : T * (y - a) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hc : (j : ℝ) ≤ (⌈T * (b - a)⌉₊ : ℝ) :=
    hl.trans ((mul_le_mul_of_nonneg_left (by linarith : y - a ≤ b - a) hT.le).trans
      (Nat.le_ceil _))
  have hjc : j ≤ ⌈T * (b - a)⌉₊ := by exact_mod_cast hc
  refine ⟨j, mem_range.mpr (by omega), ?_, ?_⟩
  · have hj := (div_le_iff₀ hT).mpr (show (j : ℝ) ≤ (y - a) * T by nlinarith [hl])
    linarith
  · apply (le_div_iff₀ hT).mpr
    have he : (y - (a + (j : ℝ) / T)) * T = T * (y - a) - j := by
      field_simp; ring
    rw [he]
    linarith

/-- P0082 page 359 Lemma 4, derived size bound for the covering mesh. -/
theorem mesh_card_bound (a b T : ℝ) (hT : 0 ≤ T) (hab : a ≤ b) :
    ((range (⌈T * (b - a)⌉₊ + 1)).card : ℝ) ≤ T * (b - a) + 2 := by
  simp only [card_range, Nat.cast_add, Nat.cast_one]
  have hc := Nat.ceil_lt_add_one (mul_nonneg hT (sub_nonneg.mpr hab))
  linarith

/-- P0082 page 359 Lemma 4, derived integer periodicity of the phase. -/
theorem phase_int (k : ℤ) : eC (k : ℝ) = 1 := by
  unfold eC
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) =
    (k : ℂ) * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- P0082 page 359 Lemma 4, derived replacement by the fractional part at
integer frequencies. -/
theorem phase_fract (h : ℕ) (x : ℝ) :
    eC ((h : ℝ) * Int.fract x) = eC ((h : ℝ) * x) := by
  have he : (h : ℝ) * x = (h : ℝ) * Int.fract x + ((h : ℤ) * ⌊x⌋ : ℤ) := by
    simp only [Int.fract, Int.cast_mul, Int.cast_natCast]
    ring
  rw [he, phase_add, phase_int, mul_one]

/-- P0082 page 359 Lemma 4, derived finite Fourier polynomial for a sum of
translated positive kernels. The coefficient bound depends only on grid size. -/
theorem grid_polynomial (H : ℕ) (s : Finset ℕ) (t : ℕ → ℝ) :
    ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ = 4 * s.card / ((H : ℝ) + 1) ∧
      (∀ h ∈ range H, ‖c h‖ ≤ 8 * s.card / ((H : ℝ) + 1)) ∧
      ∀ x : ℝ, c₀ + ∑ h ∈ range H, (c h * eC (((h : ℝ) + 1) * x)).re =
        4 / ((H : ℝ) + 1) ^ 2 *
          ∑ j ∈ s, ‖∑ h ∈ range (H + 1), eC ((h : ℝ) * (x - t j))‖ ^ 2 := by
  let m : ℝ := (H : ℝ) + 1
  have hm : 0 < m := by dsimp [m]; positivity
  let c : ℕ → ℂ := fun h =>
    ((8 * ((H : ℝ) - h) / m ^ 2 : ℝ) : ℂ) *
      ∑ j ∈ s, eC (-(((h : ℝ) + 1) * t j))
  refine ⟨4 * s.card / m, c, rfl, ?_, ?_⟩
  · intro h hh
    have hhH : (h : ℝ) ≤ H := by exact_mod_cast (mem_range.mp hh).le
    have hcoef : 0 ≤ 8 * ((H : ℝ) - h) / m ^ 2 := by positivity
    have hs : ‖∑ j ∈ s, eC (-(((h : ℝ) + 1) * t j))‖ ≤ s.card := by
      calc
        _ ≤ ∑ j ∈ s, ‖eC (-(((h : ℝ) + 1) * t j))‖ := norm_sum_le _ _
        _ = _ := by simp only [LeanLab.ExceptionalSet.U1539.norm_eC, sum_const,
          nsmul_eq_mul, mul_one]
    dsimp [c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef]
    calc
      _ ≤ (8 * ((H : ℝ) - h) / m ^ 2) * s.card :=
        mul_le_mul_of_nonneg_left hs hcoef
      _ ≤ 8 * s.card / m := by
        apply (le_div_iff₀ hm).mpr
        have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
        have hs0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
        have hdm : (H : ℝ) - h ≤ m := by dsimp [m]; linarith
        have ha := mul_le_mul_of_nonneg_right hdm
          (by positivity : 0 ≤ 8 * (s.card : ℝ))
        field_simp
        nlinarith
  · intro x
    have hphase (h j : ℕ) :
        (eC (-(((h : ℝ) + 1) * t j)) * eC (((h : ℝ) + 1) * x)).re =
          (eC (((h : ℝ) + 1) * (x - t j))).re := by
      rw [← phase_add]
      congr 2
      ring
    have he (h : ℕ) :
        (c h * eC (((h : ℝ) + 1) * x)).re =
          (8 * ((H : ℝ) - h) / m ^ 2) *
            ∑ j ∈ s, (eC (((h : ℝ) + 1) * (x - t j))).re := by
      dsimp [c]
      rw [mul_assoc, sum_mul, Complex.re_ofReal_mul, Complex.re_sum]
      simp_rw [hphase]
    simp_rw [he]
    rw [Finset.mul_sum]
    simp_rw [geometric_kernel_expansion]
    have hc : 4 * (s.card : ℝ) / m = ∑ _j ∈ s, 4 / m := by simp; ring
    rw [hc]
    have hswap : (∑ h ∈ range H, (8 * ((H : ℝ) - h) / m ^ 2) *
        ∑ j ∈ s, (eC (((h : ℝ) + 1) * (x - t j))).re) =
        ∑ j ∈ s, ∑ h ∈ range H, (8 * ((H : ℝ) - h) / m ^ 2) *
          (eC (((h : ℝ) + 1) * (x - t j))).re := by
      simp_rw [Finset.mul_sum]
      rw [sum_comm]
    rw [hswap, ← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    have hs : (∑ h ∈ range H, (8 * ((H : ℝ) - h) / m ^ 2) *
        (eC (((h : ℝ) + 1) * (x - t j))).re) =
        8 / m ^ 2 * ∑ h ∈ range H, ((H : ℝ) - h) *
          (eC (((h : ℝ) + 1) * (x - t j))).re := by
      rw [mul_sum]
      apply sum_congr rfl
      intro h hh
      ring
    rw [hs]
    set q : ℝ := ∑ h ∈ range H, ((H : ℝ) - h) *
      (eC (((h : ℝ) + 1) * (x - t j))).re
    change 4 / m + 8 / m ^ 2 * q = 4 / m ^ 2 * (m + 2 * q)
    field_simp
    ring

/-- P0082 page 359 Lemma 4, derived one sided interval majorant.
A grid of positive squared geometric sums supplies the omitted finite construction.
The constant 128 is an auxiliary bound and is not printed in the paper. -/
theorem one_sided_majorant_supplied :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ) (H : ℕ),
      0 ≤ a → a ≤ b → b ≤ 1 → 1 ≤ H →
      ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
        c₀ ≤ C * (b - a + 1 / ((H : ℝ) + 1)) ∧
        (∀ h ∈ range H, ‖c h‖ ≤ C) ∧
        ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
          c₀ + ∑ h ∈ range H, (c h * eC (((h : ℝ) + 1) * x)).re := by
  classical
  refine ⟨128, by norm_num, fun a b H ha hab hb _hH => ?_⟩
  let m : ℝ := (H : ℝ) + 1
  have hm : 0 < m := by dsimp [m]; positivity
  have hm1 : 1 ≤ m := by dsimp [m]; have := Nat.cast_nonneg (α := ℝ) H; linarith
  let T : ℝ := 8 * m
  have hT : 0 < T := by dsimp [T]; positivity
  let s : Finset ℕ := range (⌈T * (b - a)⌉₊ + 1)
  let t : ℕ → ℝ := fun j => a + (j : ℝ) / T
  obtain ⟨c₀, c, hc₀, hc, hpoly⟩ := grid_polynomial H s t
  have hcard : (s.card : ℝ) ≤ 8 * m * (b - a) + 2 :=
    mesh_card_bound a b T hT.le hab
  have hi : 1 / m ≤ 1 := (div_le_iff₀ hm).mpr (by linarith)
  have hlen : b - a ≤ 1 := by linarith
  have hlen0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hconst : c₀ ≤ 32 * (b - a) + 8 / m := by
    rw [hc₀]
    apply (div_le_iff₀ hm).mpr
    have he : (32 * (b - a) + 8 / m) * m = 32 * m * (b - a) + 8 := by
      field_simp
    rw [he]
    nlinarith [hcard]
  refine ⟨c₀, c, hconst.trans ?_, ?_, ?_⟩
  · change 32 * (b - a) + 8 / m ≤ 128 * (b - a + 1 / m)
    have hi0 : 0 ≤ 1 / m := by positivity
    simp only [div_eq_mul_inv] at hi0 ⊢
    linarith
  · intro h hh
    have hcoeff := hc h hh
    change ‖c h‖ ≤ 8 * s.card / m at hcoeff
    apply hcoeff.trans
    have hbound : 8 * (s.card : ℝ) / m ≤ 64 * (b - a) + 16 / m := by
      apply (div_le_iff₀ hm).mpr
      have he : (64 * (b - a) + 16 / m) * m = 64 * m * (b - a) + 16 := by
        field_simp
      rw [he]
      nlinarith [hcard]
    simp only [div_eq_mul_inv] at hi hbound ⊢
    linarith
  · intro x
    rw [hpoly]
    change (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
      4 / m ^ 2 * ∑ j ∈ s, ‖∑ h ∈ range (H + 1), eC ((h : ℝ) * (x - t j))‖ ^ 2
    by_cases hband : a ≤ Int.fract x ∧ Int.fract x < b
    · rw [ite_eq_left hband]
      obtain ⟨j, hj, hj0, hj1⟩ := mesh_cover a b (Int.fract x) T hT hband.1 hband.2.le
      have hk := geometric_kernel_local H (Int.fract x - t j) hj0 hj1
      have hphase (h : ℕ) : eC ((h : ℝ) * (Int.fract x - t j)) =
          eC ((h : ℝ) * (x - t j)) := by
        rw [mul_sub, mul_sub, phase_sub, phase_sub, phase_fract]
      simp_rw [hphase] at hk
      have hsingle : ‖∑ h ∈ range (H + 1), eC ((h : ℝ) * (x - t j))‖ ^ 2 ≤
          ∑ j ∈ s, ‖∑ h ∈ range (H + 1), eC ((h : ℝ) * (x - t j))‖ ^ 2 :=
        single_le_sum (f := fun j =>
          ‖∑ h ∈ range (H + 1), eC ((h : ℝ) * (x - t j))‖ ^ 2)
          (fun j _ => sq_nonneg _) hj
      calc
        (1 : ℝ) = 4 / m ^ 2 * (m / 2) ^ 2 := by field_simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hk.trans hsingle) (by positivity)
    · rw [ite_eq_right hband]
      exact mul_nonneg (by positivity) (sum_nonneg (fun j _ => sq_nonneg _))

end LeanLab.ExceptionalSet.Decomp550a
