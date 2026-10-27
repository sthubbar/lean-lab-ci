/-
P0086 Basak, Bhat, Dong, Zaharescu 2024, arXiv 2409.08968 v1, Section 6, displays (6.14)-(6.17).
Unit U-1417, PC run 20261021T1203Z-6472. AI-written Lean code, Claude. Checked only by the
Lean kernel. Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.

Goal: `SingInt617 B` of `Major618SW.lean`, unconditionally, for every `B`.

Plain math. Let `F(β) = T(β)³ e(-mβ)`, `T(β) = Σ_{u ≤ k ≤ 2u} e(kβ)`, `δ = (log u)^B / u`.
* `F` has period 1, so `∫_{-1/2}^{1/2} F = ∫_0^1 F`, which is the triple count `N(m,u)` by
  `tint_count` (6.15).
* `|T(β)| ≤ 1/(2|β|)` for `0 < |β| ≤ 1/2`: geometric sum and `|sin πβ| ≥ 2|β|`.
  So each tail `∫_{δ < |β| ≤ 1/2} |F|` is at most `∫_δ^{1/2} β⁻³/8 ≤ 1/(16 δ²)`.
* `|N(m,u) - H(m,u)| ≤ 12u` for `u ≥ 1`, `4u ≤ m ≤ 5u`: the inner count over `k₂, k₃` is
  `max(0, min(b, m-k₁-a) + 1 - max(a, m-k₁-b))`, within 3 of the 2-Lipschitz profile
  `f(x) = max(0, min(2u, m-x-u) - max(u, m-x-2u))`; the sum of `f` over integers is within
  `2(u+1) + 2u` of `∫_u^{2u} f`, and `∫_u^{2u} f = H(m,u)` exactly.
* So `|J(m,u,δ) - H(m,u)| ≤ 12u + 1/(8δ²) = 12u + u²(log u)^{-2B}/8 ≤ 2u²(log u)^{-2B}`
  once `12 (log u)^{2B} ≤ u`.
-/
import Mathlib
import LeanLab.SparseTernary.Major618SW

open Finset Filter Real MeasureTheory
open scoped Classical

noncomputable section
namespace LeanLab.SparseTernary.SingInt617Proof

open LeanLab.SparseTernary LeanLab.SparseTernary.Section4 LeanLab.SparseTernary.MajorArcs
open LeanLab.SparseTernary.LocalFactors LeanLab.SparseTernary.Tail72Proof
open LeanLab.SparseTernary.Major618SW

/-! ### The bound `|T(β)| ≤ 1/(2|β|)` -/

theorem sin_lower (β : ℝ) (h0 : 0 < |β|) (h1 : |β| ≤ 1 / 2) :
    2 * |β| ≤ |Real.sin (π * β)| := by
  have hp := Real.pi_pos
  have key : 2 * |β| ≤ Real.sin (π * |β|) := by
    have := Real.mul_le_sin (x := π * |β|) (by positivity) (by nlinarith)
    calc 2 * |β| = 2 / π * (π * |β|) := by field_simp
      _ ≤ _ := this
  rcases le_or_gt 0 β with hb | hb
  · rw [abs_of_nonneg hb] at key ⊢; exact key.trans (le_abs_self _)
  · rw [abs_of_neg hb] at key ⊢
    rw [show π * β = -(π * -β) by ring, Real.sin_neg, abs_neg]
    exact key.trans (le_abs_self _)

theorem norm_ee_sub_one (β : ℝ) : ‖ee β - 1‖ = 2 * |Real.sin (π * β)| := by
  have : ee β = Complex.exp (Complex.I * ((2 * π * β : ℝ) : ℂ)) := by
    unfold ee; congr 1; push_cast; ring
  rw [this, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    show 2 * π * β / 2 = π * β by ring]
  norm_num

theorem Icc_eq_Ico (a b : ℕ) : Icc a b = Ico a (b + 1) := by
  ext x; simp only [mem_Icc, mem_Ico]; omega

theorem norm_Tsum_le (u β : ℝ) (h0 : 0 < |β|) (h1 : |β| ≤ 1 / 2) :
    ‖Tsum u β‖ ≤ 1 / (2 * |β|) := by
  have hs := sin_lower β h0 h1
  have hx : ee β ≠ 1 := by
    intro h
    have := norm_ee_sub_one β
    rw [h, sub_self, norm_zero] at this
    linarith
  have hexp : Tsum u β = ee (⌈u⌉₊ * β) *
      ∑ i ∈ range (⌊2 * u⌋₊ + 1 - ⌈u⌉₊), ee β ^ i := by
    unfold Tsum Iu
    rw [Icc_eq_Ico, Finset.sum_Ico_eq_sum_range, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← ee_nat_mul, ← ee_add]; congr 1; push_cast; ring
  rw [hexp, geom_sum_eq hx, norm_mul, norm_ee, one_mul, norm_div, norm_ee_sub_one]
  have hnum : ‖ee β ^ (⌊2 * u⌋₊ + 1 - ⌈u⌉₊) - 1‖ ≤ 2 := by
    calc _ ≤ ‖ee β ^ (⌊2 * u⌋₊ + 1 - ⌈u⌉₊)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_ee]; norm_num
  have hpos : 0 < 2 * |β| := by linarith
  rw [div_le_div_iff₀ (by linarith) hpos]
  nlinarith [norm_nonneg (ee β ^ (⌊2 * u⌋₊ + 1 - ⌈u⌉₊) - 1)]

/-! ### The tail integrals -/

theorem tail_bound (G : ℝ → ℂ) (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hG : ∀ t, δ < t → t ≤ 1 / 2 → ‖G t‖ ≤ 1 / 8 * t ^ (-3 : ℤ)) :
    ‖∫ t in δ..(1 / 2), G t‖ ≤ 1 / (16 * δ ^ 2) := by
  have hnot : (0 : ℝ) ∉ Set.uIcc δ (1 / 2) := by
    rw [Set.uIcc_of_le hδ2]; intro h; linarith [h.1]
  have hint : IntervalIntegrable (fun t : ℝ => 1 / 8 * t ^ (-3 : ℤ)) volume δ (1 / 2) :=
    (intervalIntegral.intervalIntegrable_zpow (Or.inr hnot)).const_mul _
  refine (intervalIntegral.norm_integral_le_of_norm_le hδ2
    (Filter.Eventually.of_forall fun t ht => hG t ht.1 ht.2) hint).trans ?_
  rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, hnot⟩)]
  have e : ((-3 : ℤ) + 1) = -2 := by norm_num
  rw [e]
  have k : 1 / 8 * (((1 / 2 : ℝ) ^ (-2 : ℤ) - δ ^ (-2 : ℤ)) / (((-3 : ℤ) : ℝ) + 1)) =
      1 / (16 * δ ^ 2) - 1 / 4 := by
    rw [zpow_neg, zpow_neg, zpow_two, zpow_two]
    field_simp
    push_cast
    ring
  rw [k]; linarith

/-! ### The lattice count against `H(m,u)` -/

/-- The continuous profile: the length of `{k₂ ∈ [u,2u] : m - x - k₂ ∈ [u,2u]}`. -/
def fu (u m x : ℝ) : ℝ := max (min (2 * u) (m - x - u) - max u (m - x - 2 * u)) 0

theorem fu_cont (u m : ℝ) : Continuous (fu u m) := by unfold fu; fun_prop

theorem fu_lip (u m x y : ℝ) : |fu u m x - fu u m y| ≤ 2 * |x - y| := by
  unfold fu
  have e1 := abs_max_sub_max_le_abs (min (2 * u) (m - x - u) - max u (m - x - 2 * u))
    (min (2 * u) (m - y - u) - max u (m - y - 2 * u)) 0
  have e2 := abs_min_sub_min_le_max (2 * u) (m - x - u) (2 * u) (m - y - u)
  have e3 := abs_max_sub_max_le_max u (m - x - 2 * u) u (m - y - 2 * u)
  rw [sub_self, abs_zero, show m - x - u - (m - y - u) = -(x - y) by ring, abs_neg,
    max_eq_right (abs_nonneg (x - y))] at e2
  rw [sub_self, abs_zero, show m - x - 2 * u - (m - y - 2 * u) = -(x - y) by ring, abs_neg,
    max_eq_right (abs_nonneg (x - y))] at e3
  refine e1.trans ?_
  rw [abs_le] at e2 e3 ⊢
  constructor <;> linarith [e2.1, e2.2, e3.1, e3.2]

theorem fu_nonneg (u m x : ℝ) : 0 ≤ fu u m x := le_max_right _ _

theorem fu_le (u m x : ℝ) (hu : 0 ≤ u) : fu u m x ≤ u := by
  unfold fu
  refine max_le ?_ hu
  linarith [min_le_left (2 * u) (m - x - u), le_max_left u (m - x - 2 * u)]

theorem integral_fu (u m : ℝ) (h1 : 4 * u ≤ m) (h2 : m ≤ 5 * u) :
    ∫ x in u..(2 * u), fu u m x = Hmu m u := by
  have hc1 : u ≤ m - 3 * u := by linarith
  have hc2 : m - 3 * u ≤ 2 * u := by linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := m - 3 * u)
    ((fu_cont u m).intervalIntegrable _ _) ((fu_cont u m).intervalIntegrable _ _)]
  have e1 : ∫ x in u..(m - 3 * u), fu u m x = ∫ x in u..(m - 3 * u), (x + (4 * u - m)) := by
    apply intervalIntegral.integral_congr
    intro x hx; rw [Set.uIcc_of_le hc1] at hx
    simp only [fu]
    rw [min_eq_left (show 2 * u ≤ m - x - u by linarith [hx.2]),
      max_eq_right (show u ≤ m - x - 2 * u by linarith [hx.2]),
      max_eq_left (show 0 ≤ 2 * u - (m - x - 2 * u) by linarith [hx.1])]
    ring
  have e2 : ∫ x in (m - 3 * u)..(2 * u), fu u m x =
      ∫ x in (m - 3 * u)..(2 * u), ((m - 2 * u) - x) := by
    apply intervalIntegral.integral_congr
    intro x hx; rw [Set.uIcc_of_le hc2] at hx
    simp only [fu]
    rw [min_eq_right (show m - x - u ≤ 2 * u by linarith [hx.1]),
      max_eq_left (show m - x - 2 * u ≤ u by linarith [hx.1]),
      max_eq_left (show 0 ≤ m - x - u - u by linarith [hx.2])]
    ring
  rw [e1, e2, intervalIntegral.integral_add (continuous_id'.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (continuous_id'.intervalIntegrable _ _),
    integral_id, integral_id, intervalIntegral.integral_const, intervalIntegral.integral_const]
  unfold Hmu
  simp only [smul_eq_mul]
  ring

theorem inner_count (a b k₁ m : ℕ) :
    ∑ k₂ ∈ Icc a b, ∑ k₃ ∈ Icc a b, (if k₁ + k₂ + k₃ = m then (1 : ℝ) else 0) =
      max (min (b : ℝ) ((m : ℝ) - k₁ - a) + 1 - max (a : ℝ) ((m : ℝ) - k₁ - b)) 0 := by
  have h1 : ∀ k₂ ∈ Icc a b, ∑ k₃ ∈ Icc a b, (if k₁ + k₂ + k₃ = m then (1 : ℝ) else 0) =
      if ((a : ℤ) ≤ (m : ℤ) - k₁ - k₂ ∧ (m : ℤ) - k₁ - k₂ ≤ b) then 1 else 0 := by
    intro k₂ _
    split_ifs with hc
    · rw [Finset.sum_eq_single (m - k₁ - k₂)]
      · rw [if_pos (by omega)]
      · intro k₃ _ hne; rw [if_neg (by omega)]
      · intro hn; exfalso; apply hn; simp only [mem_Icc]; omega
    · refine sum_eq_zero fun k₃ hk₃ => ?_
      rw [mem_Icc] at hk₃; rw [if_neg (by omega)]
  rw [sum_congr rfl h1, sum_boole]
  have h2 : #((Icc a b).filter
      (fun k₂ : ℕ => (a : ℤ) ≤ (m : ℤ) - k₁ - k₂ ∧ (m : ℤ) - k₁ - k₂ ≤ b)) =
      #(Icc (max (a : ℤ) ((m : ℤ) - k₁ - b)) (min (b : ℤ) ((m : ℤ) - k₁ - a))) := by
    apply Finset.card_bij (fun (k : ℕ) _ => (k : ℤ))
    · intro k hk; simp only [mem_filter, mem_Icc] at hk ⊢; omega
    · intro x _ y _ h; exact_mod_cast h
    · intro z hz; simp only [mem_Icc] at hz
      refine ⟨z.toNat, ?_, ?_⟩
      · simp only [mem_filter, mem_Icc]; omega
      · omega
  rw [h2, Int.card_Icc]
  have h3 : ∀ z : ℤ, ((z.toNat : ℕ) : ℝ) = max (z : ℝ) 0 := by
    intro z
    have : ((z.toNat : ℕ) : ℤ) = max z 0 := Int.toNat_eq_max z
    rw [show ((z.toNat : ℕ) : ℝ) = (((z.toNat : ℕ) : ℤ) : ℝ) by norm_cast, this]
    push_cast; rfl
  rw [h3]
  push_cast
  rfl

theorem inner_dev (u : ℝ) (a b k₁ m : ℕ) (ha1 : u ≤ a) (ha2 : (a : ℝ) ≤ u + 1)
    (hb1 : 2 * u - 1 ≤ b) (hb2 : (b : ℝ) ≤ 2 * u) :
    |max (min (b : ℝ) ((m : ℝ) - k₁ - a) + 1 - max (a : ℝ) ((m : ℝ) - k₁ - b)) 0 -
      fu u m k₁| ≤ 3 := by
  unfold fu
  refine (abs_max_sub_max_le_abs _ _ 0).trans ?_
  have e2 := abs_min_sub_min_le_max (b : ℝ) ((m : ℝ) - k₁ - a) (2 * u) ((m : ℝ) - k₁ - u)
  have e3 := abs_max_sub_max_le_max (a : ℝ) ((m : ℝ) - k₁ - b) u ((m : ℝ) - k₁ - 2 * u)
  have f1 : |(b : ℝ) - 2 * u| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have f2 : |(m : ℝ) - k₁ - a - (m - k₁ - u)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have f3 : |(a : ℝ) - u| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have f4 : |(m : ℝ) - k₁ - b - (m - k₁ - 2 * u)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have g2 := e2.trans (max_le f1 f2)
  have g3 := e3.trans (max_le f3 f4)
  rw [abs_le] at g2 g3 ⊢
  constructor <;> linarith [g2.1, g2.2, g3.1, g3.2]

theorem sum_sub_integral (f : ℝ → ℝ) (hf : Continuous f) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|) (a : ℝ) (n : ℕ) :
    |∑ i ∈ range n, f (a + i) - ∫ x in a..(a + n), f x| ≤ L * n := by
  have hadj := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
    (a := fun k : ℕ => a + k) (n := n) (fun k _ => hf.intervalIntegrable _ _)
  simp only [Nat.cast_zero, add_zero] at hadj
  rw [← hadj, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i ∈ range n,
      |f (a + i) - ∫ x in (a + (i : ℕ))..(a + ((i + 1 : ℕ) : ℝ)), f x| ≤ L := by
    intro i _
    have hlen : a + ((i + 1 : ℕ) : ℝ) - (a + i) = 1 := by push_cast; ring
    have : f (a + i) - ∫ x in (a + (i : ℕ))..(a + ((i + 1 : ℕ) : ℝ)), f x =
        ∫ x in (a + (i : ℕ))..(a + ((i + 1 : ℕ) : ℝ)), (f (a + i) - f x) := by
      rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
        (hf.intervalIntegrable _ _), intervalIntegral.integral_const, hlen, one_smul]
    rw [this, ← Real.norm_eq_abs]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a + (i : ℕ)) (b := a + ((i + 1 : ℕ) : ℝ)) (C := L)
      (f := fun x => f (a + i) - f x) (fun x hx => by
        rw [Set.uIoc_of_le (by linarith)] at hx
        rw [Real.norm_eq_abs]
        have h1 : |a + i - x| ≤ 1 := by
          rw [abs_le]; push_cast at hx; constructor <;> linarith [hx.1, hx.2]
        calc |f (a + i) - f x| ≤ L * |a + i - x| := hlip _ _
          _ ≤ L * 1 := mul_le_mul_of_nonneg_left h1 hL
          _ = L := mul_one L)
    rw [hlen, abs_one, mul_one] at hb
    exact hb
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul, mul_comm]

theorem count_sub_H (u : ℝ) (m : ℕ) (hu : 1 ≤ u) (hm1 : 4 * u ≤ m) (hm2 : (m : ℝ) ≤ 5 * u) :
    |∑ k₁ ∈ Iu u, ∑ k₂ ∈ Iu u, ∑ k₃ ∈ Iu u, (if k₁ + k₂ + k₃ = m then (1 : ℝ) else 0) -
      Hmu m u| ≤ 12 * u := by
  have ha1 : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
  have ha2 : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one (by linarith)
  have hb1 : (⌊2 * u⌋₊ : ℝ) ≤ 2 * u := Nat.floor_le (by linarith)
  have hb2 : 2 * u < (⌊2 * u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  unfold Iu
  set a := ⌈u⌉₊ with ha
  set b := ⌊2 * u⌋₊ with hb
  have hab : a ≤ b + 1 := by exact_mod_cast (show (a : ℝ) ≤ b + 1 by linarith)
  have hn : ((b + 1 - a : ℕ) : ℝ) = b + 1 - a := by
    rw [Nat.cast_sub hab]; push_cast; ring
  -- step 1: inner counts
  rw [sum_congr rfl fun k₁ _ => inner_count a b k₁ m]
  -- step 2: compare with the profile at integers
  have hdev : |∑ k₁ ∈ Icc a b,
      max (min (b : ℝ) ((m : ℝ) - k₁ - a) + 1 - max (a : ℝ) ((m : ℝ) - k₁ - b)) 0 -
      ∑ k₁ ∈ Icc a b, fu u m k₁| ≤ 3 * (b + 1 - a) := by
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum fun k₁ _ =>
      inner_dev u a b k₁ m ha1 ha2.le (by linarith) hb1).trans ?_
    rw [sum_const, Icc_eq_Ico, Nat.card_Ico, nsmul_eq_mul, hn, mul_comm]
  -- step 3: sum against integral
  have hsum : ∑ k₁ ∈ Icc a b, fu u m k₁ = ∑ i ∈ range (b + 1 - a), fu u m ((a : ℝ) + i) := by
    rw [Icc_eq_Ico, Finset.sum_Ico_eq_sum_range]
    refine sum_congr rfl fun i _ => ?_
    push_cast; rfl
  have hsi := sum_sub_integral (fu u m) (fu_cont u m) 2 (by norm_num) (fu_lip u m) a (b + 1 - a)
  rw [hn, show (a : ℝ) + (b + 1 - a) = b + 1 by ring] at hsi
  -- step 4: integral over [a, b+1] against [u, 2u]
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hsmall : ∀ x y : ℝ, |x - y| ≤ 1 → |∫ t in x..y, fu u m t| ≤ u := by
    intro x y hxy
    rw [← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := u) fun t _ => ?_).trans ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (fu_nonneg u m t)]; exact fu_le u m t hu0
    · rw [abs_sub_comm]; nlinarith
  have hsplit : ∫ t in u..(2 * u), fu u m t = (∫ t in u..(a : ℝ), fu u m t) +
      (∫ t in (a : ℝ)..((b : ℝ) + 1), fu u m t) + ∫ t in ((b : ℝ) + 1)..(2 * u), fu u m t := by
    rw [intervalIntegral.integral_add_adjacent_intervals ((fu_cont u m).intervalIntegrable _ _)
        ((fu_cont u m).intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals ((fu_cont u m).intervalIntegrable _ _)
        ((fu_cont u m).intervalIntegrable _ _)]
  have hs1 := hsmall u a (by rw [abs_le]; constructor <;> linarith)
  have hs2 := hsmall ((b : ℝ) + 1) (2 * u) (by rw [abs_le]; constructor <;> linarith)
  have hH := integral_fu u m hm1 hm2
  rw [hsplit] at hH
  rw [← hsum] at hsi
  have hnb : (b : ℝ) + 1 - a ≤ u + 1 := by linarith
  rw [abs_le] at hdev hsi hs1 hs2 ⊢
  constructor <;> nlinarith [hdev.1, hdev.2, hsi.1, hsi.2, hs1.1, hs1.2, hs2.1, hs2.2]

/-! ### `|J(m,u,δ) - H(m,u)| ≤ 12u + 1/(8δ²)` -/

theorem J_sub_H (u δ : ℝ) (m : ℕ) (hu : 1 ≤ u) (hm1 : 4 * u ≤ m) (hm2 : (m : ℝ) ≤ 5 * u)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ‖Jint m u δ - (Hmu m u : ℂ)‖ ≤ 12 * u + 1 / (8 * δ ^ 2) := by
  set FF : ℝ → ℂ := fun β => Tsum u β ^ 3 * ee (-(m * β)) with hFF
  have hcont : Continuous FF := by rw [hFF]; unfold Tsum; fun_prop
  have hper : Function.Periodic FF 1 := by
    intro β
    have hT : Tsum u (β + 1) = Tsum u β := by
      unfold Tsum; refine sum_congr rfl fun k _ => ?_
      rw [show (k : ℝ) * (β + 1) = k * β + ((k : ℤ) : ℝ) by push_cast; ring, ee_add, ee_int,
        mul_one]
    have hm : ee (-(m * (β + 1))) = ee (-(m * β)) := by
      rw [show -((m : ℝ) * (β + 1)) = -(m * β) + ((-(m : ℤ) : ℤ) : ℝ) by push_cast; ring,
        ee_add, ee_int, mul_one]
    simp only [hFF, hT, hm]
  have hfull : ∫ β in (-(1 / 2) : ℝ)..(1 / 2), FF β = ∫ β in (0 : ℝ)..1, FF β := by
    have := hper.intervalIntegral_add_eq (-(1 / 2)) 0
    rw [show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num, zero_add] at this
    exact this
  have hcnt : ∫ β in (0 : ℝ)..1, FF β = ((∑ k₁ ∈ Iu u, ∑ k₂ ∈ Iu u, ∑ k₃ ∈ Iu u,
      (if k₁ + k₂ + k₃ = m then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    rw [hFF, tint_count]
    simp only [Complex.ofReal_sum]
    refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => ?_
    split_ifs <;> simp
  set cnt := ∑ k₁ ∈ Iu u, ∑ k₂ ∈ Iu u, ∑ k₃ ∈ Iu u,
      (if k₁ + k₂ + k₃ = m then (1 : ℝ) else 0) with hcntdef
  have hs1 := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (-(1 / 2)) (-δ))
    (hcont.intervalIntegrable (μ := volume) (-δ) (1 / 2))
  have hs2 := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (-δ) δ)
    (hcont.intervalIntegrable (μ := volume) δ (1 / 2))
  have hneg : ∫ β in (-(1 / 2) : ℝ)..(-δ), FF β = ∫ t in δ..(1 / 2), FF (-t) :=
    (intervalIntegral.integral_comp_neg (a := δ) (b := 1 / 2) (f := FF)).symm
  have hJ : Jint m u δ = ∫ β in (-δ)..δ, FF β := rfl
  have key : (cnt : ℂ) = (∫ t in δ..(1 / 2), FF (-t)) + Jint m u δ +
      ∫ t in δ..(1 / 2), FF t := by
    rw [← hcnt, ← hfull, ← hs1, ← hs2, hneg, hJ]; ring
  have hFFb : ∀ β : ℝ, 0 < |β| → |β| ≤ 1 / 2 → ‖FF β‖ ≤ 1 / 8 * |β| ^ (-3 : ℤ) := by
    intro β h0 h1
    simp only [hFF]
    rw [norm_mul, norm_ee, mul_one, norm_pow]
    have hT := norm_Tsum_le u β h0 h1
    calc ‖Tsum u β‖ ^ 3 ≤ (1 / (2 * |β|)) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hT 3
      _ = 1 / 8 * |β| ^ (-3 : ℤ) := by rw [zpow_neg, zpow_ofNat]; field_simp; ring
  have T1 := tail_bound (fun t => FF (-t)) δ hδ hδ2 fun t h1 h2 => by
    have ht : 0 < t := by linarith
    have := hFFb (-t) (by rw [abs_neg, abs_of_pos ht]; exact ht)
      (by rw [abs_neg, abs_of_pos ht]; exact h2)
    rwa [abs_neg, abs_of_pos ht] at this
  have T3 := tail_bound FF δ hδ hδ2 fun t h1 h2 => by
    have ht : 0 < t := by linarith
    have := hFFb t (by rw [abs_of_pos ht]; exact ht) (by rw [abs_of_pos ht]; exact h2)
    rwa [abs_of_pos ht] at this
  have hC := count_sub_H u m hu hm1 hm2
  rw [← hcntdef] at hC
  have hdiff : Jint m u δ - (Hmu m u : ℂ) = ((cnt - Hmu m u : ℝ) : ℂ) -
      (∫ t in δ..(1 / 2), FF (-t)) - ∫ t in δ..(1 / 2), FF t := by
    push_cast; rw [key]; ring
  rw [hdiff]
  have hn1 : ‖((cnt - Hmu m u : ℝ) : ℂ)‖ ≤ 12 * u := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hC
  calc _ ≤ ‖((cnt - Hmu m u : ℝ) : ℂ) - (∫ t in δ..(1 / 2), FF (-t))‖ +
        ‖∫ t in δ..(1 / 2), FF t‖ := norm_sub_le _ _
    _ ≤ (‖((cnt - Hmu m u : ℝ) : ℂ)‖ + ‖∫ t in δ..(1 / 2), FF (-t)‖) +
        ‖∫ t in δ..(1 / 2), FF t‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ (12 * u + 1 / (16 * δ ^ 2)) + 1 / (16 * δ ^ 2) := by gcongr
    _ = 12 * u + 1 / (8 * δ ^ 2) := by field_simp; ring

/-! ### `SingInt617 B`, PROVED -/

theorem ev_bound (B : ℕ) : ∃ u1 : ℝ, ∀ u ≥ u1, 12 * Real.log u ^ (2 * B) ≤ u := by
  have h := isLittleO_log_rpow_rpow_atTop ((2 * B : ℕ) : ℝ) (zero_lt_one' ℝ)
  have h2 := h.bound (show (0 : ℝ) < 1 / 12 by norm_num)
  obtain ⟨u1, hu1⟩ := Filter.eventually_atTop.mp (h2.and (Filter.eventually_gt_atTop 0))
  refine ⟨u1, fun u hu => ?_⟩
  obtain ⟨h3, h4⟩ := hu1 u hu
  rw [Real.rpow_natCast, Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos h4] at h3
  have := le_abs_self (Real.log u ^ (2 * B))
  linarith

/-- **`SingInt617 B`, PROVED for every `B`**: for `u ≥ u₀(B)` and `4u ≤ m ≤ 5u`,
`|J(m, u, (log u)^B/u) - H(m,u)| ≤ 2 u² (log u)^{-2B}`. -/
theorem singInt617 (B : ℕ) : SingInt617 B := by
  obtain ⟨u1, hu1⟩ := ev_bound B
  refine ⟨2, max u1 (Real.exp 1), fun u hu m hm1 hm2 => ?_⟩
  have hue : Real.exp 1 ≤ u := le_trans (le_max_right _ _) hu
  have hL : 1 ≤ Real.log u := by
    have := Real.log_le_log (Real.exp_pos 1) hue; rwa [Real.log_exp] at this
  have hu1' : 1 ≤ u := le_trans (by have := Real.add_one_le_exp (1 : ℝ); linarith) hue
  have hu0 : 0 < u := by linarith
  have hev := hu1 u (le_trans (le_max_left _ _) hu)
  have hLB : Real.log u ^ B ≤ Real.log u ^ (2 * B) := pow_le_pow_right₀ hL (by omega)
  have hP : 0 < Real.log u ^ B := by positivity
  have h2B : Real.log u ^ (2 * B) = (Real.log u ^ B) ^ 2 := by rw [← pow_mul, mul_comm]
  have hδ : 0 < Real.log u ^ B / u := by positivity
  have hδ2 : Real.log u ^ B / u ≤ 1 / 2 := by
    rw [div_le_iff₀ hu0]; nlinarith
  have hmain := J_sub_H u (Real.log u ^ B / u) m hu1' hm1 hm2 hδ hδ2
  have hrp : Real.log u ^ (-(2 * (B : ℝ))) = (Real.log u ^ (2 * B))⁻¹ := by
    rw [Real.rpow_neg (by linarith), show (2 * (B : ℝ)) = ((2 * B : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [hrp]
  refine hmain.trans ?_
  rw [h2B] at hev ⊢
  set P := Real.log u ^ B with hPdef
  have k1 : 1 / (8 * (P / u) ^ 2) = u ^ 2 / P ^ 2 / 8 := by field_simp
  have k2 : 12 * u ≤ u ^ 2 / P ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have k3 : 2 * u ^ 2 * (P ^ 2)⁻¹ = 2 * (u ^ 2 / P ^ 2) := by ring
  have k4 : 0 ≤ u ^ 2 / P ^ 2 := by positivity
  rw [k1, k3]; linarith

/-! ### Consequences -/

/-- **`Major618 A B` for `15A ≤ B`, CONDITIONAL ON `SW (B + 3A + 1)` and `Expand613 A B`
only**: `SingInt617 B` is now discharged by `singInt617`. -/
theorem major618_of_SW_Expand (A B : ℕ) (hB : 15 * A ≤ B) (hSW : SW ((B : ℝ) + 3 * A + 1))
    (hE : Expand613 A B) : Major618 A B :=
  major618_of_SW A B hB hSW hE (singInt617 B)

/-- **RepProp A, CONDITIONAL ON `Minor516W A B`, `SW (B + 3A + 1)` and `Expand613 A B`
only**, for `A ≥ 1`, `B ≥ 36A + 3`, `B ≥ 28A + 13`. -/
theorem repProp_of_SW_Expand (A B : ℕ) (hA : 1 ≤ A) (hB1 : 36 * A + 3 ≤ B)
    (hB2 : 28 * A + 13 ≤ B) (hmin : RepAssembly.Minor516W A B)
    (hSW : SW ((B : ℝ) + 3 * A + 1)) (hE : Expand613 A B) : RepProp A :=
  repProp_of_SW A B hA hB1 hB2 hmin hSW hE (singInt617 B)

end LeanLab.SparseTernary.SingInt617Proof

#print axioms LeanLab.SparseTernary.SingInt617Proof.sin_lower
#print axioms LeanLab.SparseTernary.SingInt617Proof.norm_ee_sub_one
#print axioms LeanLab.SparseTernary.SingInt617Proof.Icc_eq_Ico
#print axioms LeanLab.SparseTernary.SingInt617Proof.norm_Tsum_le
#print axioms LeanLab.SparseTernary.SingInt617Proof.tail_bound
#print axioms LeanLab.SparseTernary.SingInt617Proof.fu_cont
#print axioms LeanLab.SparseTernary.SingInt617Proof.fu_lip
#print axioms LeanLab.SparseTernary.SingInt617Proof.fu_nonneg
#print axioms LeanLab.SparseTernary.SingInt617Proof.fu_le
#print axioms LeanLab.SparseTernary.SingInt617Proof.integral_fu
#print axioms LeanLab.SparseTernary.SingInt617Proof.inner_count
#print axioms LeanLab.SparseTernary.SingInt617Proof.inner_dev
#print axioms LeanLab.SparseTernary.SingInt617Proof.sum_sub_integral
#print axioms LeanLab.SparseTernary.SingInt617Proof.count_sub_H
#print axioms LeanLab.SparseTernary.SingInt617Proof.J_sub_H
#print axioms LeanLab.SparseTernary.SingInt617Proof.ev_bound
#print axioms LeanLab.SparseTernary.SingInt617Proof.singInt617
#print axioms LeanLab.SparseTernary.SingInt617Proof.major618_of_SW_Expand
#print axioms LeanLab.SparseTernary.SingInt617Proof.repProp_of_SW_Expand
