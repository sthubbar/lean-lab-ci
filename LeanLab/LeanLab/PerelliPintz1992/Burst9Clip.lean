/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372, Section 5, p. 364.

ROUTE BURST session 9, 2026-11-12. Toward `clip_average_proved`, the
end averaging of the clipped window sum, the route of `Decomp1624.reduction27A` and the
second term of `Decomp1624.WA`. This file holds the pointwise facts about the moving sum
`Decomp1624.movingSum` and Gallagher's clipped window sum, all PROVED.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Burst9Leaves

namespace LeanLab.PerelliPintz1992.Burst9
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624
open LeanLab.PerelliPintz1992.Burst8P2

noncomputable section
attribute [local instance] Classical.propDecidable

variable {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))

theorem movingSum_eq (x u : ℝ) :
    movingSum χ x u = ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + u⌋₊, cf χ n := rfl

/-- The moving sum is jointly measurable in the start and the window. PROVED. -/
theorem movingSum_measurable : Measurable (fun p : ℝ × ℝ => movingSum χ p.1 p.2) := by
  have h1 : Measurable (fun p : ℝ × ℝ => (⌈p.1⌉₊, ⌊p.1 + p.2⌋₊)) :=
    (measurable_fst.nat_ceil).prodMk ((measurable_fst.add measurable_snd).nat_floor)
  have h2 : Measurable (fun mn : ℕ × ℕ => ∑ n ∈ Finset.Icc mn.1 mn.2, cf χ n) :=
    measurable_of_countable _
  exact h2.comp h1

theorem norm_cf_le (n : ℕ) : ‖cf χ n‖ ≤ Λ n + 1 := by
  unfold cf
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖(Λ n : ℂ) * χ (n : ZMod (q : ℕ))‖ ≤ Λ n := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg (DirichletCharacter.norm_le_one _ _)
  have h2 : ‖(if χ = 1 then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
  exact add_le_add h1 h2

theorem norm_cf_le_log {N n : ℕ} (hN : 1 ≤ N) (hn : n ≤ 2 * N) :
    ‖cf χ n‖ ≤ Real.log (2 * N) + 1 := by
  refine (norm_cf_le χ n).trans ?_
  have : Λ n ≤ Real.log (2 * N) := by
    refine vonMangoldt_le_log.trans ?_
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by have : (1 : ℝ) ≤ N := by exact_mod_cast hN
                                linarith)
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hn)
  linarith

/-- A uniform bound for the moving sums with `x + u ≤ R`. PROVED. -/
theorem norm_movingSum_le (R : ℝ) {x u : ℝ} (h : x + u ≤ R) :
    ‖movingSum χ x u‖ ≤ ∑ n ∈ Finset.range (⌊R⌋₊ + 1), ‖cf χ n‖ := by
  rw [movingSum_eq]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => norm_nonneg _)
  intro n hn
  have := (Finset.mem_Icc.mp hn).2
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (this.trans (Nat.floor_le_floor h)))

/-- The left end: for `x ∈ (a - 1, a]` the moving sum at `x` with window `u' + (a - x)` is the
moving sum at `a` with window `u'`. PROVED. -/
theorem movingSum_shift_left {a : ℕ} (ha : 1 ≤ a) {x : ℝ} (hx1 : (a : ℝ) - 1 < x)
    (hx2 : x ≤ a) (u' : ℝ) : movingSum χ x (u' + (a - x)) = movingSum χ a u' := by
  rw [movingSum_eq, movingSum_eq, Nat.ceil_natCast]
  have hc : ⌈x⌉₊ = a := by
    rw [Nat.ceil_eq_iff (by omega)]
    constructor
    · push_cast [Nat.cast_sub ha]; linarith
    · exact hx2
  rw [hc, show x + (u' + (a - x)) = (a : ℝ) + u' by ring]

/-- The top unit of windows: `S(a, u) = S(a, u - 1) + c(a + ⌊u⌋)` for `u ≥ 1`. PROVED. -/
theorem movingSum_top (a : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    movingSum χ a u = movingSum χ a (u - 1) + cf χ (a + ⌊u⌋₊) := by
  rw [movingSum_eq, movingSum_eq, Nat.ceil_natCast]
  have h0 : (0 : ℝ) ≤ u := by linarith
  have e1 : ⌊(a : ℝ) + u⌋₊ = a + ⌊u⌋₊ := by
    rw [add_comm, Nat.floor_add_natCast h0, add_comm]
  have e2 : ⌊(a : ℝ) + (u - 1)⌋₊ = a + ⌊u⌋₊ - 1 := by
    rw [show (a : ℝ) + (u - 1) = ((a : ℝ) + u) - 1 by ring, Nat.floor_sub_one, e1]
  have hu1 : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by exact_mod_cast hu)
  rw [e1, e2]
  obtain ⟨m, hm⟩ : ∃ m, ⌊u⌋₊ = m + 1 := ⟨⌊u⌋₊ - 1, by omega⟩
  rw [hm, show a + (m + 1) - 1 = a + m by omega, show a + (m + 1) = (a + m) + 1 by ring,
    Finset.sum_Icc_succ_top (by omega)]

/-- The right end: the moving sum at `x` with window `u` only depends on `⌊x + u⌋`. PROVED. -/
theorem movingSum_right_const {b : ℕ} {x u : ℝ} (h1 : (b : ℝ) ≤ x + u) (h2 : x + u < b + 1) :
    movingSum χ x u = movingSum χ x (b - x) := by
  rw [movingSum_eq, movingSum_eq, show x + (b - x) = (b : ℝ) by ring, Nat.floor_natCast]
  have hb : ⌊x + u⌋₊ = b := by
    rw [Nat.floor_eq_iff (by linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)])]
    exact ⟨h1, h2⟩
  rw [hb]

/-- The right end, one term split off: for `0 ≤ x < b`,
`S(x, b - x) = c(⌈x⌉) + S(x + 1, b - (x + 1))`. PROVED. -/
theorem movingSum_right_split {b : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hxb : x < b) :
    movingSum χ x (b - x) = cf χ ⌈x⌉₊ + movingSum χ (x + 1) (b - (x + 1)) := by
  rw [movingSum_eq, movingSum_eq, show x + (b - x) = (b : ℝ) by ring,
    show x + 1 + (b - (x + 1)) = (b : ℝ) by ring, Nat.floor_natCast, Nat.ceil_add_one hx0]
  have hcb : ⌈x⌉₊ ≤ b := Nat.ceil_le.mpr hxb.le
  have e : insert ⌈x⌉₊ (Finset.Icc (⌈x⌉₊ + 1) b) = Finset.Icc ⌈x⌉₊ b := by
    ext n; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  rw [← e, Finset.sum_insert (by simp)]

/-! ### Gallagher's clipped window sum -/

open Classical in
theorem cwinSum_eq_filter (T : Finset ℕ) (c : ℕ → ℂ) (h x : ℝ) :
    Burst9G.cwinSum T c h x = ∑ n ∈ T.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h), c n := by
  unfold Burst9G.cwinSum Burst9G.win
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hx : x ∈ Ico ((n : ℝ) - h) n
  · rw [indicator_of_mem hx, if_pos ⟨hx.2, by linarith [hx.1]⟩]
  · rw [indicator_of_notMem hx, if_neg]
    rintro ⟨h1, h2⟩
    exact hx ⟨by linarith, h1⟩

/-- Left end: for `a - h ≤ x < a` and `a + h ≤ b` the clipped sum is the moving sum from `a`.
PROVED. -/
theorem clip_eq_left {a b : ℕ} {h x : ℝ} (hab : (a : ℝ) + h ≤ b) (hx1 : (a : ℝ) - h ≤ x)
    (hx2 : x < a) :
    Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x = movingSum χ a (x + h - a) := by
  rw [cwinSum_eq_filter, movingSum_eq, Nat.ceil_natCast,
    show (a : ℝ) + (x + h - a) = x + h by ring]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  have hxh : 0 ≤ x + h := by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.le_floor_iff hxh]
  constructor
  · rintro ⟨⟨h1, -⟩, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    have h1' : (a : ℝ) ≤ n := by exact_mod_cast h1
    refine ⟨⟨h1, ?_⟩, by linarith, h3⟩
    have : (n : ℝ) ≤ b := by linarith
    exact_mod_cast this

/-- Middle: for `a ≤ x ≤ b - h`, `x` not an integer, the clipped sum is the moving sum.
PROVED. -/
theorem clip_eq_mid {a b : ℕ} {h x : ℝ} (hh : 0 ≤ h) (hx1 : (a : ℝ) ≤ x) (hx2 : x + h ≤ b)
    (hxn : ∀ n : ℕ, x ≠ n) :
    Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x = movingSum χ x h := by
  rw [cwinSum_eq_filter, movingSum_eq]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg a) hx1
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.le_floor_iff (by linarith : 0 ≤ x + h),
    Nat.ceil_le]
  constructor
  · rintro ⟨-, h2, h3⟩; exact ⟨h2.le, h3⟩
  · rintro ⟨h2, h3⟩
    have h2' : x < n := lt_of_le_of_ne h2 (hxn n)
    refine ⟨⟨?_, ?_⟩, h2', h3⟩
    · have : (a : ℝ) < n := by linarith
      exact_mod_cast this.le
    · have : (n : ℝ) ≤ b := by linarith
      exact_mod_cast this

/-- Right end: for `b - h < x < b`, `a ≤ x`, `x` not an integer, the clipped sum is the moving
sum ending at `b`. PROVED. -/
theorem clip_eq_right {a b : ℕ} {h x : ℝ} (hx1 : (b : ℝ) - h < x) (hx2 : x < b)
    (hxa : (a : ℝ) ≤ x) (hxn : ∀ n : ℕ, x ≠ n) :
    Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x = movingSum χ x (b - x) := by
  rw [cwinSum_eq_filter, movingSum_eq, show x + (b - x) = (b : ℝ) by ring, Nat.floor_natCast]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le]
  constructor
  · rintro ⟨⟨-, h2⟩, h3, -⟩; exact ⟨h3.le, h2⟩
  · rintro ⟨h3, h2⟩
    have h3' : x < n := lt_of_le_of_ne h3 (hxn n)
    have h2' : (n : ℝ) ≤ b := by exact_mod_cast h2
    refine ⟨⟨?_, h2⟩, h3', by linarith⟩
    have : (a : ℝ) < n := by linarith
    exact_mod_cast this.le

/-- Outside `[a - h, b)` the clipped sum vanishes. PROVED. -/
theorem clip_eq_zero {a b : ℕ} {h x : ℝ} (hx : x < (a : ℝ) - h ∨ (b : ℝ) ≤ x) :
    Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x = 0 := by
  rw [cwinSum_eq_filter]
  refine Finset.sum_eq_zero fun n hn => ?_
  exfalso
  obtain ⟨hn1, hn2, hn3⟩ := of_mem_filter hn
  have h1 : (a : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn1).1
  have h2 : (n : ℝ) ≤ b := by exact_mod_cast (Finset.mem_Icc.mp hn1).2
  rcases hx with hx | hx <;> linarith

#print axioms movingSum_measurable
#print axioms norm_cf_le_log
#print axioms norm_movingSum_le
#print axioms movingSum_shift_left
#print axioms movingSum_top
#print axioms movingSum_right_const
#print axioms movingSum_right_split
#print axioms clip_eq_left
#print axioms clip_eq_mid
#print axioms clip_eq_right
#print axioms clip_eq_zero

end
end LeanLab.PerelliPintz1992.Burst9
