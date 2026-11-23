import Mathlib
import LeanLab.HelfgottMajor.PVCases1122

/-!
Route burst S58, burst-20261122. The LEAF `PVCases1122.odd_small`: for q below 7 any interval
sum of a nontrivial Dirichlet character mod q has norm at most q/2, by periodicity of the
initial segment sums and the triangle inequality on the shorter of a window and its
complement, and q/2 is below the Pomerance odd bound for q = 3, 4, 5, 6. The case q = 2 has
no odd character. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVOddSmall1122

open Real Finset

theorem sum_range_zmod (q : ℕ) [NeZero q] (h : ZMod q → ℂ) :
    ∑ i ∈ range q, h (i : ZMod q) = ∑ x : ZMod q, h x := by
  refine Finset.sum_nbij (fun i => (i : ZMod q)) (by simp) ?_ ?_ (by simp)
  · intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  · intro x _
    exact ⟨x.val, by simp [ZMod.val_lt], by simp⟩

theorem init_periodic {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ∑ m ∈ range (n + q), χ (m : ZMod q) = ∑ m ∈ range n, χ (m : ZMod q) := by
  rw [Finset.sum_range_add]
  have : ∑ i ∈ range q, χ (((n + i : ℕ)) : ZMod q) = 0 := by
    have e := sum_range_zmod q (fun y => χ ((n : ZMod q) + y))
    simp only [Nat.cast_add]
    rw [e]
    exact (Equiv.sum_comp (Equiv.addLeft (n : ZMod q)) (fun x => χ x)).trans (MulChar.sum_eq_zero_of_ne_one hχ)
  rw [this, add_zero]

theorem init_mod {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ∑ m ∈ range n, χ (m : ZMod q) = ∑ m ∈ range (n % q), χ (m : ZMod q) := by
  have key : ∀ k r : ℕ, ∑ m ∈ range (r + q * k), χ (m : ZMod q) =
      ∑ m ∈ range r, χ (m : ZMod q) := by
    intro k r
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show r + q * (k + 1) = r + q * k + q by ring, init_periodic χ hχ, ih]
  conv_lhs => rw [← Nat.mod_add_div n q]
  exact key _ _

theorem window {q : ℕ} (χ : DirichletCharacter ℂ q) {a b : ℕ} (h : a ≤ b) :
    ‖∑ m ∈ range b, χ (m : ZMod q) - ∑ m ∈ range a, χ (m : ZMod q)‖ ≤ (b : ℝ) - a := by
  rw [← Finset.sum_Ico_eq_sub _ h]
  refine (norm_sum_le _ _).trans ?_
  have := Finset.sum_le_sum (fun i (_ : i ∈ Ico a b) => DirichletCharacter.norm_le_one χ (i : ZMod q))
  simp only [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one] at this
  rw [Nat.cast_sub h] at this
  exact this

theorem interval_le_half {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (M N : ℕ) : ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤ (q : ℝ) / 2 := by
  set f : ℕ → ℂ := fun n => ∑ m ∈ range n, χ (m : ZMod q) with hf
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have two : ∀ a b : ℕ, a < q → b < q → a ≤ b → 2 * ‖f b - f a‖ ≤ q := by
    intro a b ha hb hab
    have h1 : ‖f b - f a‖ ≤ (b : ℝ) - a := window χ hab
    have h2 : ‖f (a + q) - f b‖ ≤ ((a + q : ℕ) : ℝ) - b := window χ (by omega)
    have e : f (a + q) = f a := init_periodic χ hχ a
    rw [e, norm_sub_rev] at h2
    push_cast at h2
    linarith
  by_cases h : M ≤ N + 1
  swap
  · have h0 : Icc M N = ∅ := Finset.Icc_eq_empty (by omega)
    rw [h0, sum_empty, norm_zero]; positivity
  have hI : ∑ m ∈ Icc M N, χ (m : ZMod q) = f (N + 1) - f M := by
    have hI : Icc M N = Ico M (N + 1) := by ext x; simp
    rw [hf, ← Finset.sum_Ico_eq_sub _ h, hI]
  rw [hI, show f (N + 1) = f ((N + 1) % q) from init_mod χ hχ _,
    show f M = f (M % q) from init_mod χ hχ _]
  have ha := Nat.mod_lt (N + 1) hq
  have hb := Nat.mod_lt M hq
  rcases le_total ((N + 1) % q) (M % q) with h | h
  · have := two _ _ ha hb h
    rw [norm_sub_rev]; linarith
  · have := two _ _ hb ha h
    linarith

theorem rhs_ge (q : ℕ) (L0 : ℝ) (hL : L0 ≤ log q) (h1 : 1 ≤ L0)
    (hs : sqrt q ≤ 2 * (1 + L0 / 6.4)) :
    (q : ℝ) / 2 ≤ 1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  have s0 : 0 ≤ sqrt (q : ℝ) := sqrt_nonneg _
  have ss : sqrt (q : ℝ) * sqrt q = q := mul_self_sqrt (Nat.cast_nonneg q)
  have hll : 0 ≤ log (log q) := log_nonneg (by linarith)
  have t2 : 0 ≤ 1 / π * sqrt q * log (log q) := by positivity
  have hpi := pi_lt_d2
  have hpi0 := pi_pos
  have c1 : 1 / 6.4 ≤ 1 / (2 * π) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have t1 : sqrt q * L0 / 6.4 ≤ 1 / (2 * π) * sqrt q * log q := by
    have a : sqrt q * L0 * (1 / 6.4) ≤ sqrt q * L0 * (1 / (2 * π)) :=
      mul_le_mul_of_nonneg_left c1 (by positivity)
    have b : sqrt q * L0 ≤ sqrt q * log q := mul_le_mul_of_nonneg_left hL s0
    have b' : sqrt q * L0 * (1 / (2 * π)) ≤ sqrt q * log q * (1 / (2 * π)) :=
      mul_le_mul_of_nonneg_right b (by positivity)
    have : sqrt q * L0 / 6.4 = sqrt q * L0 * (1 / 6.4) := by ring
    have : 1 / (2 * π) * sqrt q * log q = sqrt q * log q * (1 / (2 * π)) := by ring
    linarith
  have : (q : ℝ) / 2 ≤ sqrt q * (1 + L0 / 6.4) := by
    have := mul_le_mul_of_nonneg_left hs s0
    nlinarith
  have : sqrt q * (1 + L0 / 6.4) = sqrt q + sqrt q * L0 / 6.4 := by ring
  linarith

theorem log_ge_one {q : ℕ} (h : 3 ≤ q) : 1 ≤ log (q : ℝ) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_d9
  have : (3 : ℝ) ≤ q := by exact_mod_cast h
  linarith

theorem odd_small {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (hq7 : q < 7) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  have hne : χ ≠ 1 := by
    rintro rfl
    exact hodd (MulChar.one_apply (isUnit_one.neg))
  refine (interval_le_half χ hne M N).trans ?_
  have hq0 : q ≠ 0 := NeZero.ne q
  by_cases h2 : q = 2
  · subst h2
    exact absurd (by rw [show (-1 : ZMod 2) = 1 by decide, map_one]) hodd
  have h3 : 3 ≤ q := by omega
  by_cases h6 : q = 6
  · subst h6
    refine rhs_ge 6 1.69 ?_ (by norm_num) ?_
    · rw [show ((6 : ℕ) : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      have := log_two_gt_d9
      have := log_ge_one (q := 3) le_rfl
      push_cast at this
      linarith
    · rw [Real.sqrt_le_iff]; constructor <;> norm_num
  · refine rhs_ge q 1 (log_ge_one h3) le_rfl ?_
    rw [Real.sqrt_le_iff]; constructor
    · norm_num
    · have : (q : ℝ) ≤ 5 := by exact_mod_cast (by omega : q ≤ 5)
      linarith

example : type_of% @odd_small = type_of% @LeanLab.HelfgottMajor.PVCases1122.odd_small := rfl

end LeanLab.HelfgottMajor.PVOddSmall1122

#print axioms LeanLab.HelfgottMajor.PVOddSmall1122.odd_small
