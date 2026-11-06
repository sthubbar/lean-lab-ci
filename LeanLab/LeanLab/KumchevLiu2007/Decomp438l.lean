/-
Full period supply for the three-square diagonal mean square.
Source page 15 first display and Schwarz page 83 display 2.11.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp438k

namespace LeanLab.KumchevLiu2007.Task438l

open Real Complex Task129b Task129c Task292a
open scoped BigOperators

/-- LEAF. Page 15 first display, using the character definition on page 13
and Schwarz page 83 display 2.11. This is only a complete period average
at one modulus. There is no interval, P, Q, x or y variable.
The even prime powers through 8 are included. -/
theorem complete_period_square :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, 0 < q →
      (∑ n ∈ Finset.range q, ‖A3 n q‖ ^ 2) ≤
        K * (localMajorant q ^ 6 / (q : ℝ)) := by
  sorry

/-- Page 15 first display. A nonnegative periodic function summed over
an interval of length at least its period is bounded by six times the
length divided by the period times its complete period sum. -/
theorem nonnegative_periodic_interval (v : ℕ → ℝ) (q : ℕ) (hq : 0 < q)
    (hp : Function.Periodic v q) (hv : ∀ n, 0 ≤ v n)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 1 ≤ y) (hqy : (q : ℝ) ≤ y) :
    (∑ n ∈ intervalNumbers x y, v n) ≤
      6 * y / (q : ℝ) * (∑ n ∈ Finset.range q, v n) := by
  classical
  let S := ∑ n ∈ Finset.range q, v n
  let μ := S / (q : ℝ)
  let g : ℕ → ℂ := fun n => ((v n - μ : ℝ) : ℂ)
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hS : 0 ≤ S := Finset.sum_nonneg (fun n hn => hv n)
  have hμ : 0 ≤ μ := div_nonneg hS (by positivity)
  have hqμ : (q : ℝ) * μ = S := by dsimp [μ]; field_simp
  have hgper : Function.Periodic g q := by intro n; simp [g, hp n]
  have hgzero : (∑ n ∈ Finset.range q, g n) = 0 := by
    have he : (∑ n ∈ Finset.range q, g n) = ((S - (q : ℝ) * μ : ℝ) : ℂ) := by
      simp [g, S, Finset.sum_sub_distrib]
    rw [he, hqμ, sub_self, Complex.ofReal_zero]
  have hgperiod : (∑ n ∈ Finset.range q, ‖g n‖) ≤ 2 * S := by
    calc
      _ ≤ ∑ n ∈ Finset.range q, (v n + μ) := by
        apply Finset.sum_le_sum
        intro n hn
        calc
          _ = |v n - μ| := by
            change ‖((v n - μ : ℝ) : ℂ)‖ = _
            rw [Complex.norm_real, Real.norm_eq_abs]
          _ ≤ |v n| + |μ| := abs_sub _ _
          _ = _ := by rw [abs_of_nonneg (hv n), abs_of_nonneg hμ]
      _ = 2 * S := by simp [Finset.sum_add_distrib, ← hqμ, S]; ring
  have hi : ‖∑ n ∈ intervalNumbers x y, g n‖ ≤ 4 * S := by
    have h := periodic_zero_mean_interval g hq hgper hgzero
      (Order.succ ⌊x⌋₊) (Order.succ ⌊x + y⌋₊)
    have h' : ‖∑ n ∈ intervalNumbers x y, g n‖ ≤ 2 * ∑ n ∈ Finset.range q, ‖g n‖ := by
      simpa only [intervalNumbers, ← Finset.Ico_succ_succ_eq_Ioc] using h
    exact h'.trans (by linarith)
  have hgsum : (∑ n ∈ intervalNumbers x y, g n) =
      (((∑ n ∈ intervalNumbers x y, v n) - ((intervalNumbers x y).card : ℝ) * μ : ℝ) : ℂ) := by
    simp [g, Finset.sum_sub_distrib]
  rw [hgsum, Complex.norm_real, Real.norm_eq_abs] at hi
  have hcard := Task271a.interval_card_le hx hy
  have hmain : ((intervalNumbers x y).card : ℝ) * μ ≤ 2 * y * μ :=
    mul_le_mul_of_nonneg_right hcard hμ
  have hSmain : S ≤ y * μ := by nlinarith
  have herr := le_abs_self ((∑ n ∈ intervalNumbers x y, v n) - ((intervalNumbers x y).card : ℝ) * μ)
  have hbound : (∑ n ∈ intervalNumbers x y, v n) ≤ 6 * y * μ := by nlinarith
  have heq : 6 * y * μ = 6 * y / (q : ℝ) * S := by dsimp [μ]; ring
  exact hbound.trans_eq heq

/-- Page 15 first display. Exact Task438b single modulus interval supply.
CONDITIONAL only on complete_period_square. -/
theorem coefficient_interval_square :
    ∃ K : ℝ, 0 < K ∧ ∀ x y : ℝ, ∀ q : ℕ,
      0 ≤ x → 1 ≤ y → 0 < q → (q : ℝ) ^ 3 ≤ y →
      (∑ n ∈ intervalNumbers x y, ‖A3 n q‖ ^ 2) ≤
        K * y * (localMajorant q ^ 6 / (q : ℝ) ^ 2) := by
  obtain ⟨K, hK, hb⟩ := complete_period_square
  refine ⟨6 * K, by positivity, ?_⟩
  intro x y q hx hy hq hqy
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqle : (q : ℝ) ≤ y := by
    have hpos : 0 ≤ (q : ℝ) * ((q : ℝ) - 1) * ((q : ℝ) + 1) := by positivity
    nlinarith
  have hper : Function.Periodic (fun n => ‖A3 n q‖ ^ 2) q := by
    intro n
    change ‖A3 (n + q) q‖ ^ 2 = ‖A3 n q‖ ^ 2
    have he : A3 (n + q) q = A3 n q := Task403a.A3_periodic q n
    rw [he]
  calc
    _ ≤ 6 * y / (q : ℝ) * (∑ n ∈ Finset.range q, ‖A3 n q‖ ^ 2) :=
      nonnegative_periodic_interval _ q hq hper (fun n => sq_nonneg _) x y hx hy hqle
    _ ≤ 6 * y / (q : ℝ) * (K * (localMajorant q ^ 6 / (q : ℝ))) :=
      mul_le_mul_of_nonneg_left (hb q hq) (by positivity)
    _ = (6 * K) * y * (localMajorant q ^ 6 / (q : ℝ) ^ 2) := by ring

#print axioms complete_period_square
#print axioms nonnegative_periodic_interval
#print axioms coefficient_interval_square

end LeanLab.KumchevLiu2007.Task438l
