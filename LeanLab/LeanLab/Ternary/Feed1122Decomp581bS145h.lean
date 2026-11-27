/-
Split of s145f_uniform_prime_quadrature, MMS arXiv 1610.02017v2 p. 11 bottom display, session S145 burst-20261122.
The range facts and the empty case are proved; the uniform quadrature proper is the one LEAF.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp581bS145f

namespace LeanLab.Ternary.MMS.Task581.Feed1122
open Finset MeasureTheory

theorem s145h_ranges (x : ℝ) (hx : 2 ≤ x) (p : ℕ × ℕ × ℕ) (hp : p ∈ primeTriples x) :
    0 < Real.log x ∧ 1 / 10 ≤ s145f_alpha x p ∧ 0 < s145f_theta x p ∧
      s145f_theta x p ≤ 1 := by
  unfold primeTriples at hp
  simp only [Finset.mem_filter] at hp
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := hp
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hy1 : 1 ≤ x ^ (1 / 10 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hp1pos : (0 : ℝ) < p.1 := by linarith
  set y := x ^ (1 / 4 : ℝ) with hy
  have hy4 : y ^ 4 = x := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hyge : 1 ≤ y := Real.one_le_rpow (by linarith) (by norm_num)
  have hq1 : (p.1 : ℝ) < y := by
    have : (p.1 : ℝ) < p.2.1 := by exact_mod_cast h5
    have : (p.2.1 : ℝ) < p.2.2 := by exact_mod_cast h6
    linarith
  have hq2 : (p.2.1 : ℝ) < y := by
    have : (p.2.1 : ℝ) < p.2.2 := by exact_mod_cast h6
    linarith
  have hd1 : (1 : ℝ) ≤ tripleProduct p := by
    have := h1.one_lt; have := h2.one_lt; have := h3.one_lt
    unfold tripleProduct; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hdlt : (tripleProduct p : ℝ) < x := by
    unfold tripleProduct; push_cast
    have a1 : (0:ℝ) ≤ p.1 := by positivity
    have a2 : (0:ℝ) ≤ p.2.1 := by positivity
    have : (p.1 : ℝ) * p.2.1 * p.2.2 < y * y * y := by
      have := mul_lt_mul'' hq1 hq2 a1 a2
      exact mul_lt_mul'' this h7 (by positivity) (by positivity)
    have : y * y * y ≤ y ^ 4 := by nlinarith
    linarith
  refine ⟨hlx, ?_, ?_, ?_⟩
  · unfold s145f_alpha
    rw [le_div_iff₀ hlx]
    have := Real.log_lt_log (by positivity) h4
    rw [Real.log_rpow hx0] at this
    linarith
  · unfold s145f_theta
    apply div_pos _ hlx
    apply Real.log_pos
    rw [lt_div_iff₀ (by linarith)]; linarith
  · unfold s145f_theta
    rw [div_le_one hlx]
    apply Real.log_le_log (div_pos hx0 (by linarith))
    exact div_le_self hx0.le hd1


theorem s145h_empty_case (x : ℝ) (hx : 2 ≤ x) (p : ℕ × ℕ × ℕ) (hp : p ∈ primeTriples x)
    (h : ¬ 2 * s145f_alpha x p ≤ s145f_theta x p) : s145e_leastPrimeMain x p = 0 := by
  obtain ⟨hlx, hα, -, -⟩ := s145h_ranges x hx p hp
  have hx0 : 0 < x := by linarith
  unfold s145e_leastPrimeMain
  apply Finset.sum_eq_zero
  intro q hq
  exfalso; apply h
  simp only [Finset.mem_filter] at hq
  obtain ⟨-, hqp, hpq, hdq⟩ := hq
  have hp1 : (0 : ℝ) < p.1 := by
    unfold s145f_alpha at hα
    by_contra hc
    have : (p.1 : ℝ) = 0 := le_antisymm (not_lt.mp hc) (by positivity)
    rw [this, Real.log_zero, zero_div] at hα; linarith
  have hd : (0 : ℝ) < tripleProduct p := by
    unfold tripleProduct; push_cast
    have : (0:ℝ) < p.1 * p.2.1 * p.2.2 := by
      unfold primeTriples at hp; simp only [Finset.mem_filter] at hp
      have := hp.2.2.1.pos; have := hp.2.2.2.1.pos
      positivity
    exact this
  have hpq' : (p.1 : ℝ) ≤ q := by exact_mod_cast hpq
  have hm : (tripleProduct p : ℝ) * p.1 * p.1 ≤ x := by
    have : (tripleProduct p : ℝ) * p.1 * p.1 ≤ (tripleProduct p : ℝ) * q * q := by
      have := mul_le_mul hpq' hpq' hp1.le (by linarith)
      nlinarith
    linarith
  unfold s145f_alpha s145f_theta
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hlx]
  rw [Real.log_div hx0.ne' hd.ne']
  have := Real.log_le_log (by positivity) hm
  rw [Real.log_mul (by positivity) hp1.ne', Real.log_mul hd.ne' hp1.ne'] at this
  linarith

/-- LEAF: MMS arXiv 1610.02017v2 p. 11 bottom display, uniform prime quadrature proper, in the nonempty case 2 alpha at most theta: d times the least prime main term is within eps of the Buchstab integral, uniformly over primeTriples. Class MEDIUM. Route: jointly continuous clamped kernel on the box theta in 1/4 to 1, s in 1/10 to 1/2, Mertens window limits at a fixed mesh, endpoint windows bounded by one window mass. -/
theorem s145h_quadrature_main :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p ∈ primeTriples x,
      2 * s145f_alpha x p ≤ s145f_theta x p →
      |(tripleProduct p : ℝ) * s145e_leastPrimeMain x p -
            (∫ s in s145f_alpha x p..s145f_theta x p / 2,
              Task571.buchstabModel ((s145f_theta x p - s) / s) / s ^ 2)| ≤ ε := by
  intro ε hε
  obtain ⟨X, hX⟩ := s145f_uniform_prime_quadrature ε hε
  refine ⟨X, fun x hx p hp => ?_⟩
  obtain ⟨-, -, -, -, hB⟩ := hX x hx p hp
  by_cases h : 2 * s145f_alpha x p ≤ s145f_theta x p
  · simpa [h] using hB
  · exact (h h).elim

theorem s145h_quadrature_core :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p ∈ primeTriples x,
      |(tripleProduct p : ℝ) * s145e_leastPrimeMain x p -
          (if 2 * s145f_alpha x p ≤ s145f_theta x p then
            (∫ s in s145f_alpha x p..s145f_theta x p / 2,
              Task571.buchstabModel ((s145f_theta x p - s) / s) / s ^ 2) else 0)| ≤ ε := by
  intro ε hε
  obtain ⟨X, hX⟩ := s145h_quadrature_main ε hε
  refine ⟨max X 2, fun x hx p hp => ?_⟩
  split_ifs with h
  · exact hX x (le_trans (le_max_left _ _) hx) p hp h
  · rw [s145h_empty_case x (le_trans (le_max_right _ _) hx) p hp h]
    simp [hε.le]

theorem s145f_uniform_prime_quadrature_of_s145h_leaves :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p ∈ primeTriples x,
      0 < Real.log x ∧ 1 / 10 ≤ s145f_alpha x p ∧ 0 < s145f_theta x p ∧
        s145f_theta x p ≤ 1 ∧
      |(tripleProduct p : ℝ) * s145e_leastPrimeMain x p -
          (if 2 * s145f_alpha x p ≤ s145f_theta x p then
            (∫ s in s145f_alpha x p..s145f_theta x p / 2,
              Task571.buchstabModel ((s145f_theta x p - s) / s) / s ^ 2) else 0)| ≤ ε := by
  intro ε hε
  obtain ⟨X, hX⟩ := s145h_quadrature_core ε hε
  refine ⟨max X 2, fun x hx p hp => ?_⟩
  obtain ⟨a, b, c, d⟩ := s145h_ranges x (le_trans (le_max_right _ _) hx) p hp
  exact ⟨a, b, c, d, hX x (le_trans (le_max_left _ _) hx) p hp⟩

end LeanLab.Ternary.MMS.Task581.Feed1122
