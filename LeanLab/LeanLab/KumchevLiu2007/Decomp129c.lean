/-
Kumchev and Liu, arXiv 0801.0130, paper P0088. Route burst session 9, 2026-11-12.
Bridge from the split leaf `eq49_lemma38` of `Decomp129`, Lemma 3.8 display 49 on
page 14 for j equal to 2, to `lemma38_two` of `Decomp129b`, which is assembled
there from `truncation_input` and `tail_mean_square_input`. Also a proof of the
statement of the split leaf `eq48_P2_lower`, the lower half of display 48 on
page 13, from the prime factor bounds of `Decomp129b` and the lab Mertens bound.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp129b
import LeanLab.PNTSieve.MertensUpper

namespace LeanLab.KumchevLiu2007.Task129c

open Real Complex LeanLab.KumchevLiu2007 Task129 Task129b

/-- The product of page 13 display 45 used in `Decomp129` is the one of
`Decomp129b`. -/
theorem eulerP2_eq_product2 (n : ℕ) (Q : ℝ) : eulerP2 n Q = product2 n Q := rfl

/-- Lemma 3.8, display 49 on page 14, in the form `eq49_lemma38` of
`Decomp129`, follows from `lemma38_two` of `Decomp129b`. The two statements
agree term for term. -/
theorem eq49_lemma38_of_lemma38_two (h : lemma38_two) (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ, x0 ≤ x → x ^ ε ≤ y → y ≤ x →
      0 < P → P ≤ Q → Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, ‖series2 n P - eulerP2 n Q‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) :=
  h A ε hA hε

/-- The same statement, CONDITIONAL ON the two leaves of `Decomp129b` through
`lemma38_from_leaves`. -/
theorem eq49_lemma38_from_129b (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ, x0 ≤ x → x ^ ε ≤ y → y ≤ x →
      0 < P → P ≤ Q → Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, ‖series2 n P - eulerP2 n Q‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) :=
  eq49_lemma38_of_lemma38_two lemma38_from_leaves A ε hA hε

/-! ### Display 48, lower half, for j equal to 2. Route burst session 9. -/

/-- Real analysis: log of 1 minus x is at least minus x minus 2 x squared for x
in 0, 1/2, from Mathlib's Taylor bound for the logarithm. -/
theorem log_one_sub_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    -x - 2 * x ^ 2 ≤ Real.log (1 - x) := by
  have hx : |x| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one, abs_of_nonneg h0] at h
  have hden : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg x]
  have := (abs_le.mp (h.trans hden)).1
  linarith

/-- The same in exponential form: 1 minus x is at least exp of minus x minus 2 x squared. -/
theorem exp_le_one_sub {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    Real.exp (-x - 2 * x ^ 2) ≤ 1 - x := by
  calc Real.exp (-x - 2 * x ^ 2) ≤ Real.exp (Real.log (1 - x)) :=
        Real.exp_le_exp.mpr (log_one_sub_ge h0 h1)
    _ = 1 - x := Real.exp_log (by linarith)

/-- Arithmetic for primes p at least 5 with x equal to 1/p plus 6/p squared,
the bound of page 14 display 47 at a prime in `A2_prime_norm_le_inv_add`. -/
theorem xp_facts {p : ℝ} (hp : 5 ≤ p) :
    0 ≤ 1 / p + 6 / p ^ 2 ∧ 1 / p + 6 / p ^ 2 ≤ 1 / 2 ∧
      (1 / p + 6 / p ^ 2) + 2 * (1 / p + 6 / p ^ 2) ^ 2 ≤ 1 / p + 16 * (p ^ 2)⁻¹ := by
  have hp0 : 0 < p := by linarith
  set u := 1 / p with hu_def
  have hu0 : 0 ≤ u := by positivity
  have hu : u ≤ 1 / 5 := by
    rw [hu_def]; exact one_div_le_one_div_of_le (by norm_num) hp
  have e1 : 6 / p ^ 2 = 6 * u ^ 2 := by rw [hu_def]; field_simp
  have e2 : (p ^ 2)⁻¹ = u ^ 2 := by rw [hu_def]; field_simp
  rw [e1, e2]
  have h5 : (1 + 6 * u) ^ 2 ≤ 5 := by nlinarith
  have hsq : (u + 6 * u ^ 2) ^ 2 = u ^ 2 * (1 + 6 * u) ^ 2 := by ring
  refine ⟨by positivity, by nlinarith, ?_⟩
  rw [hsq]
  nlinarith [mul_le_mul_of_nonneg_left h5 (sq_nonneg u)]

/-- Route burst session 9. The statement of the split leaf `eq48_P2_lower` of
`Decomp129`, page 13 display 48 lower half for j equal to 2, proved with
c equal to exp of minus 44 and P0 equal to 2. The local factors at 2 and 3 are
2 and 3/2 on H2; for p at least 5 the factor is at least 1 minus 1/p minus 6/p
squared by display 47; the product is bounded below through the logarithm and
the lab Mertens bound, sum of 1/p up to N at most log log N plus 12. -/
theorem eq48_P2_lower_proved :
    ∃ c P0 : ℝ, 0 < c ∧ 2 ≤ P0 ∧ ∀ P : ℝ, P0 ≤ P → ∀ n : ℕ, InH2 n →
      c / Real.log P ≤ ‖eulerP2 n P‖ := by
  refine ⟨Real.exp (-44), 2, Real.exp_pos _, le_rfl, ?_⟩
  intro P hP n hn
  set N := ⌊P⌋₊ with hN_def
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hP)
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNP : (N : ℝ) ≤ P := Nat.floor_le (by linarith)
  set S := (Finset.range (N + 1)).filter Nat.Prime with hS_def
  set x : ℕ → ℝ := fun p => if 5 ≤ p then 1 / (p : ℝ) + 6 / (p : ℝ) ^ 2 else 0 with hx_def
  have hx0 : ∀ p, 0 ≤ x p := by
    intro p; simp only [hx_def]; split_ifs with h
    · exact (xp_facts (by exact_mod_cast h)).1
    · exact le_rfl
  have hx1 : ∀ p, x p ≤ 1 / 2 := by
    intro p; simp only [hx_def]; split_ifs with h
    · exact (xp_facts (by exact_mod_cast h)).2.1
    · norm_num
  -- local factors
  have hloc : ∀ p ∈ S, 1 - x p ≤ ‖1 + U1534.A2 n p‖ := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    simp only [hx_def]
    split_ifs with h5
    · have : Fact p.Prime := ⟨hpp⟩
      have hb := Task129b.A2_prime_norm_le_inv_add p n
      have ht : ‖(1 : ℂ)‖ ≤ ‖1 + U1534.A2 n p‖ + ‖U1534.A2 n p‖ := by
        have := norm_sub_le (1 + U1534.A2 n p) (U1534.A2 n p)
        simpa only [add_sub_cancel_right] using this
      rw [norm_one] at ht
      linarith
    · have hp23 : p = 2 ∨ p = 3 := by
        have := hpp.two_le
        interval_cases p <;> simp_all <;> norm_num at hpp
      rcases hp23 with rfl | rfl
      · rw [U1534.A2_two_even (by have := hn.2; omega)]
        norm_num
      · rw [U1534.A2_three_ne_one hn.1]
        have : (1 : ℂ) + 1 / 2 = ((3 / 2 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
        norm_num
  have hnorm : ‖eulerP2 n P‖ = ∏ p ∈ S, ‖1 + U1534.A2 n p‖ := by
    simp only [eulerP2, hS_def, hN_def]
    exact Complex.norm_prod _ _
  have hprod1 : ∏ p ∈ S, (1 - x p) ≤ ‖eulerP2 n P‖ := by
    rw [hnorm]
    exact Finset.prod_le_prod₀ (fun p _ => by linarith [hx1 p]) hloc
  have hprod2 : Real.exp (-∑ p ∈ S, (x p + 2 * x p ^ 2)) ≤ ∏ p ∈ S, (1 - x p) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod₀ (fun p _ => (Real.exp_pos _).le)
    intro p _
    have := exp_le_one_sub (hx0 p) (hx1 p)
    rwa [show -(x p + 2 * x p ^ 2) = -x p - 2 * x p ^ 2 by ring]
  -- the sum
  have hper : ∀ p ∈ S, x p + 2 * x p ^ 2 ≤ 1 / (p : ℝ) + 16 * ((p : ℝ) ^ 2)⁻¹ := by
    intro p _
    simp only [hx_def]
    split_ifs with h5
    · exact (xp_facts (by exact_mod_cast h5)).2.2
    · norm_num; positivity
  have hsum1 : ∑ p ∈ S, (1 : ℝ) / p ≤ Real.log (Real.log N) + 12 := by
    refine le_trans ?_ (LeanLab.PNTSieve.Mertens.sum_inv_primes_le N hN2)
    apply le_of_eq
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [hS_def, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2.one_lt.le, by omega⟩, h2⟩
    · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨by omega, h2⟩
  have hsum2 : ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ ≤ 2 := by
    have hsub : S ⊆ Finset.Ioo 0 (N + 1) := by
      intro p hp
      simp only [hS_def, Finset.mem_filter, Finset.mem_range] at hp
      simp only [Finset.mem_Ioo]
      exact ⟨hp.2.pos, hp.1⟩
    calc ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ ≤ ∑ i ∈ Finset.Ioo 0 (N + 1), ((i : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 2 / ((0 : ℕ) + 1 : ℝ) := sum_Ioo_inv_sq_le 0 (N + 1)
      _ = 2 := by norm_num
  have hsum : ∑ p ∈ S, (x p + 2 * x p ^ 2) ≤ Real.log (Real.log N) + 44 := by
    calc ∑ p ∈ S, (x p + 2 * x p ^ 2)
        ≤ ∑ p ∈ S, (1 / (p : ℝ) + 16 * ((p : ℝ) ^ 2)⁻¹) := Finset.sum_le_sum hper
      _ = ∑ p ∈ S, (1 : ℝ) / p + 16 * ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ Real.log (Real.log N) + 44 := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hexp : Real.exp (-44) / Real.log N ≤ ‖eulerP2 n P‖ := by
    refine le_trans ?_ (hprod2.trans hprod1)
    have : Real.exp (-44) / Real.log N = Real.exp (-(Real.log (Real.log N) + 44)) := by
      rw [show -(Real.log (Real.log N) + 44) = -44 + -Real.log (Real.log N) by ring,
        Real.exp_add, Real.exp_neg (Real.log (Real.log N)), Real.exp_log hlogN, div_eq_mul_inv]
    rw [this]
    exact Real.exp_le_exp.mpr (by linarith)
  refine le_trans ?_ hexp
  apply div_le_div_of_nonneg_left (Real.exp_pos _).le hlogN
  exact Real.log_le_log (by linarith) hNP

end LeanLab.KumchevLiu2007.Task129c

#print axioms LeanLab.KumchevLiu2007.Task129c.eulerP2_eq_product2
#print axioms LeanLab.KumchevLiu2007.Task129c.eq49_lemma38_of_lemma38_two
#print axioms LeanLab.KumchevLiu2007.Task129c.eq49_lemma38_from_129b
#print axioms LeanLab.KumchevLiu2007.Task129c.eq48_P2_lower_proved
