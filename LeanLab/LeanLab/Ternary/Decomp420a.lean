/-
Helfgott https://arxiv.org/abs/1312.7748v2, page 70, equation 7.50.
Finite weighted union bounds for the discarded terms.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp379b
import LeanLab.Ternary.Decomp420f
import LeanLab.Common.PsiTheta.Bound
import LeanLab.Helfgott2013.MellinSup
import LeanLab.Helfgott2013.Conclusion

namespace LeanLab.Ternary.Task420
open Finset MeasureTheory
open scoped ArithmeticFunction

/-- Cyclic relabeling preserves a finite triple sum.
Derived finite sum step for Helfgott page 70, equation 7.50. -/
theorem triple_sum_rotate {α : Type*} (s : Finset α) (f : α → α → α → ℝ) :
    (∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, f p q r) =
      ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, f r p q := by
  rw [sum_comm]
  apply sum_congr rfl
  intro q hq
  rw [sum_comm]

/-- Fixing two coordinates leaves at most one third coordinate.
Helfgott page 70, equation 7.50, before summing the two remaining masses. -/
theorem constrained_inner_sum_le (N p q : ℕ) (a : ℕ → ℝ) (L : ℝ)
    (haL : ∀ n ∈ range (N + 1), a n ≤ L) (hL : 0 ≤ L) :
    (∑ r ∈ range (N + 1), if p + q + r = N then a r else 0) ≤ L := by
  by_cases hpq : p + q ≤ N
  · have hr : N - (p + q) ∈ range (N + 1) := mem_range.mpr (by omega)
    have he (r : ℕ) : p + q + r = N ↔ r = N - (p + q) := by omega
    simpa only [he, sum_ite_eq', ite_eq_left hr] using haL _ hr
  · have he (r : ℕ) : p + q + r ≠ N := by omega
    simpa only [he, ite_false, sum_const_zero] using hL

/-- One specified bad coordinate costs its mass times the full mass and L.
Helfgott page 70, the second inequality of equation 7.50.
The good predicate is arbitrary and the coordinate weights are nonnegative. -/
theorem bad_first_sum_le (N : ℕ) (a : ℕ → ℝ) (G : ℕ → Prop) [DecidablePred G]
    (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (ha : ∀ n ∈ range (N + 1), 0 ≤ a n)
    (haL : ∀ n ∈ range (N + 1), a n ≤ L) :
    (∑ p ∈ range (N + 1), ∑ q ∈ range (N + 1), ∑ r ∈ range (N + 1),
      if p + q + r = N ∧ ¬ G p then C * a p * a q * a r else 0) ≤
      C * L * (∑ p ∈ range (N + 1), if ¬ G p then a p else 0) *
        (∑ q ∈ range (N + 1), a q) := by
  calc
    _ ≤ ∑ p ∈ range (N + 1), ∑ q ∈ range (N + 1),
        if ¬ G p then C * a p * a q * L else 0 := by
      apply sum_le_sum
      intro p hp
      apply sum_le_sum
      intro q hq
      by_cases hg : G p
      · simp only [hg, not_true_eq_false, and_false, ite_false, sum_const_zero]
        exact le_rfl
      · simp only [hg, not_false_eq_true, and_true, ite_true]
        have he (r : ℕ) : (if p + q + r = N then C * a p * a q * a r else 0) =
            C * a p * a q * (if p + q + r = N then a r else 0) := by
          split_ifs <;> ring
        simp_rw [he]
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (constrained_inner_sum_le N p q a L haL hL)
          (mul_nonneg (mul_nonneg hC (ha p hp)) (ha q hq))
    _ = ∑ p ∈ range (N + 1),
        (C * L * (if ¬ G p then a p else 0)) * (∑ q ∈ range (N + 1), a q) := by
      apply sum_congr rfl
      intro p hp
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      split_ifs <;> ring
    _ = _ := by rw [← sum_mul, ← mul_sum]

/-- Three choices for the bad coordinate give the factor three.
Helfgott page 70, equation 7.50. No sign condition on w is required. -/
theorem discarded_le_of_weight_bound (N : ℕ) (a : ℕ → ℝ) (C L : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (ha : ∀ n ∈ range (N + 1), 0 ≤ a n)
    (haL : ∀ n ∈ range (N + 1), a n ≤ L)
    (w : ℕ → ℕ → ℕ → ℝ)
    (hw : ∀ p ∈ range (N + 1), ∀ q ∈ range (N + 1), ∀ r ∈ range (N + 1),
      w p q r ≤ C * a p * a q * a r) :
    Task379.discardedTotal N w ≤
      3 * C * L * (∑ p ∈ range (N + 1), if ¬ (p.Prime ∧ Odd p) then a p else 0) *
        (∑ q ∈ range (N + 1), a q) := by
  classical
  let G : ℕ → Prop := fun p => p.Prime ∧ Odd p
  let s := range (N + 1)
  let A := fun p q r => C * a p * a q * a r
  let M := C * L * (∑ p ∈ s, if ¬ G p then a p else 0) * (∑ q ∈ s, a q)
  let S₁ := ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s,
    if p + q + r = N ∧ ¬ G p then A p q r else 0
  let S₂ := ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s,
    if p + q + r = N ∧ ¬ G q then A p q r else 0
  let S₃ := ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s,
    if p + q + r = N ∧ ¬ G r then A p q r else 0
  have h₁ : S₁ ≤ M := bad_first_sum_le N a G C L hC hL ha haL
  have h₂ : S₂ = S₁ := by
    dsimp [S₂, S₁]
    rw [triple_sum_rotate]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro r hr
    have he : r + p + q = p + q + r := by omega
    simp only [he]
    split_ifs <;> dsimp [A] <;> ring
  have h₃ : S₃ = S₁ := by
    dsimp [S₃, S₁]
    rw [triple_sum_rotate, triple_sum_rotate]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro r hr
    have he : q + r + p = p + q + r := by omega
    simp only [he]
    split_ifs <;> dsimp [A] <;> ring
  have hu : Task379.discardedTotal N w ≤ S₁ + S₂ + S₃ := by
    dsimp [Task379.discardedTotal, S₁, S₂, S₃]
    simp only [← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    apply sum_le_sum
    intro q hq
    apply sum_le_sum
    intro r hr
    have hA : 0 ≤ A p q r :=
      mul_nonneg (mul_nonneg (mul_nonneg hC (ha p hp)) (ha q hq)) (ha r hr)
    have hW := hw p hp q hq r hr
    change w p q r ≤ A p q r at hW
    have hg : (p.Prime ∧ Odd p ∧ q.Prime ∧ Odd q ∧ r.Prime ∧ Odd r) ↔
        G p ∧ G q ∧ G r := by dsimp [G]; tauto
    simp only [hg]
    by_cases hs : p + q + r = N
    · by_cases hpG : G p <;> by_cases hqG : G q <;> by_cases hrG : G r <;>
        simp only [hs, hpG, hqG, hrG, not_true_eq_false, not_false_eq_true,
          and_true, and_false, ite_true, ite_false] <;> linarith
    · simp only [hs, false_and, ite_false, add_zero, le_refl]
  rw [h₂, h₃] at hu
  calc
    _ ≤ S₁ + S₁ + S₁ := hu
    _ ≤ M + M + M := add_le_add (add_le_add h₁ h₁) h₁
    _ = _ := by dsimp [M, s, G]; ring

/-- The discarded one dimensional mass is psi minus theta plus log two.
Helfgott page 70 below equation 7.50. The endpoint two is counted once. -/
theorem bad_mangoldt_mass_identity (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ range (N + 1), if ¬ (n.Prime ∧ Odd n) then (Λ n : ℝ) else 0) =
      Chebyshev.psi N - Chebyshev.theta N + Real.log 2 := by
  classical
  have he (n : ℕ) :
      (if ¬ (n.Prime ∧ Odd n) then (Λ n : ℝ) else 0) =
        ((Λ n : ℝ) - if n.Prime then Real.log n else 0) +
          if n = 2 then Real.log 2 else 0 := by
    by_cases hn : n.Prime
    · by_cases htwo : n = 2
      · subst n
        norm_num [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      · simp [hn, hn.odd_of_ne_two htwo, htwo,
          ArithmeticFunction.vonMangoldt_apply_prime hn]
    · have htwo : n ≠ 2 := by intro h; subst n; exact hn Nat.prime_two
      simp [hn, htwo]
  simp_rw [he]
  rw [sum_add_distrib, sum_sub_distrib]
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
  simp only [Nat.floor_natCast, ← Nat.range_succ_eq_Icc_zero, sum_filter]
  have htwo : 2 ∈ range (N + 1) := mem_range.mpr (by omega)
  simp only [sum_ite_eq', ite_eq_left htwo]

/-- A coarse psi bound sufficient after the stronger prime power mass estimate.
Derived replacement for the RS62 step on Helfgott page 70.
The proved Chebyshev bound is used instead of the quoted coefficient 1.03883. -/
theorem psi_le_111 {x : ℝ} (hx : 10 ^ 8 ≤ x) : Chebyshev.psi x ≤ 1.11 * x := by
  have hx0 : 0 < x := by linarith
  have hp := LeanLab.Common.PsiTheta.psi_le_real (by linarith : 1 ≤ x)
  have hl := LeanLab.Common.PsiTheta.log_le_four_root hx0
  let u := x ^ ((4 : ℕ) : ℝ)⁻¹
  have hu0 : 0 ≤ u := Real.rpow_nonneg hx0.le _
  have hu4 : u ^ 4 = x := by
    dsimp [u]
    rw [← Real.rpow_mul_natCast hx0.le]
    norm_num
  have hu100 : 100 ≤ u := le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hu0
    (by rw [hu4]; norm_num at hx ⊢; exact hx)
  have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hlu : Real.log x ≤ 2 * u := by
    have h : 4 * u / Real.exp 1 ≤ 2 * u :=
      (div_le_iff₀ (Real.exp_pos 1)).mpr (by nlinarith)
    exact hl.trans h
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsq : Real.log x ^ 2 ≤ 4 * u ^ 2 := by nlinarith
  have hu2 : 10000 ≤ u ^ 2 := by nlinarith
  have hu4' : 10000 * u ^ 2 ≤ u ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu2)]
  have hbudget : 2 * Real.log x ^ 2 + 160 ≤ 0.0038 * x := by
    rw [← hu4]
    rw [← hu4] at hsq
    nlinarith
  linarith

/-- The bad coordinate mass is at most 1.251 times the square root.
Derived stronger replacement for Helfgott page 70 below equation 7.50.
The extra log two is absorbed once N is at least ten to power eight. -/
theorem bad_mangoldt_mass_le (N : ℕ) (hN : (10 : ℝ) ^ (8 : ℕ) ≤ N) :
    (∑ n ∈ range (N + 1), if ¬ (n.Prime ∧ Odd n) then (Λ n : ℝ) else 0) ≤
      1.251 * Real.sqrt N := by
  have hN2 : 2 ≤ N := by exact_mod_cast (by linarith : (2 : ℝ) ≤ N)
  rw [bad_mangoldt_mass_identity N hN2]
  have hp := LeanLab.Common.PsiTheta.psi_sub_theta_lt_125 hN
  have hs : (10000 : ℝ) ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num at hN ⊢
    exact hN
  have hl := Real.log_two_lt_d9
  linarith

/-- The full range sum is precisely psi, including the zero term.
Derived endpoint convention for Helfgott page 70, equation 7.50. -/
theorem mangoldt_range_sum (N : ℕ) :
    (∑ n ∈ range (N + 1), (Λ n : ℝ)) = Chebyshev.psi N := by
  rw [Chebyshev.psi_eq_sum_Icc]
  simp only [Nat.floor_natCast, ← Nat.range_succ_eq_Icc_zero]

/-- The full positive Mellin integral equals the proved compact support model.
Helfgott page 60, equation 7.19, using eta two from page 25, equation 4.7.
This bridge applies only at nonnegative arguments. -/
theorem etaStar_eq_mellin {w : ℝ} (hw : 0 ≤ w) :
    LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2 w =
      LeanLab.Helfgott2013.MellinL2.mellin w := by
  unfold LeanLab.HelfgottArcs.mconv LeanLab.Helfgott2013.MellinL2.mellin
  rw [intervalIntegral.integral_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Set.Icc (1 / 4 : ℝ) 1 ⊆ Set.Ioi 0 by
      intro t ht
      exact (by linarith [ht.1] : 0 < t))]
  · apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hz : 0 ≤ w / t := div_nonneg hw ht0.le
    have hg : LeanLab.HelfgottArcs.etaT2 (w / t) =
        LeanLab.Helfgott2013.GaussianL2.phi (w / t) := by
      unfold LeanLab.HelfgottArcs.etaT2 LeanLab.Helfgott2013.GaussianL2.phi
      split_ifs with h
      · rfl
      · have he : w / t = 0 := by linarith
        simp [he]
    dsimp only
    rw [hg]
    rfl
  · intro t ht
    have he : LeanLab.HelfgottArcs.eta2 t = 0 :=
      LeanLab.Helfgott2013.EtaTwo.etaTwo_eq_zero ht.2
    rw [he, zero_mul, zero_div]

/-- The actual eta star has the already proved sup bound.
Helfgott page 60, equation 7.19. No new analytic leaf is needed for this weight. -/
theorem etaStar_abs_le {w : ℝ} (hw : 0 ≤ w) :
    |LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2 w| ≤
      (1.414 : ℝ) := by
  rw [etaStar_eq_mellin hw]
  exact (LeanLab.Helfgott2013.MellinSup.mellin_sup w).2

/-- LEAF. The actual eta plus is uniformly bounded on the positive half line.
Helfgott page 56, equation 7.3. The written proof is in the cited major arcs
paper https://arxiv.org/abs/1305.2897v4, pages 76 and 77, equations B.34 to B.38.
This leaf concerns one smoothing function and contains no prime sum. -/
theorem etaPlus_abs_le (t : ℝ) : |LeanLab.HelfgottArcs.etaPlus t| ≤ (1.079955 : ℝ) := by
  exact etaPlus_abs_le_from_bandlimited_error t

/-- Every coordinate von Mangoldt value is at most log N.
Helfgott page 70, the second inequality of equation 7.50. -/
theorem mangoldt_le_log_of_le {n N : ℕ} (hN : 1 ≤ N) (hn : n ≤ N) :
    (Λ n : ℝ) ≤ Real.log N := by
  by_cases hn0 : n = 0
  · simp only [hn0, ArithmeticFunction.map_zero]
    exact Real.log_nonneg (by exact_mod_cast hN)
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0) (by exact_mod_cast hn))

/-- The actual triple weight is bounded by the product of three von Mangoldt values.
Helfgott page 70, equation 7.50, using the sup bounds from 7.3 and 7.19.
CONDITIONAL ON the stated eta plus sup hypothesis. -/
theorem helfgottTripleWeight_le
    (hplus : ∀ t : ℝ, |LeanLab.HelfgottArcs.etaPlus t| ≤ (1.079955 : ℝ))
    (N p q r : ℕ) :
    Task379.helfgottTripleWeight N p q r ≤
      (1.079955 ^ 2 * 1.414) * (Λ p : ℝ) * (Λ q : ℝ) * (Λ r : ℝ) := by
  let x := LeanLab.Helfgott2013.xOf N
  have hx : 0 ≤ x := by
    dsimp [x, LeanLab.Helfgott2013.xOf, LeanLab.Helfgott2013.ratio]
    positivity
  have hstar := etaStar_abs_le (show 0 ≤ 49 * (r / x) by positivity)
  have hprod :
      |LeanLab.HelfgottArcs.etaPlus (p / x) * LeanLab.HelfgottArcs.etaPlus (q / x) *
        LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
          (49 * (r / x))| ≤ (1.079955 ^ 2 * 1.414 : ℝ) := by
    rw [abs_mul, abs_mul, pow_two]
    exact mul_le_mul (mul_le_mul (hplus _) (hplus _) (abs_nonneg _) (by norm_num))
      hstar (abs_nonneg _) (by norm_num)
  have hA : 0 ≤ (Λ p : ℝ) * (Λ q : ℝ) * (Λ r : ℝ) := by positivity
  calc
    _ = ((Λ p : ℝ) * (Λ q : ℝ) * (Λ r : ℝ)) *
        (LeanLab.HelfgottArcs.etaPlus (p / x) * LeanLab.HelfgottArcs.etaPlus (q / x) *
          LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
            (49 * (r / x))) := by unfold Task379.helfgottTripleWeight; dsimp [x]; ring
    _ ≤ ((Λ p : ℝ) * (Λ q : ℝ) * (Λ r : ℝ)) *
        |LeanLab.HelfgottArcs.etaPlus (p / x) * LeanLab.HelfgottArcs.etaPlus (q / x) *
          LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
            (49 * (r / x))| := mul_le_mul_of_nonneg_left (le_abs_self _) hA
    _ ≤ ((Λ p : ℝ) * (Λ q : ℝ) * (Λ r : ℝ)) * (1.079955 ^ 2 * 1.414) :=
      mul_le_mul_of_nonneg_left hprod hA
    _ = _ := by ring

/-- The exact existing discarded contribution bound follows from the smaller smoothing leaf.
Helfgott page 70, equation 7.50 and the following displays.
The stronger proved prime power mass estimate replaces the quoted RS62 constants.
CONDITIONAL ON etaPlus_abs_le alone. -/
theorem helfgott_discarded_upper_decomposed (N : ℕ)
    (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    Task379.discardedTotal N (Task379.helfgottTripleWeight N) ≤
      7.3306 * (N : ℝ) ^ (3 / 2 : ℝ) * Real.log N := by
  have hN8 : (10 : ℝ) ^ (8 : ℕ) ≤ N := by norm_num at hN ⊢; linarith
  have hN1 : 1 ≤ N := by exact_mod_cast (by norm_num at hN8; linarith : (1 : ℝ) ≤ N)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hb := bad_mangoldt_mass_le N hN8
  have hp := psi_le_111 hN8
  have hsum := discarded_le_of_weight_bound N (fun n => (Λ n : ℝ))
    (1.079955 ^ 2 * 1.414) (Real.log N) (by norm_num) hlog
    (fun n hn => ArithmeticFunction.vonMangoldt_nonneg)
    (fun n hn => mangoldt_le_log_of_le hN1 (by have := mem_range.mp hn; omega))
    (Task379.helfgottTripleWeight N)
    (fun p hp q hq r hr => helfgottTripleWeight_le etaPlus_abs_le N p q r)
  rw [mangoldt_range_sum] at hsum
  have hs := mul_le_mul hb hp (Chebyshev.psi_nonneg _) (by positivity : 0 ≤ 1.251 * Real.sqrt N)
  have hbound := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 3 * (1.079955 ^ 2 * 1.414) * Real.log N by positivity)
  have hpow : Real.sqrt (N : ℝ) * N = (N : ℝ) ^ (3 / 2 : ℝ) := by
    calc
      _ = (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < N))]
        norm_num
  have hcoeff : (3 : ℝ) * (1.079955 ^ 2 * 1.414) * (1.251 * 1.11) ≤ 7.3306 := by norm_num
  calc
    _ ≤ 3 * (1.079955 ^ 2 * 1.414) * Real.log N *
        ((1.251 * Real.sqrt N) * (1.11 * N)) := by nlinarith only [hsum, hbound]
    _ = (3 * (1.079955 ^ 2 * 1.414) * (1.251 * 1.11)) *
        (N : ℝ) ^ (3 / 2 : ℝ) * Real.log N := by rw [← hpow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (by positivity) _)) hlog

end LeanLab.Ternary.Task420
